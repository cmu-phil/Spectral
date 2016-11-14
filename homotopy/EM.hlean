/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
-/

import homotopy.EM .spectrum

open eq is_equiv equiv is_conn is_trunc unit function pointed nat group algebra trunc trunc_index
     fiber prod pointed susp EM.ops

namespace EM

  /- Functorial action of Eilenberg-Maclane spaces -/

  definition pEM1_functor [constructor] {G H : Group} (φ : G →g H) : pEM1 G →* pEM1 H :=
  begin
    fconstructor,
    { intro g, induction g,
      { exact base },
      { exact pth (φ g) },
      { exact ap pth (respect_mul φ g h) ⬝ resp_mul (φ g) (φ h) }},
    { reflexivity }
  end

  definition EMadd1_functor [constructor] {G H : CommGroup} (φ : G →g H) (n : ℕ) :
    EMadd1 G n →* EMadd1 H n :=
  begin
    apply ptrunc_functor,
    apply iterate_psusp_functor,
    apply pEM1_functor,
    exact φ
  end

  definition EM_functor [unfold 4] {G H : CommGroup} (φ : G →g H) (n : ℕ) :
    K G n →* K H n :=
  begin
    cases n with n,
    { exact pmap_of_homomorphism φ },
    { exact EMadd1_functor φ n }
  end

  -- TODO: (K G n →* K H n) ≃ (G →g H)

  /- Equivalence of Groups and pointed connected 1-truncated types -/

  definition pEM1_pequiv_ptruncconntype (X : 1-Type*[0]) : pEM1 (π₁ X) ≃* X :=
  pEM1_pequiv_type

  definition Group_equiv_ptruncconntype [constructor] : Group ≃ 1-Type*[0] :=
  equiv.MK (λG, ptruncconntype.mk (pEM1 G) _ pt !is_conn_pEM1)
           (λX, π₁ X)
           begin intro X, apply ptruncconntype_eq, esimp, exact pEM1_pequiv_type end
           begin intro G, apply eq_of_isomorphism, apply fundamental_group_pEM1 end

  /- Higher EM-spaces -/

  /- K(G, 2) is unique (see below for general case) -/
  definition loopn_EMadd1 (G : CommGroup) (n : ℕ) : Ω[succ n] (EMadd1 G n) ≃* pType_of_Group G :=
  begin
    refine _ ⬝e* loop_pEM1 G,
    cases n with n,
    { refine !loop_ptrunc_pequiv ⬝e* _, refine ptrunc_pequiv _ _ _,
      apply is_trunc_eq, apply is_trunc_EM1},
    induction n with n IH,
    { exact loop_pequiv_loop (loop_EM2 G)},
    refine _ ⬝e* IH,
    refine !homotopy_group_pequiv_loop_ptrunc⁻¹ᵉ* ⬝e* _ ⬝e* !homotopy_group_pequiv_loop_ptrunc,
    apply iterate_psusp_stability_pequiv,
    rexact add_mul_le_mul_add n 1 1
  end

  definition EM2_map [unfold 7] {G : CommGroup} {X : Type*} (e : Ω[2] X ≃ G)
    (r : Π(p q : Ω[2] X), e (@concat (Ω X) idp idp idp p q) = e p * e q)
    [is_conn 1 X] [is_trunc 2 X] : EMadd1 G 1 → X :=
  begin
    change trunc 2 (susp (EM1 G)) → X, intro x,
    induction x with x, induction x with x,
    { exact pt},
    { exact pt},
    { change carrier (Ω X), refine EM1_map e r x}
  end

  definition pEM2_pmap [constructor] {G : CommGroup} {X : Type*} (e : Ω[2] X ≃ G)
    (r : Π(p q : Ω[2] X), e (@concat (Ω X) idp idp idp p q) = e p * e q)
    [is_conn 1 X] [is_trunc 2 X] : EMadd1 G 1 →* X :=
  pmap.mk (EM2_map e r) idp

  definition loop_pEM2_pmap {G : CommGroup} {X : Type*} (e : Ω[2] X ≃ G)
    (r : Π(p q : Ω[2] X), e (@concat (Ω X) idp idp idp p q) = e p * e q)
    [is_conn 1 X] [is_trunc 2 X] :
    Ω→[2](pEM2_pmap e r) ~ e⁻¹ᵉ ∘ loopn_EMadd1 G 1 :=
  begin
    exact sorry
  end

  -- TODO: make arguments in trivial_homotopy_group_of_is_trunc implicit
  attribute is_conn_EMadd1 is_trunc_EMadd1 [instance]
  definition pEM2_pequiv' {G : CommGroup} {X : Type*} (e : Ω[2] X ≃ G)
    (r : Π(p q : Ω[2] X), e (@concat (Ω X) idp idp idp p q) = e p * e q)
    [is_conn 1 X] [is_trunc 2 X] : EMadd1 G 1 ≃* X :=
  begin
    apply pequiv_of_pmap (pEM2_pmap e r),
    have is_conn 0 (EMadd1 G 1), from !is_conn_of_is_conn_succ,
    have is_trunc 2 (EMadd1 G 1), from !is_trunc_EMadd1,
    refine whitehead_principle_pointed 2 _ _,
    intro k, apply @nat.lt_by_cases k 2: intro H,
    { apply @is_equiv_of_is_contr,
      do 2 exact trivial_homotopy_group_of_is_conn _ (le_of_lt_succ H)},
    { cases H, esimp, apply is_equiv_trunc_functor, esimp,
      apply is_equiv.homotopy_closed, rotate 1,
      { symmetry, exact loop_pEM2_pmap _ _},
      apply is_equiv_compose, apply pequiv.to_is_equiv, apply to_is_equiv},
    { apply @is_equiv_of_is_contr,
      exact trivial_homotopy_group_of_is_trunc _ H,
      apply @trivial_homotopy_group_of_is_trunc, rotate 1, exact H, exact _inst_2}
  end

  definition pEM2_pequiv {G : CommGroup} {X : Type*} (e : πg[1+1] X ≃g G)
    [is_conn 1 X] [is_trunc 2 X] : EMadd1 G 1 ≃* X :=
  begin
    have is_set (Ω[2] X), from !is_trunc_eq,
    apply pEM2_pequiv' (!trunc_equiv⁻¹ᵉ ⬝e equiv_of_isomorphism e),
    intro p q, esimp, exact to_respect_mul e (tr p) (tr q)
  end

 -- general case
  definition EMadd1_map [unfold 8] {G : CommGroup} {X : Type*} {n : ℕ} (e : Ω[succ n] X ≃ G)
    (r : Π(p q : Ω (Ω[n] X)), e (p ⬝ q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n → X :=
  begin
    revert X e r H1 H2, induction n with n f: intro X e r H1 H2,
    { change trunc 1 (EM1 G) → X, intro x, induction x with x, exact EM1_map e r x},
    change trunc (n.+2) (susp (iterate_psusp n (pEM1 G))) → X, intro x,
    induction x with x, induction x with x,
    { exact pt},
    { exact pt},
    change carrier (Ω X), refine f _ _ _ _ _ (tr x),
    { refine _⁻¹ᵉ ⬝e e, apply equiv_of_pequiv, apply loopn_succ_in},
    exact abstract begin
      intro p q, refine _ ⬝ !r, apply ap e, esimp,
      apply inv_eq_of_eq,
      refine _⁻¹ ⬝ !loopn_succ_in_con⁻¹,
      exact to_right_inv (loopn_succ_in X (succ n)) p ◾ to_right_inv (loopn_succ_in X (succ n)) q
    end end
  end

  definition pEMadd1_pmap [constructor] {G : CommGroup} {X : Type*} {n : ℕ} (e : Ω[succ n] X ≃ G)
    (r : Π(p q : Ω[succ n] X), e (@concat (Ω[n] X) pt pt pt p q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n →* X :=
  pmap.mk (EMadd1_map e r) begin cases n with n: reflexivity end

  definition loop_pEMadd1_pmap {G : CommGroup} {X : Type*} {n : ℕ} (e : Ω[succ n] X ≃ G)
    (r : Π(p q : Ω[succ n] X), e (@concat (Ω[n] X) pt pt pt p q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] :
    Ω→[succ n](pEMadd1_pmap e r) ~ e⁻¹ᵉ ∘ loopn_EMadd1 G n :=
  begin
    apply homotopy_of_inv_homotopy_pre (loopn_EMadd1 G n),
    intro g, esimp at *,
    revert X e r H1 H2, induction n with n IH: intro X e r H1 H2,
    { refine !idp_con ⬝ _, refine !ap_compose'⁻¹ ⬝ _, apply elim_pth},
    { replace (succ (succ n)) with ((succ n) + 1), rewrite [apn_succ],
      exact sorry}
    -- exact !idp_con ⬝ !elim_pth
  end

  -- definition is_conn_of_le (n : ℕ₋₂) (A : Type) [is_conn (n.+1) A] :
  --   is_conn n A :=
  -- is_trunc_trunc_of_le A -2 (trunc_index.self_le_succ n)
  -- attribute is_conn_EMadd1 is_trunc_EMadd1 [instance]

  definition pEMadd1_pequiv' {G : CommGroup} {X : Type*} {n : ℕ} (e : Ω[succ n] X ≃ G)
    (r : Π(p q : Ω[succ n] X), e (@concat (Ω[n] X) pt pt pt p q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n ≃* X :=
  begin
    apply pequiv_of_pmap (pEMadd1_pmap e r),
    have is_conn 0 (EMadd1 G n), from is_conn_of_le _ (zero_le_of_nat n),
    have is_trunc (n.+1) (EMadd1 G n), from !is_trunc_EMadd1,
    refine whitehead_principle_pointed (n.+1) _ _,
    intro k, apply @nat.lt_by_cases k (succ n): intro H,
    { apply @is_equiv_of_is_contr,
      do 2 exact trivial_homotopy_group_of_is_conn _ (le_of_lt_succ H)},
    { cases H, esimp, apply is_equiv_trunc_functor, esimp,
      apply is_equiv.homotopy_closed, rotate 1,
      { symmetry, exact loop_pEMadd1_pmap _ _},
      apply is_equiv_compose, apply pequiv.to_is_equiv},
    { apply @is_equiv_of_is_contr,
      do 2 exact trivial_homotopy_group_of_is_trunc _ H}
  end

  definition pEMadd1_pequiv {G : CommGroup} {X : Type*} {n : ℕ} (e : πg[n+1] X ≃g G)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n ≃* X :=
  begin
    have is_set (Ω[succ n] X), from !is_set_loopn,
    apply pEMadd1_pequiv' (!trunc_equiv⁻¹ᵉ ⬝e equiv_of_isomorphism e),
    intro p q, esimp, exact to_respect_mul e (tr p) (tr q)
  end

  definition EM_pequiv_succ {G : CommGroup} {X : Type*} {n : ℕ} (e : πg[n+1] X ≃g G)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EM G (succ n) ≃* X :=
  pEMadd1_pequiv e

  definition EM_pequiv_zero {G : CommGroup} {X : Type*} (e : X ≃* pType_of_Group G) : EM G 0 ≃* X :=
  proof e⁻¹ᵉ* qed

  definition EM_spectrum /-[constructor]-/ (G : CommGroup) : spectrum :=
  spectrum.Mk (K G) (λn, (loop_EM G n)⁻¹ᵉ*)

  /- uniqueness of K(G,n), method 2: -/

-- definition freudenthal_homotopy_group_pequiv (A : Type*) {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
--   : π*[k + 1] (psusp A) ≃* π*[k] A  :=
-- calc
--   π*[k + 1] (psusp A) ≃* π*[k] (Ω (psusp A)) : pequiv_of_eq (homotopy_group_succ_in (psusp A) k)
--     ... ≃* Ω[k] (ptrunc k (Ω (psusp A)))     : homotopy_group_pequiv_loop_ptrunc k (Ω (psusp A))
--     ... ≃* Ω[k] (ptrunc k A)                 : loopn_pequiv_loopn k (freudenthal_pequiv A H)
--     ... ≃* π*[k] A                           : (homotopy_group_pequiv_loop_ptrunc k A)⁻¹ᵉ*

  definition iterate_psusp_succ_pequiv (n : ℕ) (A : Type*) :
    iterate_psusp (succ n) A ≃* iterate_psusp n (psusp A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact psusp_equiv IH}
  end

  definition is_conn_psusp [instance] (n : trunc_index) (A : Type*)
    [H : is_conn n A] : is_conn (n .+1) (psusp A) :=
  is_conn_susp n A

  definition iterated_freudenthal_pequiv (A : Type*) {n k m : ℕ} [HA : is_conn n A] (H : k ≤ 2 * n)
    : ptrunc k A ≃* ptrunc k (Ω[m] (iterate_psusp m A)) :=
  begin
    revert A n k HA H, induction m with m IH: intro A n k HA H,
    { reflexivity},
    { have H2 : succ k ≤ 2 * succ n,
      from calc
        succ k ≤ succ (2 * n) : succ_le_succ H
           ... ≤ 2 * succ n   : self_le_succ,
      exact calc
        ptrunc k A ≃* ptrunc k (Ω (psusp A))   : freudenthal_pequiv A H
          ... ≃* Ω (ptrunc (succ k) (psusp A)) : loop_ptrunc_pequiv
          ... ≃* Ω (ptrunc (succ k) (Ω[m] (iterate_psusp m (psusp A)))) :
                   loop_pequiv_loop (IH (psusp A) (succ n) (succ k) _ H2)
          ... ≃* ptrunc k (Ω[succ m] (iterate_psusp m (psusp A))) : loop_ptrunc_pequiv
          ... ≃* ptrunc k (Ω[succ m] (iterate_psusp (succ m) A)) :
                   ptrunc_pequiv_ptrunc _ (loopn_pequiv_loopn _ !iterate_psusp_succ_pequiv)}
  end

  definition pmap_eq_of_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) : f = g :=
  pmap_eq (to_homotopy p) (to_homotopy_pt p)⁻¹

  definition pmap_equiv_pmap_right {A B : Type*} (C : Type*) (f : A ≃* B) : C →* A ≃ C →* B :=
  begin
    fapply equiv.MK,
    { exact pcompose f},
    { exact pcompose f⁻¹ᵉ*},
    { intro f, apply pmap_eq_of_phomotopy,
      exact !passoc⁻¹* ⬝* pwhisker_right _ !pright_inv ⬝* !pid_pcompose},
    { intro f, apply pmap_eq_of_phomotopy,
      exact !passoc⁻¹* ⬝* pwhisker_right _ !pleft_inv ⬝* !pid_pcompose}
  end

  definition iterate_psusp_adjoint_loopn [constructor] (X Y : Type*) (n : ℕ) :
    iterate_psusp n X →* Y ≃ X →* Ω[n] Y :=
  begin
    revert X Y, induction n with n IH: intro X Y,
    { reflexivity},
    { refine !susp_adjoint_loop ⬝e !IH ⬝e _, apply pmap_equiv_pmap_right,
      symmetry, apply loopn_succ_in}
  end

end EM
-- cohomology ∥ X → K(G,n) ∥
-- reduced cohomology ∥ X →* K(G,n) ∥
-- but we probably want to do this for any spectrum
