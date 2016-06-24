/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
-/

import homotopy.EM .spectrum

open eq is_equiv equiv is_conn is_trunc unit function pointed nat group algebra trunc trunc_index
     fiber prod fin pointed susp EM.ops

namespace EM

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
    refine !phomotopy_group_pequiv_loop_ptrunc⁻¹ᵉ* ⬝e* _ ⬝e* !phomotopy_group_pequiv_loop_ptrunc,
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
    (r : Π(p q : Ω[succ n] X), e (@concat (Ω[n] X) pt pt pt p q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n → X :=
  begin
    revert X e r H1 H2, induction n with n f: intro X e r H1 H2,
    { change trunc 1 (EM1 G) → X, intro x, induction x with x, exact EM1_map e r x},
    change trunc (n.+2) (susp (iterate_psusp n (pEM1 G))) → X, intro x,
    induction x with x, induction x with x,
    { exact pt},
    { exact pt},
    { change carrier (Ω X), refine f _ _ _ _ _ (tr x),
      { refine _⁻¹ᵉ ⬝e e, apply equiv_of_pequiv, apply pequiv_of_eq, apply loop_space_succ_eq_in},
      exact abstract begin
        intro p q, refine _ ⬝ !r, apply ap e, esimp,
        apply inv_tr_eq_of_eq_tr, symmetry,
        rewrite [- + ap_inv, - + tr_compose],
        refine !loop_space_succ_eq_in_concat ⬝ _, exact !tr_inv_tr ◾ !tr_inv_tr
      end end}
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
    { refine !idp_con ⬝ _, refine !ap_compose'⁻¹ ⬝ _, esimp, apply elim_pth},
    { replace (succ (succ n)) with ((succ n) + 1), rewrite [apn_succ],
      unfold [ap1], exact sorry}
    --exact !idp_con ⬝ !elim_pth
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

  definition EM_spectrum /-[constructor]-/ (G : CommGroup) : spectrum :=
  spectrum.Mk (K G) (λn, (loop_EM G n)⁻¹ᵉ*)

end EM
-- cohomology ∥ X → K(G,n) ∥
-- reduced cohomology ∥ X →* K(G,n) ∥
-- but we probably want to do this for any spectrum
