/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
-/

import homotopy.EM

open eq is_equiv equiv is_conn is_trunc unit function pointed nat group algebra trunc trunc_index
     fiber prod fin pointed

namespace chain_complex
  open succ_str

  definition is_contr_of_is_embedding_of_is_surjective {N : succ_str} (X : chain_complex N) {n : N}
    (H : is_exact_at X (S n)) [is_embedding (cc_to_fn X n)]
    [H2 : is_surjective (cc_to_fn X (S (S (S n))))] : is_contr (X (S (S n))) :=
  begin
    apply is_contr.mk pt, intro x,
    have p : cc_to_fn X n (cc_to_fn X (S n) x) = cc_to_fn X n pt,
      from !cc_is_chain_complex ⬝ !respect_pt⁻¹,
    have q : cc_to_fn X (S n) x = pt, from is_injective_of_is_embedding p,
    induction H x q with y r,
    induction H2 y with z s,
    exact (cc_is_chain_complex X _ z)⁻¹ ⬝ ap (cc_to_fn X _) s ⬝ r
  end

end chain_complex open chain_complex

namespace EM

    -- MOVE to connectedness
    definition is_conn_fun_to_unit_of_is_conn (n : ℕ₋₂) (A : Type) [H : is_conn n A]
      : is_conn_fun n (const A unit.star) :=
    begin
      intro u, induction u,
      exact is_conn_equiv_closed n (fiber.fiber_star_equiv A)⁻¹ᵉ _,
    end

  /- Whitehead Corollaries -/

  -- to pointed

  definition pointed_eta_pequiv [constructor] (A : Type*) : A ≃* pointed.MK A pt :=
  pequiv.mk id !is_equiv_id idp

  /- every pointed map is homotopic to one of the form `pmap_of_map _ _`, up to some
     pointed equivalences -/
  definition phomotopy_pmap_of_map {A B : Type*} (f : A →* B) :
    (pointed_eta_pequiv B ⬝e* (pequiv_of_eq_pt (respect_pt f))⁻¹ᵉ*) ∘* f ∘*
      (pointed_eta_pequiv A)⁻¹ᵉ* ~* pmap_of_map f pt :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { esimp [pequiv.trans, pequiv.symm],
      exact !con.right_inv⁻¹ ⬝ ((!idp_con⁻¹ ⬝ !ap_id⁻¹) ◾ (!ap_id⁻¹⁻² ⬝ !idp_con⁻¹)), }
  end

  -- reorder arguments of is_equiv_compose
  -- rename whiteheads_principle to whitehead_principle
  definition whitehead_principle_pointed (n : ℕ₋₂) {A B : Type*}
    [HA : is_trunc n A] [HB : is_trunc n B] [is_conn 0 A] (f : A →* B)
    (H : Πk, is_equiv (π→*[k] f)) : is_equiv f :=
  begin
    apply whiteheads_principle n, rexact H 0,
    intro a k, revert a, apply is_conn.elim -1,
    have is_equiv (π→*[k + 1] (pointed_eta_pequiv B ⬝e* (pequiv_of_eq_pt (respect_pt f))⁻¹ᵉ*)
           ∘* π→*[k + 1] f ∘* π→*[k + 1] (pointed_eta_pequiv A)⁻¹ᵉ*),
    begin
      apply is_equiv_compose (π→*[k + 1] f ∘* π→*[k + 1] (pointed_eta_pequiv A)⁻¹ᵉ*),
      apply is_equiv_compose (π→*[k + 1] (pointed_eta_pequiv A)⁻¹ᵉ*),
      all_goals apply is_equiv_homotopy_group_functor,
    end,
    refine @(is_equiv.homotopy_closed _) _ this _,
    apply to_homotopy,
    refine pwhisker_left _ !phomotopy_group_functor_compose⁻¹* ⬝* _,
    refine !phomotopy_group_functor_compose⁻¹* ⬝* _,
    apply phomotopy_group_functor_phomotopy, apply phomotopy_pmap_of_map
  end

  -- replace in homotopy_group?
  theorem trivial_homotopy_group_of_is_trunc' (A : Type*) {n k : ℕ} [is_trunc n A] (H : n < k)
    : is_contr (π[k] A) :=
  begin
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply @is_trunc_of_le A n _,
    apply trunc_index.le_of_succ_le_succ,
    rewrite [succ_sub_two_succ k],
    exact of_nat_le_of_nat H,
  end

  definition is_trunc_pointed_MK [instance] [priority 1100] (n : ℕ₋₂) {A : Type} (a : A)
    [H : is_trunc n A] : is_trunc n (pointed.MK A a) :=
  H

  definition is_contr_of_trivial_homotopy (n : ℕ₋₂) (A : Type) [is_trunc n A] [is_conn 0 A]
    (H : Πk a, is_contr (π[k] (pointed.MK A a))) : is_contr A :=
  begin
    fapply is_trunc_is_equiv_closed_rev, { exact λa, ⋆},
    apply whiteheads_principle n,
    { apply is_equiv_trunc_functor_of_is_conn_fun, apply is_conn_fun_to_unit_of_is_conn},
    intro a k,
    apply @is_equiv_of_is_contr,
    refine trivial_homotopy_group_of_is_trunc' _ !one_le_succ,
  end

  definition is_contr_of_trivial_homotopy_nat (n : ℕ) (A : Type) [is_trunc n A] [is_conn 0 A]
    (H : Πk a, k ≤ n → is_contr (π[k] (pointed.MK A a))) : is_contr A :=
  begin
    apply is_contr_of_trivial_homotopy n,
    intro k a, apply @lt_ge_by_cases _ _ n k,
    { intro H', exact trivial_homotopy_group_of_is_trunc' _ H'},
    { intro H', exact H k a H'}
  end

  definition is_contr_of_trivial_homotopy_pointed (n : ℕ₋₂) (A : Type*) [is_trunc n A]
    (H : Πk, is_contr (π[k] A)) : is_contr A :=
  begin
    have is_conn 0 A, proof H 0 qed,
    fapply is_contr_of_trivial_homotopy n A,
    intro k, apply is_conn.elim -1,
    cases A with A a, exact H k
  end

  definition is_contr_of_trivial_homotopy_nat_pointed (n : ℕ) (A : Type*) [is_trunc n A]
    (H : Πk, k ≤ n → is_contr (π[k] A)) : is_contr A :=
  begin
    have is_conn 0 A, proof H 0 !zero_le qed,
    fapply is_contr_of_trivial_homotopy_nat n A,
    intro k a H', revert a, apply is_conn.elim -1,
    cases A with A a, exact H k H'
  end

  -- replace in homotopy_group
  definition phomotopy_group_ptrunc_of_le [constructor] {k n : ℕ} (H : k ≤ n) (A : Type*) :
    π*[k] (ptrunc n A) ≃* π*[k] A :=
  calc
    π*[k] (ptrunc n A) ≃* Ω[k] (ptrunc k (ptrunc n A))
             : phomotopy_group_pequiv_loop_ptrunc k (ptrunc n A)
      ... ≃* Ω[k] (ptrunc k A)
             : loopn_pequiv_loopn k (ptrunc_ptrunc_pequiv_left A (of_nat_le_of_nat H))
      ... ≃* π*[k] A : (phomotopy_group_pequiv_loop_ptrunc k A)⁻¹ᵉ*

  definition is_conn_fun_of_equiv_on_homotopy_groups.{u} (n : ℕ) {A B : Type.{u}} (f : A → B)
    [is_equiv (trunc_functor 0 f)]
    (H1 : Πa k, k ≤ n → is_equiv (homotopy_group_functor k (pmap_of_map f a)))
    (H2 : Πa, is_surjective (homotopy_group_functor (succ n) (pmap_of_map f a))) : is_conn_fun n f :=
  have H2' : Πa k, k ≤ n → is_surjective (homotopy_group_functor (succ k) (pmap_of_map f a)),
  begin
    intro a k H, cases H with n' H',
    { apply H2},
    { apply is_surjective_of_is_equiv, apply H1, exact succ_le_succ H'}
  end,
  have H3 : Πa, is_contr (ptrunc n (pfiber (pmap_of_map f a))),
  begin
    intro a, apply is_contr_of_trivial_homotopy_nat_pointed n,
    { intro k H, apply is_trunc_equiv_closed_rev, exact phomotopy_group_ptrunc_of_le H _,
      rexact @is_contr_of_is_embedding_of_is_surjective +3ℕ
               (LES_of_homotopy_groups (pmap_of_map f a)) (k, 0)
               (is_exact_LES_of_homotopy_groups _ _)
               proof @(is_embedding_of_is_equiv _)  (H1 a k H) qed
               proof (H2' a k H) qed}
  end,
  show Πb, is_contr (trunc n (fiber f b)),
  begin
    intro b,
    note p := right_inv (trunc_functor 0 f) (tr b), revert p,
    induction (trunc_functor 0 f)⁻¹ (tr b), esimp, intro p,
    induction !tr_eq_tr_equiv p with q,
    rewrite -q, exact H3 a
  end

  -- open sigma lift
  -- definition flatten_univ.{u v} {A : Type.{u}} {B : Type.{v}} (f : A → B) :
  --   Σ(A' B' : Type.{max u v}) (f' : A' → B') (g : A ≃ A') (h : B ≃ B'), h ∘ f ~ f' ∘ g :=
  -- ⟨lift A, lift B, lift_functor f, proof equiv_lift A qed, proof equiv_lift B qed,
  --   proof sorry qed⟩

  definition is_conn_inf [reducible] (A : Type) : Type := Πn, is_conn n A
  definition is_conn_fun_inf [reducible] {A B : Type} (f : A → B) : Type := Πn, is_conn_fun n f

  /- applications to EM spaces -/

  -- TODO

  definition pEM1_pmap [constructor] {G : Group} {X : Type*} (e : Ω X ≃ G)
    (r : Πp q, e (p ⬝ q) = e p * e q) [is_conn 0 X] [is_trunc 1 X] : pEM1 G →* X :=
  begin
    apply pmap.mk (EM1_map e r),
    reflexivity,
  end

  definition loop_pEM1 [constructor] (G : Group) : Ω (pEM1 G) ≃* pType_of_Group G :=
  pequiv_of_equiv (base_eq_base_equiv G) idp

  attribute base_eq_base_equiv [constructor]
  export [unfold] groupoid_quotient

  definition loop_pEM1_pmap {G : Group} {X : Type*} (e : Ω X ≃ G)
    (r : Πp q, e (p ⬝ q) = e p * e q) [is_conn 0 X] [is_trunc 1 X] :
    Ω→(pEM1_pmap e r) ~ e⁻¹ᵉ ∘ base_eq_base_equiv G :=
  begin
    apply homotopy_of_inv_homotopy_pre (base_eq_base_equiv G),
    esimp, intro g, exact !idp_con ⬝ !elim_pth
  end

  definition pEM1_pequiv'.{u} {G : Group.{u}} {X : pType.{u}} (e : Ω X ≃ G)
    (r : Πp q, e (p ⬝ q) = e p * e q) [is_conn 0 X] [is_trunc 1 X] : pEM1 G ≃* X :=
  begin
    apply pequiv_of_pmap (pEM1_pmap e r),
    apply whitehead_principle_pointed 1,
    intro k, cases k with k,
    { apply @is_equiv_of_is_contr,
      all_goals (esimp; exact _)},
    { cases k with k,
      { apply is_equiv_trunc_functor, esimp,
        apply is_equiv.homotopy_closed, rotate 1,
        { symmetry, exact loop_pEM1_pmap _ _},
        apply is_equiv_compose, apply to_is_equiv},
      { apply @is_equiv_of_is_contr,
        do 2 apply trivial_homotopy_group_of_is_trunc _ _ _ !one_le_succ}}
  end

  definition pEM1_pequiv.{u} {G : Group.{u}} {X : pType.{u}} (e : π₁ X ≃g G)
    [is_conn 0 X] [is_trunc 1 X] : pEM1 G ≃* X :=
  begin
    apply pEM1_pequiv' (!trunc_equiv⁻¹ᵉ ⬝e equiv_of_isomorphism e),
    intro p q, esimp, exact respect_mul e (tr p) (tr q)
  end

  definition KG1_pequiv.{u} {X Y : pType.{u}} (e : π₁ X ≃g π₁ Y)
    [is_conn 0 X] [is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y] : X ≃* Y :=
  (pEM1_pequiv e)⁻¹ᵉ* ⬝e* pEM1_pequiv !isomorphism.refl


end EM
