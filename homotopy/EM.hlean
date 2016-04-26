/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
-/

import homotopy.EM

open eq is_equiv equiv is_conn is_trunc unit function pointed nat group algebra trunc trunc_index
     fiber prod fin

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

  open sigma lift
  definition flatten_univ.{u v} {A : Type.{u}} {B : Type.{v}} (f : A → B) :
    Σ(A' B' : Type.{max u v}) (f' : A' → B') (g : A ≃ A') (h : B ≃ B'), h ∘ f ~ f' ∘ g :=
  ⟨lift A, lift B, lift_functor f, proof equiv_lift A qed, proof equiv_lift B qed,
    proof sorry qed⟩

  definition is_conn_inf [reducible] (A : Type) : Type := Πn, is_conn n A
  definition is_conn_fun_inf [reducible] {A B : Type} (f : A → B) : Type := Πn, is_conn_fun n f


end EM
