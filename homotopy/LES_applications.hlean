/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import .LES_of_homotopy_groups homotopy.connectedness homotopy.homotopy_group homotopy.join
       homotopy.complex_hopf
open eq is_trunc pointed is_conn is_equiv fiber equiv trunc nat chain_complex fin algebra
     group trunc_index function join pushout prod sigma sigma.ops

namespace nat
  open sigma sum
  definition eq_even_or_eq_odd (n : ℕ) : (Σk, 2 * k = n) ⊎ (Σk, 2 * k + 1 = n) :=
  begin
    induction n with n IH,
    { exact inl ⟨0, idp⟩},
    { induction IH with H H: induction H with k p: induction p,
      { exact inr ⟨k, idp⟩},
      { refine inl ⟨k+1, idp⟩}}
  end

  definition rec_on_even_odd {P : ℕ → Type} (n : ℕ) (H : Πk, P (2 * k)) (H2 : Πk, P (2 * k + 1))
    : P n :=
  begin
    cases eq_even_or_eq_odd n with v v: induction v with k p: induction p,
    { exact H k},
    { exact H2 k}
  end

end nat
open nat

namespace pointed

  definition apn_phomotopy {A B : Type*} {f g : A →* B} (n : ℕ) (p : f ~* g)
    : apn n f ~* apn n g :=
  begin
    induction n with n IH,
    { exact p},
    { exact ap1_phomotopy IH}
  end

end pointed open pointed

namespace chain_complex
  section
  universe variable u
  parameters {F X Y : pType.{u}} (f : X →* Y) (g : F →* X) (e : pfiber f ≃* F)
             (p : ppoint f ~* g ∘* e)
  include f p
  open succ_str
  definition fibration_sequence_car [reducible] : +3ℕ → Type*
  | (n, fin.mk 0 H) := Ω[n] Y
  | (n, fin.mk 1 H) := Ω[n] X
  | (n, fin.mk k H) := Ω[n] F

  definition fibration_sequence_fun
    : Π(n : +3ℕ), fibration_sequence_car (S n) →* fibration_sequence_car n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] g qed
  | (n, fin.mk 2 H) := proof Ω→[n] (e ∘* boundary_map f) ∘* pcast (loop_space_succ_eq_in Y n) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition fibration_sequence_pequiv : Π(x : +3ℕ),
     loop_spaces2 f x ≃* fibration_sequence_car x
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := loopn_pequiv_loopn n e
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  /- all cases where n>0 are basically the same -/
  definition fibration_sequence_fun_phomotopy : Π(x : +3ℕ),
    fibration_sequence_pequiv x ∘* loop_spaces_fun2 f x ~*
      (fibration_sequence_fun x ∘* fibration_sequence_pequiv (S x))
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) :=
    begin refine !pid_comp ⬝* _, refine apn_phomotopy n p ⬝* _,
      refine !apn_compose ⬝* _, reflexivity end
  | (n, fin.mk 2 H) := begin refine !passoc⁻¹* ⬝* _ ⬝* !comp_pid⁻¹*, apply pwhisker_right,
      refine _ ⬝* !apn_compose⁻¹*, reflexivity end
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition type_fibration_sequence [constructor] : type_chain_complex +3ℕ :=
  transfer_type_chain_complex
    (LES_of_loop_spaces2 f)
    fibration_sequence_fun
    fibration_sequence_pequiv
    fibration_sequence_fun_phomotopy

  definition is_exact_type_fibration_sequence : is_exact_t type_fibration_sequence :=
  begin
    intro n,
    apply is_exact_at_t_transfer,
    apply is_exact_LES_of_loop_spaces2
  end

  definition fibration_sequence [constructor] : chain_complex +3ℕ :=
  trunc_chain_complex type_fibration_sequence

  end
end chain_complex

namespace is_conn

  local attribute comm_group.to_group [coercion]
  local attribute is_equiv_tinverse [instance]

  theorem is_equiv_π_of_is_connected.{u} {A B : pType.{u}} (n k : ℕ) (f : A →* B)
    [H : is_conn_fun n f] (H2 : k ≤ n) : is_equiv (π→[k] f) :=
  begin
    cases k with k,
    { /- k = 0 -/
      change (is_equiv (trunc_functor 0 f)), apply is_equiv_trunc_functor_of_is_conn_fun,
      refine is_conn_fun_of_le f (zero_le_of_nat n)},
    { /- k > 0 -/
     have H2' : k ≤ n, from le.trans !self_le_succ H2,
      exact
      @is_equiv_of_trivial _
        (LES_of_homotopy_groups f) _
        (is_exact_LES_of_homotopy_groups f (k, 2))
        (is_exact_LES_of_homotopy_groups f (succ k, 0))
        (@is_contr_HG_fiber_of_is_connected A B k n f H H2')
        (@is_contr_HG_fiber_of_is_connected A B (succ k) n f H H2)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups f k 0) idp)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups f k 1) idp)
        (homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun f (k, 0)))},
  end

  theorem is_surjective_π_of_is_connected.{u} {A B : pType.{u}} (n : ℕ) (f : A →* B)
    [H : is_conn_fun n f] : is_surjective (π→[n + 1] f) :=
  @is_surjective_of_trivial _
    (LES_of_homotopy_groups f) _
    (is_exact_LES_of_homotopy_groups f (n, 2))
    (@is_contr_HG_fiber_of_is_connected A B n n f H !le.refl)

  -- TODO: move and rename?
  definition natural_square2 {A B X : Type} {f : A → X} {g : B → X} (h : Πa b, f a = g b)
    {a a' : A} {b b' : B} (p : a = a') (q : b = b')
    : square (ap f p) (ap g q) (h a b) (h a' b') :=
  by induction p; induction q; exact hrfl

end is_conn

namespace sigma
  definition ppr1 {A : Type*} {B : A → Type*} : (Σ*(x : A), B x) →* A :=
  pmap.mk pr1 idp

  definition ppr2 {A : Type*} (B : A → Type*) (v : (Σ*(x : A), B x)) : B (ppr1 v) :=
  pr2 v
end sigma

namespace hopf

  open sphere.ops susp circle sphere_index

  attribute hopf [unfold 4]
  -- definition phopf (x : psusp A) : Type* :=
  -- pointed.MK (hopf A x)
  -- begin
  --   induction x with a: esimp,
  --   do 2 exact 1,
  --   apply pathover_of_tr_eq, rewrite [↑hopf, elim_type_merid, ▸*, mul_one],
  -- end

  -- maybe define this as a composition of pointed maps?
  definition complex_phopf [constructor] : S. 3 →* S. 2 :=
  proof pmap.mk complex_hopf idp qed

  definition fiber_pr1_fun {A : Type} {B : A → Type} {a : A} (b : B a)
    : fiber_pr1 B a (fiber.mk ⟨a, b⟩ idp) = b :=
  idp

  --TODO: in fiber.equiv_precompose, make f explicit
  open sphere sphere.ops

  definition add_plus_one_of_nat (n m : ℕ) : (n +1+ m) = sphere_index.of_nat (n + m + 1) :=
  begin
    induction m with m IH,
    { reflexivity },
    { exact ap succ IH}
  end

  -- definition pjoin_pspheres (n m : ℕ) : join (S. n) (S. m) ≃ (S. (n + m + 1)) :=
  -- join.spheres n m ⬝e begin esimp, apply equiv_of_eq, apply ap S, apply add_plus_one_of_nat end

  definition part_of_complex_hopf : S (of_nat 3) → sigma (hopf S¹) :=
  begin
    intro x, apply inv (hopf.total S¹), apply inv (join.spheres 1 1), exact x
  end

  definition part_of_complex_hopf_base2
    : (part_of_complex_hopf (@sphere.base 3)).2 = circle.base :=
  begin
    exact sorry
  end

  definition pfiber_complex_phopf : pfiber complex_phopf ≃* S. 1 :=
  begin
    fapply pequiv_of_equiv,
    { esimp, unfold [complex_hopf],
      refine @fiber.equiv_precompose _ _ (sigma.pr1 ∘ (hopf.total S¹)⁻¹ᵉ) _ _
               (join.spheres 1 1)⁻¹ᵉ _ ⬝e _,
      refine fiber.equiv_precompose (hopf.total S¹)⁻¹ᵉ ⬝e _,
      apply fiber_pr1},
    { esimp, refine _ ⬝ part_of_complex_hopf_base2, apply fiber_pr1_fun}
  end

  open int

  definition one_le_succ (n : ℕ) : 1 ≤ succ n :=
  nat.succ_le_succ !zero_le

  definition π2S2 : πg[1+1] (S. 2) = gℤ :=
  begin
    refine _ ⬝ fundamental_group_of_circle,
    refine _ ⬝ ap (λx, π₁ x) (eq_of_pequiv pfiber_complex_phopf),
    fapply Group_eq,
    { fapply equiv.mk,
      { exact cc_to_fn (LES_of_homotopy_groups complex_phopf) (1, 2)},
      { refine @is_equiv_of_trivial _
        _ _
        (is_exact_LES_of_homotopy_groups _ (1, 1))
        (is_exact_LES_of_homotopy_groups _ (1, 2))
        _
        _
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        _,
        { rewrite [LES_of_homotopy_groups_1, ▸*],
          have H : 1 ≤[ℕ] 2, from !one_le_succ,
          apply trivial_homotopy_group_of_is_conn, exact H, rexact is_conn_psphere 3},
        { refine tr_rev (λx, is_contr (ptrunctype._trans_of_to_pType x))
                        (LES_of_homotopy_groups_1 complex_phopf 2) _,
          apply trivial_homotopy_group_of_is_conn, apply le.refl, rexact is_conn_psphere 3},
        { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (0, 2))}}},
    { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (0, 2))}
  end

  open circle
  definition πnS3_eq_πnS2 (n : ℕ) : πg[n+2 +1] (S. 3) = πg[n+2 +1] (S. 2) :=
  begin
    fapply Group_eq,
    { fapply equiv.mk,
      { exact cc_to_fn (LES_of_homotopy_groups complex_phopf) (n+3, 0)},
      { have H : is_trunc 1 (pfiber complex_phopf),
        from @(is_trunc_equiv_closed_rev _ pfiber_complex_phopf) is_trunc_circle,
        refine @is_equiv_of_trivial _
        _ _
        (is_exact_LES_of_homotopy_groups _ (n+2, 2))
        (is_exact_LES_of_homotopy_groups _ (n+3, 0))
        _
        _
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        _,
        { rewrite [▸*, LES_of_homotopy_groups_2 _ (n +[ℕ] 2)],
          have H : 1 ≤[ℕ] n + 1, from !one_le_succ,
          apply trivial_homotopy_group_of_is_trunc _ _ _ H},
        { refine tr_rev (λx, is_contr (ptrunctype._trans_of_to_pType x))
                        (LES_of_homotopy_groups_2 complex_phopf _) _,
          have H : 1 ≤[ℕ] n + 2, from !one_le_succ,
          apply trivial_homotopy_group_of_is_trunc _ _ _ H},
        { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (n+2, 0))}}},
    { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (n+2, 0))}
  end

end hopf
