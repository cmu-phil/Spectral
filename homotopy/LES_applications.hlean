/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import .LES_of_homotopy_groups homotopy.connectedness homotopy.homotopy_group homotopy.join
open eq is_trunc pointed is_conn is_equiv fiber equiv trunc nat chain_complex prod fin algebra
     group trunc_index function join pushout

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
    { /- k > 0 even -/
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

  -- TODO: move
  section
    open sphere sphere_index

    definition add_plus_one_minus_one (n : ℕ₋₁) : n +1+ -1 = n := idp
    definition add_plus_one_succ (n m : ℕ₋₁) : n +1+ (m.+1) = (n +1+ m).+1 := idp
    definition minus_one_add_plus_one (n : ℕ₋₁) : -1 +1+ n = n :=
    begin induction n with n IH, reflexivity, exact ap succ IH end
    definition succ_add_plus_one (n m : ℕ₋₁) : (n.+1) +1+ m = (n +1+ m).+1 :=
    begin induction m with m IH, reflexivity, exact ap succ IH end

  end

end is_conn
