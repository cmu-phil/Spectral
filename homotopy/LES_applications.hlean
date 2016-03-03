import .LES_of_homotopy_groups homotopy.connectedness homotopy.homotopy_group
open eq is_trunc pointed homotopy is_equiv fiber equiv trunc nat chain_complex prod fin algebra
     group equiv.ops trunc_index function
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

  theorem is_contr_HG_fiber_of_is_connected {A B : Type*} (k n : ℕ) (f : A →* B)
    [H : is_conn_map n f] (H2 : k ≤ n) : is_contr (π[k] (pfiber f)) :=
  @(trivial_homotopy_group_of_is_conn (pfiber f) H2) (H pt)

  -- TODO: use this for trivial_homotopy_group_of_is_conn (in homotopy.homotopy_group)
  theorem is_conn_of_le (A : Type) {n k : ℕ₋₂} (H : n ≤ k) [is_conn k A] : is_conn n A :=
  begin
    apply is_contr_equiv_closed,
    apply trunc_trunc_equiv_left _ n k H
  end

  definition zero_le_of_nat (n : ℕ) : 0 ≤[ℕ₋₂] n :=
  of_nat_le_of_nat (zero_le n)

  local attribute is_conn_map [reducible] --TODO
  theorem is_conn_map_of_le {A B : Type} (f : A → B) {n k : ℕ₋₂} (H : n ≤ k)
    [is_conn_map k f] : is_conn_map n f :=
  λb, is_conn_of_le _ H

  definition is_surjective_trunc_functor {A B : Type} (n : ℕ₋₂) (f : A → B) [H : is_surjective f]
    : is_surjective (trunc_functor n f) :=
  begin
    cases n with n: intro b,
    { exact tr (fiber.mk !center !is_prop.elim)},
    { refine @trunc.rec _ _ _ _ _ b, {intro x, exact is_trunc_of_le _ !minus_one_le_succ},
      clear b, intro b, induction H b with v, induction v with a p,
      exact tr (fiber.mk (tr a) (ap tr p))}
  end

  definition is_surjective_cancel_right {A B C : Type} (g : B → C) (f : A → B)
    [H : is_surjective (g ∘ f)] : is_surjective g :=
  begin
    intro c,
    induction H c with v, induction v with a p,
    exact tr (fiber.mk (f a) p)
  end

  -- Lemma 7.5.14
  theorem is_equiv_trunc_functor_of_is_conn_map {A B : Type} (n : ℕ₋₂) (f : A → B)
    [H : is_conn_map n f] : is_equiv (trunc_functor n f) :=
  begin
    exact sorry
  end

  definition is_equiv_tinverse [constructor] (A : Type*) : is_equiv (@tinverse A) :=
  by apply @is_equiv_trunc_functor; apply is_equiv_eq_inverse

  local attribute comm_group.to_group [coercion]
  local attribute is_equiv_tinverse [instance]

  theorem is_equiv_π_of_is_connected.{u} {A B : pType.{u}} (n k : ℕ) (f : A →* B)
    [H : is_conn_map n f] (H2 : k ≤ n) : is_equiv (π→[k] f) :=
  begin
    induction k using rec_on_even_odd with k: cases k with k,
    { /- k = 0 -/
      change (is_equiv (trunc_functor 0 f)), apply is_equiv_trunc_functor_of_is_conn_map,
      refine is_conn_map_of_le f (zero_le_of_nat n)},
    { /- k > 0 even -/
      have H2' : 2 * k + 1 ≤ n, from le.trans !self_le_succ H2,
      exact
      @is_equiv_of_trivial _
        (LES_of_homotopy_groups3 f) _
        (is_exact_LES_of_homotopy_groups3 f (k, 5))
        (is_exact_LES_of_homotopy_groups3 f (succ k, 0))
        (@is_contr_HG_fiber_of_is_connected A B (2 * k + 1) n f H H2')
        (@is_contr_HG_fiber_of_is_connected A B (2 * succ k) n f H H2)
        (@pgroup_of_group _ (comm_group_LES_of_homotopy_groups3 f k 0) idp)
        (@pgroup_of_group _ (comm_group_LES_of_homotopy_groups3 f k 1) idp)
        (homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun3 f (k, 0)))},
    { /- k = 1 -/
      exact sorry},
    { /- k > 1 odd -/
      have H2' : 2 * succ k ≤ n, from le.trans !self_le_succ H2,
      have H3 : is_equiv (π→*[2*(succ k) + 1] f ∘* tinverse), from
      @is_equiv_of_trivial _
        (LES_of_homotopy_groups3 f) _
        (is_exact_LES_of_homotopy_groups3 f (succ k, 2))
        (is_exact_LES_of_homotopy_groups3 f (succ k, 3))
        (@is_contr_HG_fiber_of_is_connected A B (2 * succ k) n f H H2')
        (@is_contr_HG_fiber_of_is_connected A B (2 * succ k + 1) n f H H2)
        (@pgroup_of_group _ (comm_group_LES_of_homotopy_groups3 f k 3) idp)
        (@pgroup_of_group _ (comm_group_LES_of_homotopy_groups3 f k 4) idp)
        (homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun3 f (k, 3))),
      exact @(is_equiv.cancel_right tinverse) !is_equiv_tinverse
                  (pmap.to_fun (π→*[2*(succ k) + 1] f)) H3}
  end

  theorem is_surjective_π_of_is_connected.{u} {A B : pType.{u}} (n : ℕ) (f : A →* B)
    [H : is_conn_map n f] : is_surjective (π→[n + 1] f) :=
  begin
    induction n using rec_on_even_odd with n,
    { cases n with n,
      { exact sorry},
      { have H3 : is_surjective (π→*[2*(succ n) + 1] f ∘* tinverse), from
        @is_surjective_of_trivial _
          (LES_of_homotopy_groups3 f) _
          (is_exact_LES_of_homotopy_groups3 f (succ n, 2))
          (@is_contr_HG_fiber_of_is_connected A B (2 * succ n) (2 * succ n) f H !le.refl),
        exact @(is_surjective_cancel_right (pmap.to_fun (π→*[2*(succ n) + 1] f)) tinverse) H3}},
    { exact @is_surjective_of_trivial _
        (LES_of_homotopy_groups3 f) _
        (is_exact_LES_of_homotopy_groups3 f (k, 5))
        (@is_contr_HG_fiber_of_is_connected A B (2 * k + 1) (2 * k + 1) f H !le.refl)}
  end

end is_conn
