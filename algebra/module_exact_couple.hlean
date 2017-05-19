/- Exact couples of graded (left-) R-modules. -/

-- Author: Floris van Doorn

import .graded ..homotopy.spectrum .product_group

open algebra is_trunc left_module is_equiv equiv eq function nat

-- move
section
  open group int chain_complex pointed succ_str

  definition is_exact_of_is_exact_at {N : succ_str} {A : chain_complex N} {n : N}
    (H : is_exact_at A n) : is_exact (cc_to_fn A (S n)) (cc_to_fn A n) :=
  is_exact.mk (cc_is_chain_complex A n) H

  definition is_equiv_mul_right [constructor] {A : Group} (a : A) : is_equiv (λb, b * a) :=
  adjointify _ (λb : A, b * a⁻¹) (λb, !inv_mul_cancel_right) (λb, !mul_inv_cancel_right)

  definition right_action [constructor] {A : Group} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_mul_right a)

  definition is_equiv_add_right [constructor] {A : AddGroup} (a : A) : is_equiv (λb, b + a) :=
  adjointify _ (λb : A, b - a) (λb, !neg_add_cancel_right) (λb, !add_neg_cancel_right)

  definition add_right_action [constructor] {A : AddGroup} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_add_right a)


  section
    variables {A B : Type} (f : A ≃ B) [ab_group A]

    -- to group
    definition group_equiv_mul_comm (b b' : B) : group_equiv_mul f b b' = group_equiv_mul f b' b :=
    by rewrite [↑group_equiv_mul, mul.comm]

    definition ab_group_equiv_closed : ab_group B :=
    ⦃ab_group, group_equiv_closed f,
      mul_comm := group_equiv_mul_comm f⦄
  end

  definition ab_group_of_is_contr (A : Type) [is_contr A] : ab_group A :=
  have ab_group unit, from ab_group_unit,
  ab_group_equiv_closed (equiv_unit_of_is_contr A)⁻¹ᵉ

  definition group_of_is_contr (A : Type) [is_contr A] : group A :=
  have ab_group A, from ab_group_of_is_contr A, by apply _

  definition ab_group_lift_unit : ab_group (lift unit) :=
  ab_group_of_is_contr (lift unit)

  definition trivial_ab_group_lift : AbGroup :=
  AbGroup.mk _ ab_group_lift_unit

  definition homomorphism_of_is_contr_right (A : Group) {B : Type} (H : is_contr B) :
    A →g Group.mk B (group_of_is_contr B) :=
  group.homomorphism.mk (λa, center _) (λa a', !is_prop.elim)

  open trunc pointed is_conn
  definition ab_group_homotopy_group_of_is_conn (n : ℕ) (A : Type*) [H : is_conn 1 A] : ab_group (π[n] A) :=
  begin
    have is_conn 0 A, from !is_conn_of_is_conn_succ,
    cases n with n,
    { unfold [homotopy_group, ptrunc], apply ab_group_of_is_contr },
    cases n with n,
    { unfold [homotopy_group, ptrunc], apply ab_group_of_is_contr },
    exact ab_group_homotopy_group n A
  end

end

namespace int /- move to int-/
  definition max0 : ℤ → ℕ
  | (of_nat n) := n
  | (-[1+ n])  := 0

  lemma le_max0 : Π(n : ℤ), n ≤ of_nat (max0 n)
  | (of_nat n) := proof le.refl n qed
  | (-[1+ n])  := proof unit.star qed

  lemma le_of_max0_le {n : ℤ} {m : ℕ} (h : max0 n ≤ m) : n ≤ of_nat m :=
  le.trans (le_max0 n) (of_nat_le_of_nat_of_le h)

end int

/- exact couples -/

namespace left_module

  structure exact_couple (R : Ring) (I : Set) : Type :=
    (D E : graded_module R I)
    (i : D →gm D) (j : D →gm E) (k : E →gm D)
    (ij : is_exact_gmod i j)
    (jk : is_exact_gmod j k)
    (ki : is_exact_gmod k i)

  namespace derived_couple
  section
  open exact_couple

  parameters {R : Ring} {I : Set} (X : exact_couple R I)
  local abbreviation D := D X
  local abbreviation E := E X
  local abbreviation i := i X
  local abbreviation j := j X
  local abbreviation k := k X
  local abbreviation ij := ij X
  local abbreviation jk := jk X
  local abbreviation ki := ki X

  definition d : E →gm E := j ∘gm k
  definition D' : graded_module R I := graded_image i
  definition E' : graded_module R I := graded_homology d d

  definition is_contr_E' {x : I} (H : is_contr (E x)) : is_contr (E' x) :=
  !is_contr_homology

  definition is_contr_D' {x : I} (H : is_contr (D x)) : is_contr (D' x) :=
  !is_contr_image_module

  definition i' : D' →gm D' :=
  graded_image_lift i ∘gm graded_submodule_incl _
  -- degree i + 0

  lemma is_surjective_i' {x y : I} (p : deg i' x = y)
    (H : Π⦃z⦄ (q : deg i z = x), is_surjective (i ↘ q)) : is_surjective (i' ↘ p) :=
  begin
    apply is_surjective_graded_hom_compose,
    { intro y q, apply is_surjective_graded_image_lift },
    { intro y q, apply is_surjective_of_is_equiv,
      induction q,
      exact to_is_equiv (equiv_of_isomorphism (image_module_isomorphism (i ← x) (H _)))
      }
  end

  lemma j_lemma1 ⦃x : I⦄ (m : D x) : d ((deg j) x) (j x m) = 0 :=
  begin
    rewrite [graded_hom_compose_fn,↑d,graded_hom_compose_fn],
    refine ap (graded_hom_fn j (deg k (deg j x))) _ ⬝
      !to_respect_zero,
    exact compose_constant.elim (gmod_im_in_ker (jk)) x m
  end

  lemma j_lemma2 : Π⦃x : I⦄ ⦃m : D x⦄ (p : i x m = 0),
    (graded_quotient_map _ ∘gm graded_hom_lift j j_lemma1) x m = 0 :> E' _ :=
  begin
    have Π⦃x y : I⦄ (q : deg k x = y) (r : deg d x = deg j y)
      (s : ap (deg j) q = r) ⦃m : D y⦄ (p : i y m = 0), image (d ↘ r) (j y m),
    begin
      intros, induction s, induction q,
      note m_in_im_k := is_exact.ker_in_im (ki idp _) _ p,
      induction m_in_im_k with e q,
      induction q,
      apply image.mk e idp
    end,
    have Π⦃x : I⦄ ⦃m : D x⦄ (p : i x m = 0), image (d ← (deg j x)) (j x m),
    begin
      intros,
      refine this _ _ _ p,
      exact to_right_inv (deg k) _ ⬝ to_left_inv (deg j) x,
      apply is_set.elim
      -- rewrite [ap_con, -adj],
    end,
    intros,
    rewrite [graded_hom_compose_fn],
    exact quotient_map_eq_zero _ (this p)
  end

  definition j' : D' →gm E' :=
  graded_image_elim (graded_homology_intro d d ∘gm graded_hom_lift j j_lemma1) j_lemma2
  -- degree deg j - deg i

  lemma k_lemma1 ⦃x : I⦄ (m : E x) : image (i ← (deg k x)) (k x m) :=
  begin
    exact sorry
  end

  lemma k_lemma2 : compose_constant (graded_hom_lift k k_lemma1 : E →gm D') d :=
  begin
    --   apply compose_constant.mk, intro x m,
    --   rewrite [graded_hom_compose_fn],
    --   refine ap (graded_hom_fn (graded_image_lift i) (deg k (deg d x))) _ ⬝ !to_respect_zero,
    --   exact compose_constant.elim (gmod_im_in_ker jk) (deg k x) (k x m)
    exact sorry
  end

  definition k' : E' →gm D' :=
  graded_homology_elim (graded_hom_lift k k_lemma1) k_lemma2

  definition deg_i' : deg i' ~ deg i := by reflexivity
  definition deg_j' : deg j' ~ deg j ∘ (deg i)⁻¹ := by reflexivity
  definition deg_k' : deg k' ~ deg k := by reflexivity

  lemma i'j' : is_exact_gmod i' j' :=
  begin
    apply is_exact_gmod.mk,
    { intro x, refine total_image.rec _, intro m, exact sorry
      -- exact calc
      --   j' (deg i' x) (i' x ⟨(i ← x) m, image.mk m idp⟩)
      --       = j' (deg i' x) (graded_image_lift i x ((i ← x) m)) : idp
      --   ... = graded_homology_intro d d (deg j ((deg i)⁻¹ᵉ (deg i x)))
      --           (graded_hom_lift j j_lemma1 ((deg i)⁻¹ᵉ (deg i x))
      --           (i ↘ (!to_right_inv ⬝ !to_left_inv⁻¹) m)) : _
      --   ... = graded_homology_intro d d (deg j ((deg i)⁻¹ᵉ (deg i x)))
      --           (graded_hom_lift j j_lemma1 ((deg i)⁻¹ᵉ (deg i x))
      --           (i ↘ (!to_right_inv ⬝ !to_left_inv⁻¹) m)) : _
      --   ... = 0 : _
      },
    { exact sorry }
  end

  lemma j'k' : is_exact_gmod j' k' :=
  begin
    apply is_exact_gmod.mk,
    { exact sorry },
    { exact sorry }
  end

  lemma k'i' : is_exact_gmod k' i' :=
  begin
    apply is_exact_gmod.mk,
    { intro x m, exact sorry },
    { exact sorry }
  end

  end
  end derived_couple

  section
  open derived_couple exact_couple

  definition derived_couple [constructor] {R : Ring} {I : Set}
    (X : exact_couple R I) : exact_couple R I :=
  ⦃exact_couple, D := D' X, E := E' X, i := i' X, j := j' X, k := k' X,
    ij := i'j' X, jk := j'k' X, ki := k'i' X⦄

  structure is_bounded {R : Ring} {I : Set} (X : exact_couple R I) : Type :=
  mk' :: (B B' : I → ℕ)
    (Dub : Π⦃x y⦄ ⦃s : ℕ⦄, (deg (i X))^[s] x = y → B x ≤ s → is_contr (D X y))
    (Dlb : Π⦃x y z⦄ ⦃s : ℕ⦄ (p : deg (i X) x = y), (deg (i X))^[s] y = z → B' z ≤ s → is_surjective (i X ↘ p))
    (Elb : Π⦃x y⦄ ⦃s : ℕ⦄, (deg (i X))⁻¹ᵉ^[s] x = y → B x ≤ s → is_contr (E X y))
    (deg_ik_commute : hsquare (deg (k X)) (deg (k X)) (deg (i X)) (deg (i X)))
    (deg_ij_commute : hsquare (deg (j X)) (deg (j X)) (deg (i X)) (deg (i X)))

/- Note: Elb proves Dlb for some bound B', but we want tight control over when B' = 0 -/
  definition is_bounded.mk [constructor] {R : Ring} {I : Set} {X : exact_couple R I}
    (B B' B'' : I → ℕ)
    (Dub : Π⦃x : I⦄ ⦃s : ℕ⦄, B x ≤ s → is_contr (D X ((deg (i X))^[s] x)))
    (Dlb : Π⦃x : I⦄ ⦃s : ℕ⦄, B' x ≤ s → is_surjective (i X (((deg (i X))⁻¹ᵉ^[s + 1] x))))
    (Elb : Π⦃x : I⦄ ⦃s : ℕ⦄, B'' x ≤ s → is_contr (E X ((deg (i X))⁻¹ᵉ^[s] x)))
    (deg_ik_commute : hsquare (deg (k X)) (deg (k X)) (deg (i X)) (deg (i X)))
    (deg_ij_commute : hsquare (deg (j X)) (deg (j X)) (deg (i X)) (deg (i X))) : is_bounded X :=
  begin
    apply is_bounded.mk' (λx, max (B x) (B'' x)) B',
    { intro x y s p h, induction p, exact Dub (le.trans !le_max_left h) },
    { intro x y z s p q h, induction p, induction q,
      refine transport (λx, is_surjective (i X x)) _ (Dlb h),
      rewrite [-iterate_succ], apply iterate_left_inv },
    { intro x y s p h, induction p, exact Elb (le.trans !le_max_right h) },
    { assumption },
    { assumption }
  end

  open is_bounded
  parameters {R : Ring} {I : Set} (X : exact_couple R I) (HH : is_bounded X)

  local abbreviation B := B HH
  local abbreviation B' := B' HH
  local abbreviation Dub := Dub HH
  local abbreviation Dlb := Dlb HH
  local abbreviation Elb := Elb HH
  local abbreviation deg_ik_commute := deg_ik_commute HH
  local abbreviation deg_ij_commute := deg_ij_commute HH

  definition deg_iterate_ik_commute (n : ℕ) :
    hsquare (deg (k X)) (deg (k X)) ((deg (i X))^[n]) ((deg (i X))^[n]) :=
  iterate_commute n deg_ik_commute

  definition deg_iterate_ij_commute (n : ℕ) :
    hsquare (deg (j X)) (deg (j X)) ((deg (i X))⁻¹ᵉ^[n]) ((deg (i X))⁻¹ᵉ^[n]) :=
  iterate_commute n (hvinverse deg_ij_commute)

  definition B2 (x : I) : ℕ := max (B (deg (k X) x)) (B ((deg (j X))⁻¹ x))
  definition Eub ⦃x y : I⦄ ⦃s : ℕ⦄ (p : (deg (i X))^[s] x = y) (h : B2 x ≤ s) :
    is_contr (E X y) :=
  begin
    induction p,
    refine @(is_contr_middle_of_is_exact (exact_couple.jk X (right_inv (deg (j X)) _) idp)) _ _ _,
    exact Dub (iterate_commute s (hhinverse deg_ij_commute) x) (le.trans !le_max_right h),
    exact Dub !deg_iterate_ik_commute (le.trans !le_max_left h)
  end

  -- we start counting pages at 0, not at 2.
  definition page (r : ℕ) : exact_couple R I :=
  iterate derived_couple r X

  definition is_contr_E (r : ℕ) (x : I) (h : is_contr (E X x)) :
    is_contr (E (page r) x) :=
  by induction r with r IH; exact h; exact is_contr_E' (page r) IH

  definition is_contr_D (r : ℕ) (x : I) (h : is_contr (D X x)) :
    is_contr (D (page r) x) :=
  by induction r with r IH; exact h; exact is_contr_D' (page r) IH

  definition deg_i (r : ℕ) : deg (i (page r)) ~ deg (i X) :=
  begin
    induction r with r IH,
    { reflexivity },
    { exact IH }
  end

  definition deg_k (r : ℕ) : deg (k (page r)) ~ deg (k X) :=
  begin
    induction r with r IH,
    { reflexivity },
    { exact IH }
  end

  definition deg_j (r : ℕ) :
    deg (j (page r)) ~ deg (j X) ∘ iterate (deg (i X))⁻¹ r :=
  begin
    induction r with r IH,
    { reflexivity },
    { refine hwhisker_left (deg (j (page r)))
        (to_inv_homotopy_inv (deg_i r)) ⬝hty _,
      refine hwhisker_right _ IH ⬝hty _,
      apply hwhisker_left, symmetry, apply iterate_succ }
  end

  definition deg_j_inv (r : ℕ) :
    (deg (j (page r)))⁻¹ ~ iterate (deg (i X)) r ∘ (deg (j X))⁻¹ :=
  have H : deg (j (page r)) ~ iterate_equiv (deg (i X))⁻¹ᵉ r ⬝e deg (j X), from deg_j r,
  λx, to_inv_homotopy_to_inv H x ⬝ iterate_inv (deg (i X))⁻¹ᵉ r ((deg (j X))⁻¹ x)

  definition deg_d (r : ℕ) :
    deg (d (page r)) ~ deg (j X) ∘ iterate (deg (i X))⁻¹ r ∘ deg (k X) :=
  compose2 (deg_j r) (deg_k r)

  definition deg_d_inv (r : ℕ) :
    (deg (d (page r)))⁻¹ ~ (deg (k X))⁻¹ ∘ iterate (deg (i X)) r ∘ (deg (j X))⁻¹ :=
  compose2 (to_inv_homotopy_to_inv (deg_k r)) (deg_j_inv r)

  definition B3 (x : I) : ℕ :=
  max (B (deg (j X) (deg (k X) x))) (B2 ((deg (k X))⁻¹ ((deg (j X))⁻¹ x)))

  definition Estable {x : I} {r : ℕ} (H : B3 x ≤ r) :
    E (page (r + 1)) x ≃lm E (page r) x :=
  begin
    change homology (d (page r) x) (d (page r) ← x) ≃lm E (page r) x,
    apply homology_isomorphism: apply is_contr_E,
    exact Eub (hhinverse (deg_iterate_ik_commute r) _ ⬝ (deg_d_inv r x)⁻¹)
              (le.trans !le_max_right H),
    exact Elb (deg_iterate_ij_commute r _ ⬝ (deg_d r x)⁻¹)
              (le.trans !le_max_left H)
  end

  definition is_surjective_i {x y z : I} {r s : ℕ} (H : B' z ≤ s + r)
    (p : deg (i (page r)) x = y) (q : iterate (deg (i X)) s y = z) :
    is_surjective (i (page r) ↘ p) :=
  begin
    revert x y z s H p q, induction r with r IH: intro x y z s H p q,
    { exact Dlb p q H },
-- the following is a start of the proof that i is surjective from the contractibility of E
      -- induction p, change is_surjective (i X x),
      -- apply @(is_surjective_of_is_exact_of_is_contr (exact_couple.ij X idp idp)),
      -- refine Elb _ H,
      -- exact sorry
    { change is_surjective (i' (page r) ↘ p),
      apply is_surjective_i', intro z' q',
      refine IH _ _ _ _ (le.trans H (le_of_eq (succ_add s r)⁻¹)) _ _,
      refine !iterate_succ ⬝ ap ((deg (i X))^[s]) _ ⬝ q,
      exact !deg_i⁻¹ ⬝ p }
  end

  definition Dstable {x : I} {r : ℕ} (H : B' x ≤ r) :
    D (page (r + 1)) x ≃lm D (page r) x :=
  begin
    change image_module (i (page r) ← x) ≃lm D (page r) x,
    refine image_module_isomorphism (i (page r) ← x)
      (is_surjective_i (le.trans H (le_of_eq !zero_add⁻¹)) _ _),
    reflexivity
  end

  definition Einf : graded_module R I :=
  λx, E (page (B3 x)) x

  definition Dinf : graded_module R I :=
  λx, D (page (B' x)) x

  definition Einfstable {x y : I} {r : ℕ} (Hr : B3 y ≤ r) (p : x = y) : Einf y ≃lm E (page r) x :=
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Estable Hr ⬝lm IH

  definition Dinfstable {x y : I} {r : ℕ} (Hr : B' y ≤ r) (p : x = y) : Dinf y ≃lm D (page r) x :=
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Dstable Hr ⬝lm IH

  parameters {x : I}

  definition r (n : ℕ) : ℕ :=
  max (max (B (deg (j X) (deg (k X) x)) + n + 1) (B3 ((deg (i X))^[n] x)))
      (max (B' (deg (k X) ((deg (i X))^[n] x)))
           (max (B' (deg (k X) ((deg (i X))^[n+1] x))) (B ((deg (j X))⁻¹ ((deg (i X))^[n] x)))))

  lemma rb0 (n : ℕ) : r n ≥ n + 1 :=
  ge.trans !le_max_left (ge.trans !le_max_left !le_add_left)
  lemma rb1 (n : ℕ) : B (deg (j X) (deg (k X) x)) ≤ r n - (n + 1) :=
  le_sub_of_add_le (le.trans !le_max_left !le_max_left)
  lemma rb2 (n : ℕ) : B3 ((deg (i X))^[n] x) ≤ r n :=
  le.trans !le_max_right !le_max_left
  lemma rb3 (n : ℕ) : B' (deg (k X) ((deg (i X))^[n] x)) ≤ r n :=
  le.trans !le_max_left !le_max_right
  lemma rb4 (n : ℕ) : B' (deg (k X) ((deg (i X))^[n+1] x)) ≤ r n :=
  le.trans (le.trans !le_max_left !le_max_right) !le_max_right
  lemma rb5 (n : ℕ) : B ((deg (j X))⁻¹ ((deg (i X))^[n] x)) ≤ r n :=
  le.trans (le.trans !le_max_right !le_max_right) !le_max_right

  definition Einfdiag : graded_module R ℕ :=
  λn, Einf ((deg (i X))^[n] x)

  definition Dinfdiag : graded_module R ℕ :=
  λn, Dinf (deg (k X) ((deg (i X))^[n] x))

  definition short_exact_mod_page_r (n : ℕ) : short_exact_mod
    (E (page (r n)) ((deg (i X))^[n] x))
    (D (page (r n)) (deg (k (page (r n))) ((deg (i X))^[n] x)))
    (D (page (r n)) (deg (i (page (r n))) (deg (k (page (r n))) ((deg (i X))^[n] x)))) :=
  begin
    fapply short_exact_mod_of_is_exact,
    { exact j (page (r n)) ← ((deg (i X))^[n] x) },
    { exact k (page (r n)) ((deg (i X))^[n] x) },
    { exact i (page (r n)) (deg (k (page (r n))) ((deg (i X))^[n] x)) },
    { exact j (page (r n)) _ },
    { apply is_contr_D, refine Dub !deg_j_inv⁻¹ (rb5 n) },
    { apply is_contr_E, refine Elb _ (rb1 n),
      refine !deg_iterate_ij_commute ⬝ _,
      refine ap (deg (j X)) _ ⬝ !deg_j⁻¹,
      refine iterate_sub _ !rb0 _ ⬝ _, apply ap (_^[r n]),
      exact ap (deg (i X)) (!deg_iterate_ik_commute ⬝ !deg_k⁻¹) ⬝ !deg_i⁻¹ },
    { apply jk (page (r n)) },
    { apply ki (page (r n)) },
    { apply ij (page (r n)) }
  end

  definition short_exact_mod_infpage (n : ℕ) :
    short_exact_mod (Einfdiag n) (Dinfdiag n) (Dinfdiag (n+1)) :=
  begin
    refine short_exact_mod_isomorphism _ _ _ (short_exact_mod_page_r n),
    { exact Einfstable !rb2 idp },
    { exact Dinfstable !rb3 !deg_k },
    { exact Dinfstable !rb4 (!deg_i ⬝ ap (deg (i X)) !deg_k ⬝ !deg_ik_commute) }
  end

  definition Dinfdiag0 (bound_zero : B' (deg (k X) x) = 0) : Dinfdiag 0 ≃lm D X (deg (k X) x) :=
  Dinfstable (le_of_eq bound_zero) idp

  definition Dinfdiag_stable {s : ℕ} (h : B (deg (k X) x) ≤ s) : is_contr (Dinfdiag s) :=
  is_contr_D _ _ (Dub !deg_iterate_ik_commute h)

  end


end left_module
open left_module
namespace pointed

  open pointed int group is_trunc trunc is_conn

  definition homotopy_group_conn_nat (n : ℕ) (A : Type*[1]) : AbGroup :=
  AbGroup.mk (π[n] A) (ab_group_homotopy_group_of_is_conn n A)

  definition homotopy_group_conn : Π(n : ℤ) (A : Type*[1]), AbGroup
  | (of_nat n) A := homotopy_group_conn_nat n A
  | (-[1+ n])  A := trivial_ab_group_lift

  notation `πag'[`:95 n:0 `]`:0 := homotopy_group_conn n

  definition homotopy_group_conn_nat_functor (n : ℕ) {A B : Type*[1]} (f : A →* B) :
    homotopy_group_conn_nat n A →g homotopy_group_conn_nat n B :=
  begin
    cases n with n, { apply homomorphism_of_is_contr_right },
    cases n with n, { apply homomorphism_of_is_contr_right },
    exact π→g[n+2] f
  end

  definition homotopy_group_conn_functor : Π(n : ℤ) {A B : Type*[1]} (f : A →* B), πag'[n] A →g πag'[n] B
  | (of_nat n) A B f := homotopy_group_conn_nat_functor n f
  | (-[1+ n])  A B f := homomorphism_of_is_contr_right _ _

  notation `π→ag'[`:95 n:0 `]`:0 := homotopy_group_conn_functor n

  section
  open prod prod.ops fiber
  parameters {A : ℤ → Type*[1]} (f : Π(n : ℤ), A n →* A (n - 1)) [Hf : Πn, is_conn_fun 1 (f n)]
  include Hf
  definition I [constructor] : Set := trunctype.mk (ℤ × ℤ) !is_trunc_prod

  definition D_sequence : graded_module rℤ I :=
  λv, LeftModule_int_of_AbGroup (πag'[v.2] (A (v.1)))

  definition E_sequence : graded_module rℤ I :=
  λv, LeftModule_int_of_AbGroup (πag'[v.2] (pconntype.mk (pfiber (f (v.1))) !Hf pt))

  -- definition exact_couple_sequence : exact_couple rℤ I :=
  -- exact_couple.mk D_sequence E_sequence sorry sorry sorry sorry sorry sorry

  end


end pointed

namespace spectrum
  open pointed int group is_trunc trunc is_conn prod prod.ops group fin chain_complex
  section

  parameters {A : ℤ → spectrum} (f : Π(s : ℤ), A s →ₛ A (s - 1))

  definition I [constructor] : Set := trunctype.mk (gℤ ×g gℤ) !is_trunc_prod

  definition D_sequence : graded_module rℤ I :=
  λv, LeftModule_int_of_AbGroup (πₛ[v.1] (A (v.2)))

  definition E_sequence : graded_module rℤ I :=
  λv, LeftModule_int_of_AbGroup (πₛ[v.1] (sfiber (f (v.2))))

  include f
  definition i_sequence : D_sequence →gm D_sequence :=
  begin
    fapply graded_hom.mk, exact (prod_equiv_prod erfl (add_right_action (- 1))),
    intro v,
    apply lm_hom_int.mk, esimp,
    exact πₛ→[v.1] (f v.2)
  end

  definition j_sequence : D_sequence →gm E_sequence :=
  begin
    fapply graded_hom.mk_out',
    exact (prod_equiv_prod (add_right_action 1) (add_right_action (- 1))),
    intro v, induction v with n s,
    apply lm_hom_int.mk, esimp,
    rexact shomotopy_groups_fun (f s) (n, 2)
  end

  definition k_sequence : E_sequence →gm D_sequence :=
  begin
    fapply graded_hom.mk erfl,
    intro v, induction v with n s,
    apply lm_hom_int.mk, esimp,
    exact πₛ→[n] (spoint (f s))
  end

  lemma ij_sequence : is_exact_gmod i_sequence j_sequence :=
  begin
    intro x y z p q,
    revert y z q p,
    refine eq.rec_right_inv (deg j_sequence) _,
    intro y, induction x with n s, induction y with m t,
    refine equiv_rect !pair_eq_pair_equiv⁻¹ᵉ _ _,
    intro pq, esimp at pq, induction pq with p q,
    revert t q, refine eq.rec_equiv (add_right_action (- 1)) _,
    induction p using eq.rec_symm,
    apply is_exact_homotopy homotopy.rfl,
    { symmetry, intro, apply graded_hom_mk_out'_left_inv },
    rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (m, 2)),
  end

  lemma jk_sequence : is_exact_gmod j_sequence k_sequence :=
  begin
    intro x y z p q, induction q,
    revert x y p, refine eq.rec_right_inv (deg j_sequence) _,
    intro x, induction x with n s,
    apply is_exact_homotopy,
    { symmetry, intro, apply graded_hom_mk_out'_left_inv },
    { reflexivity },
    rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (n, 1)),
  end

  lemma ki_sequence : is_exact_gmod k_sequence i_sequence :=
  begin
    intro i j k p q, induction p, induction q, induction i with n s,
    rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (n, 0)),
  end

  definition exact_couple_sequence [constructor] : exact_couple rℤ I :=
  exact_couple.mk D_sequence E_sequence i_sequence j_sequence k_sequence
                  ij_sequence jk_sequence ki_sequence

  open int
  parameters (ub : ℤ) (lb : ℤ → ℤ)
    (Aub : Πs n, s ≥ ub + 1 → is_equiv (f s n))
    (Alb : Πs n, s ≤ lb n → is_contr (πₛ[n] (A s)))

  definition B : I → ℕ
  | (n, s) := max0 (s - lb n)

  definition B' : I → ℕ
  | (n, s) := max0 (ub - s)

  definition B'' : I → ℕ
  | (n, s) := max0 (ub + 1 - s)

  lemma iterate_deg_i (n s : ℤ) (m : ℕ) : (deg i_sequence)^[m] (n, s) = (n, s - m) :=
  begin
    induction m with m IH,
    { exact prod_eq idp !sub_zero⁻¹ },
    { exact ap (deg i_sequence) IH ⬝ (prod_eq idp !sub_sub) }
  end

  lemma iterate_deg_i_inv (n s : ℤ) (m : ℕ) : (deg i_sequence)⁻¹ᵉ^[m] (n, s) = (n, s + m) :=
  begin
    induction m with m IH,
    { exact prod_eq idp !add_zero⁻¹ },
    { exact ap (deg i_sequence)⁻¹ᵉ IH ⬝ (prod_eq idp !add.assoc) }
  end

  include Aub Alb
  lemma Dub ⦃x : I⦄ ⦃t : ℕ⦄ (h : B x ≤ t) : is_contr (D_sequence ((deg i_sequence)^[t] x)) :=
  begin
    apply Alb, induction x with n s, rewrite [iterate_deg_i],
    apply sub_le_of_sub_le,
    exact le_of_max0_le h,
  end

  lemma Dlb ⦃x : I⦄ ⦃t : ℕ⦄ (h : B' x ≤ t) :
    is_surjective (i_sequence ((deg i_sequence)⁻¹ᵉ^[t+1] x)) :=
  begin
    apply is_surjective_of_is_equiv,
    apply is_equiv_homotopy_group_functor,
    apply Aub, induction x with n s,
    rewrite [iterate_deg_i_inv, ▸*, of_nat_add, -add.assoc],
    apply add_le_add_right,
    apply le_add_of_sub_left_le,
    exact le_of_max0_le h
  end

  lemma Elb ⦃x : I⦄ ⦃t : ℕ⦄ (h : B'' x ≤ t) : is_contr (E_sequence ((deg i_sequence)⁻¹ᵉ^[t] x)) :=
  begin
    apply is_contr_homotopy_group_of_is_contr,
    apply is_contr_fiber_of_is_equiv,
    apply Aub, induction x with n s,
    rewrite [iterate_deg_i_inv, ▸*],
    apply le_add_of_sub_left_le,
    apply le_of_max0_le h,
  end

  definition is_bounded_sequence [constructor] : is_bounded exact_couple_sequence :=
  is_bounded.mk B B' B'' Dub Dlb Elb
    (by intro x; reflexivity)
    begin
      intro x, induction x with n s, apply pair_eq, esimp, esimp, esimp [j_sequence, i_sequence],
      refine !add.assoc ⬝ ap (add s) !add.comm ⬝ !add.assoc⁻¹,
    end

  end

end spectrum
