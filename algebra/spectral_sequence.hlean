/- Exact couples of graded (left-) R-modules. This file includes:
  - Constructing exact couples from sequences of maps
  - Deriving an exact couple
  - The convergence theorem for exact couples -/

-- Author: Floris van Doorn

import .graded ..spectrum.basic .product_group

open algebra is_trunc left_module is_equiv equiv eq function nat sigma sigma.ops set_quotient

/- exact couples -/

namespace left_module

  structure exact_couple (R : Ring) (I : Set) : Type :=
    (D E : graded_module R I)
    (i : D →gm D) (j : D →gm E) (k : E →gm D)
    (ij : is_exact_gmod i j)
    (jk : is_exact_gmod j k)
    (ki : is_exact_gmod k i)

  open exact_couple

  namespace derived_couple
  section

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
  graded_image_lift i ∘gm  graded_submodule_incl (λx, image (i ← x))

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
    (graded_homology_intro _ _ ∘gm graded_hom_lift _ j j_lemma1) x m = 0 :> E' _ :=
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
    exact @quotient_map_eq_zero _ _ _ _ _ (this p)
  end

  definition j' : D' →gm E' :=
  graded_image_elim (graded_homology_intro d d ∘gm graded_hom_lift _ j j_lemma1) j_lemma2
  -- degree deg j - deg i

  lemma k_lemma1 ⦃x : I⦄ (m : E x) (p : d x m = 0) : image (i ← (deg k x)) (k x m) :=
  gmod_ker_in_im (exact_couple.ij X) (k x m) p

  definition k₂ : graded_kernel d →gm D' := graded_submodule_functor k k_lemma1

  lemma k_lemma2 ⦃x : I⦄ (m : E x) (h₁ : lm_kernel (d x) m) (h₂ : image (d ← x) m) :
    k₂ x ⟨m, h₁⟩ = 0 :=
  begin
    assert H₁ : Π⦃x' y z w : I⦄ (p : deg k x' = y) (q : deg j y = z) (r : deg k z = w) (n : E x'),
      k ↘ r (j ↘ q (k ↘ p n)) = 0,
    { intros, exact gmod_im_in_ker (exact_couple.jk X) q r (k ↘ p n) },
    induction h₂ with n p,
    assert H₂ : k x m = 0,
    { rewrite [-p], refine ap (k x) (graded_hom_compose_fn_out j k x n) ⬝ _, apply H₁ },
    exact subtype_eq H₂
  end

  definition k' : E' →gm D' :=
  @graded_quotient_elim _ _ _ _ _ _ (graded_submodule_functor k k_lemma1)
                       (by intro x m h; cases m with [m1, m2]; exact k_lemma2 m1 m2 h)

  definition i'_eq ⦃x : I⦄ (m : D x) (h : image (i ← x) m) : (i' x ⟨m, h⟩).1 = i x m :=
  by reflexivity

  definition k'_eq ⦃x : I⦄ (m : E x) (h : d x m = 0) : (k' x (class_of ⟨m, h⟩)).1 = k x m :=
  by reflexivity

  lemma j'_eq {x : I} (m : D x) : j' ↘ (ap (deg j) (left_inv (deg i) x)) (graded_image_lift i x m) =
    class_of (graded_hom_lift _ j proof j_lemma1 qed x m) :=
  begin
    refine graded_image_elim_destruct _ _ _ idp _ m,
    apply is_set.elim,
  end

  definition deg_i' : deg i' ~ deg i := by reflexivity
  definition deg_j' : deg j' ~ deg j ∘ (deg i)⁻¹ := by reflexivity
  definition deg_k' : deg k' ~ deg k := by reflexivity

  open group
  set_option pp.coercions true
  lemma i'j' : is_exact_gmod i' j' :=
  begin
    intro x, refine equiv_rect (deg i) _ _,
    intros y z p q, revert z q x p,
    refine eq.rec_grading (deg i ⬝e deg j') (deg j) (ap (deg j) (left_inv (deg i) y)) _,
    intro x, revert y, refine eq.rec_equiv (deg i) _,
    apply transport (λx, is_exact_mod x _) (idpath (i' x)),
    apply transport (λx, is_exact_mod _ (j' ↘ (ap (deg j) (left_inv (deg i) x)))) (idpath x),
    apply is_exact_mod.mk,
    { revert x, refine equiv_rect (deg i) _ _, intro x,
      refine graded_image.rec _, intro m,
      transitivity j' ↘ _ (graded_image_lift i (deg i x) (i x m)),
        apply ap (λx, j' ↘ _ x), apply subtype_eq, apply i'_eq,
      refine !j'_eq ⬝ _,
      apply ap class_of, apply subtype_eq, exact is_exact.im_in_ker (exact_couple.ij X idp idp) m },
    { revert x, refine equiv_rect (deg k) _ _, intro x,
      refine graded_image.rec _, intro m p,
      assert q : graded_homology_intro d d (deg j (deg k x))
                   (graded_hom_lift _ j j_lemma1 (deg k x) m) = 0,
      { exact !j'_eq⁻¹ ⬝ p },
      note q2 := image_of_graded_homology_intro_eq_zero idp (graded_hom_lift _ j _ _ m) q,
      induction q2 with n r,
      assert s : j (deg k x) (m - k x n) = 0,
      { refine respect_sub (j (deg k x)) m (k x n) ⬝ _,
        refine ap (sub _) r ⬝ _, apply sub_self },
      assert t : trunctype.carrier (image (i ← (deg k x)) (m - k x n)),
      { exact is_exact.ker_in_im (exact_couple.ij X _ _) _ s },
      refine image.mk ⟨m - k x n, t⟩ _,
      apply subtype_eq, refine !i'_eq ⬝ !to_respect_sub ⬝ _,
      refine ap (@sub (D (deg i (deg k x))) _ _) _ ⬝ @sub_zero _ _ _,
      apply is_exact.im_in_ker (exact_couple.ki X _ _) }
  end

  lemma j'k' : is_exact_gmod j' k' :=
  begin
    refine equiv_rect (deg i) _ _,
    intros x y z p, revert y p z,
    refine eq.rec_grading (deg i ⬝e deg j') (deg j) (ap (deg j) (left_inv (deg i) x)) _,
    intro z q, induction q,
    apply is_exact_mod.mk,
    { refine graded_image.rec _, intro m,
      refine ap (k' _) (j'_eq m) ⬝ _,
      apply subtype_eq,
      refine k'_eq _ _ ⬝ _,
      exact is_exact.im_in_ker (exact_couple.jk X idp idp) m },
    { intro m p, induction m using set_quotient.rec_prop with m,
      induction m with m h, note q := (k'_eq m h)⁻¹ ⬝ ap pr1 p,
      induction is_exact.ker_in_im (exact_couple.jk X idp idp) m q with n r,
      apply image.mk (graded_image_lift i x n),
      refine !j'_eq ⬝ _,
      apply ap class_of, apply subtype_eq, exact r }
  end

  lemma k'i' : is_exact_gmod k' i' :=
  begin
    apply is_exact_gmod.mk,
    { intro x m, induction m using set_quotient.rec_prop with m,
      cases m with m p, apply subtype_eq,
      change i (deg k x) (k x m) = 0,
      exact is_exact.im_in_ker (exact_couple.ki X idp idp) m },
    { intro x m, induction m with m h, intro p,
      have i (deg k x) m = 0, from ap pr1 p,
      induction is_exact.ker_in_im (exact_couple.ki X idp idp) m this with n q,
      have j (deg k x) m = 0, from @(is_exact.im_in_ker2 (exact_couple.ij X _ _)) m h,
      have d x n = 0, from ap (j (deg k x)) q ⬝ this,
      exact image.mk (class_of ⟨n, this⟩) (subtype_eq q) }
  end

  end
  end derived_couple

  open derived_couple

  definition derived_couple [constructor] {R : Ring} {I : Set}
    (X : exact_couple R I) : exact_couple R I :=
  ⦃exact_couple, D := D' X, E := E' X, i := i' X, j := j' X, k := k' X,
    ij := i'j' X, jk := j'k' X, ki := k'i' X⦄

  /- if an exact couple is bounded, we can prove the convergence theorem for it -/
  structure is_bounded {R : Ring} {I : Set} (X : exact_couple R I) : Type :=
  mk' :: (B B' : I → ℕ)
    (Dub : Π⦃x y⦄ ⦃s : ℕ⦄, (deg (i X))^[s] x = y → B x ≤ s → is_contr (D X y))
    (Dlb : Π⦃x y z⦄ ⦃s : ℕ⦄ (p : deg (i X) x = y), (deg (i X))^[s] y = z → B' z ≤ s → is_surjective (i X ↘ p))
    (Elb : Π⦃x y⦄ ⦃s : ℕ⦄, (deg (i X))⁻¹ᵉ^[s] x = y → B x ≤ s → is_contr (E X y))
    (deg_ik_commute : hsquare (deg (k X)) (deg (k X)) (deg (i X)) (deg (i X)))
    (deg_ij_commute : hsquare (deg (j X)) (deg (j X)) (deg (i X)) (deg (i X)))

/- Note: Elb proves Dlb for some bound B', but we want tight control over when B' = 0 -/
  protected definition is_bounded.mk [constructor] {R : Ring} {I : Set} {X : exact_couple R I}
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

  namespace convergence_theorem
  section

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

  -- we start counting pages at 0
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
  λx, to_inv_homotopy_inv H x ⬝ iterate_inv (deg (i X))⁻¹ᵉ r ((deg (j X))⁻¹ x)

  definition deg_d (r : ℕ) :
    deg (d (page r)) ~ deg (j X) ∘ iterate (deg (i X))⁻¹ r ∘ deg (k X) :=
  compose2 (deg_j r) (deg_k r)

  definition deg_d_inv (r : ℕ) :
    (deg (d (page r)))⁻¹ ~ (deg (k X))⁻¹ ∘ iterate (deg (i X)) r ∘ (deg (j X))⁻¹ :=
  compose2 (to_inv_homotopy_inv (deg_k r)) (deg_j_inv r)

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
/- the following is a start of the proof that i is surjective using that E is contractible (but this
   makes the bound 1 higher than necessary -/
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

  /- the infinity pages of E and D -/
  definition Einf : graded_module R I :=
  λx, E (page (B3 x)) x

  definition Dinf : graded_module R I :=
  λx, D (page (B' x)) x

  definition Einfstable {x y : I} {r : ℕ} (Hr : B3 y ≤ r) (p : x = y) : Einf y ≃lm E (page r) x :=
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Estable Hr ⬝lm IH

  definition Dinfstable {x y : I} {r : ℕ} (Hr : B' y ≤ r) (p : x = y) : Dinf y ≃lm D (page r) x :=
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Dstable Hr ⬝lm IH

  parameters (x : I)

  definition r (n : ℕ) : ℕ :=
  max (max (B (deg (j X) (deg (k X) x)) + n + 1) (B3 ((deg (i X))^[n] x)))
      (max (B' (deg (k X) ((deg (i X))^[n] x)))
           (max (B' (deg (k X) ((deg (i X))^[n+1] x))) (B ((deg (j X))⁻¹ ((deg (i X))^[n] x)))))

  lemma rb0 (n : ℕ) : r n ≥ n + 1 :=
  ge.trans !le_max_left (ge.trans !le_max_left !le_add_left)
  lemma rb1 (n : ℕ) : B (deg (j X) (deg (k X) x)) ≤ r n - (n + 1) :=
  nat.le_sub_of_add_le (le.trans !le_max_left !le_max_left)
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

  /- the convergence theorem is a combination of the following three results -/
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

  lemma Dinfdiag_stable {s : ℕ} (h : B (deg (k X) x) ≤ s) : is_contr (Dinfdiag s) :=
  is_contr_D _ _ (Dub !deg_iterate_ik_commute h)

  /- some useful immediate properties -/

  definition short_exact_mod_infpage0 (bound_zero : B' (deg (k X) x) = 0) :
    short_exact_mod (Einfdiag 0) (D X (deg (k X) x)) (Dinfdiag 1) :=
  begin
    refine short_exact_mod_isomorphism _ _ _ (short_exact_mod_infpage 0),
    { reflexivity },
    { exact (Dinfdiag0 bound_zero)⁻¹ˡᵐ },
    { reflexivity }
  end

  end
  end convergence_theorem

  -- open convergence_theorem
  -- print axioms short_exact_mod_infpage
  -- print axioms Dinfdiag0
  -- print axioms Dinfdiag_stable

  open int group prod convergence_theorem prod.ops

  definition Z2 [constructor] : Set := gℤ ×g gℤ

  structure converges_to.{u v w} {R : Ring} (E' : gℤ → gℤ → LeftModule.{u v} R)
                                 (Dinf : gℤ → LeftModule.{u w} R) : Type.{max u (v+1) (w+1)} :=
    (X : exact_couple.{u 0 v w} R Z2)
    (HH : is_bounded X)
    (s₀ : gℤ → gℤ)
    (p : Π(n : gℤ), is_bounded.B' HH (deg (k X) (n, s₀ n)) = 0)
    (e : Π(x : gℤ ×g gℤ), exact_couple.E X x ≃lm E' x.1 x.2)
    (f : Π(n : gℤ), exact_couple.D X (deg (k X) (n, s₀ n)) ≃lm Dinf n)

  infix ` ⟹ `:25 := converges_to

  definition converges_to_g [reducible] (E' : gℤ → gℤ → AbGroup) (Dinf : gℤ → AbGroup) : Type :=
  (λn s, LeftModule_int_of_AbGroup (E' n s)) ⟹ (λn, LeftModule_int_of_AbGroup (Dinf n))

  infix ` ⟹ᵍ `:25 := converges_to_g

  section
  open converges_to
  parameters {R : Ring} {E' : gℤ → gℤ → LeftModule R} {Dinf : gℤ → LeftModule R} (c : E' ⟹ Dinf)
  local abbreviation X := X c
  local abbreviation i := i X
  local abbreviation HH := HH c
  local abbreviation s₀ := s₀ c
  local abbreviation Dinfdiag (n : gℤ) (k : ℕ) := Dinfdiag X HH (n, s₀ n) k
  local abbreviation Einfdiag (n : gℤ) (k : ℕ) := Einfdiag X HH (n, s₀ n) k

  definition converges_to_isomorphism {E'' : gℤ → gℤ → LeftModule R} {Dinf' : graded_module R gℤ}
    (e' : Πn s, E' n s ≃lm E'' n s) (f' : Πn, Dinf n ≃lm Dinf' n) : E'' ⟹ Dinf' :=
  converges_to.mk X HH s₀ (p c)
    begin intro x, induction x with n s, exact e c (n, s) ⬝lm e' n s end
    (λn, f c n ⬝lm f' n)

  theorem is_contr_converges_to_precise (n : gℤ)
  (H : Π(n : gℤ) (l : ℕ), is_contr (E' ((deg i)^[l] (n, s₀ n)).1 ((deg i)^[l] (n, s₀ n)).2)) :
    is_contr (Dinf n) :=
  begin
    assert H2 : Π(l : ℕ), is_contr (Einfdiag n l),
    { intro l, apply is_contr_E,
      refine @(is_trunc_equiv_closed_rev -2 (equiv_of_isomorphism (e c _))) (H n l) },
    assert H3 : is_contr (Dinfdiag n 0),
    { fapply nat.rec_down (λk, is_contr (Dinfdiag n k)),
      { exact is_bounded.B HH (deg (k X) (n, s₀ n)) },
      { apply Dinfdiag_stable, reflexivity },
      { intro l H,
        exact is_contr_middle_of_short_exact_mod (short_exact_mod_infpage X HH (n, s₀ n) l)
                (H2 l) H }},
    refine @is_trunc_equiv_closed _ _ _ _ H3,
    exact equiv_of_isomorphism (Dinfdiag0 X HH (n, s₀ n) (p c n) ⬝lm f c n)
  end

  theorem is_contr_converges_to (n : gℤ) (H : Π(n s : gℤ), is_contr (E' n s)) : is_contr (Dinf n) :=
  is_contr_converges_to_precise n (λn s, !H)

  end

  variables {E' : gℤ → gℤ → AbGroup} {Dinf : gℤ → AbGroup} (c : E' ⟹ᵍ Dinf)
  definition converges_to_g_isomorphism {E'' : gℤ → gℤ → AbGroup} {Dinf' : gℤ → AbGroup}
    (e' : Πn s, E' n s ≃g E'' n s) (f' : Πn, Dinf n ≃g Dinf' n) : E'' ⟹ᵍ Dinf' :=
  converges_to_isomorphism c (λn s, lm_iso_int.mk (e' n s)) (λn, lm_iso_int.mk (f' n))


end left_module
open left_module
namespace pointed

  open pointed int group is_trunc trunc is_conn

  definition homotopy_group_conn_nat (n : ℕ) (A : Type*[1]) : AbGroup :=
  AbGroup.mk (π[n] A) (ab_group_homotopy_group_of_is_conn n A)

  definition homotopy_group_conn : Π(n : ℤ) (A : Type*[1]), AbGroup
  | (of_nat n) A := homotopy_group_conn_nat n A
  | (-[1+ n])  A := trivial_ab_group_lift

  notation `πc[`:95 n:0 `]`:0 := homotopy_group_conn n

  definition homotopy_group_conn_nat_functor (n : ℕ) {A B : Type*[1]} (f : A →* B) :
    homotopy_group_conn_nat n A →g homotopy_group_conn_nat n B :=
  begin
    cases n with n, { apply trivial_homomorphism },
    cases n with n, { apply trivial_homomorphism },
    exact π→g[n+2] f
  end

  definition homotopy_group_conn_functor :
    Π(n : ℤ) {A B : Type*[1]} (f : A →* B), πc[n] A →g πc[n] B
  | (of_nat n) A B f := homotopy_group_conn_nat_functor n f
  | (-[1+ n])  A B f := trivial_homomorphism _ _

  notation `π→c[`:95 n:0 `]`:0 := homotopy_group_conn_functor n

  section
  open prod prod.ops fiber
  parameters {A : ℤ → Type*[1]} (f : Π(n : ℤ), A n →* A (n - 1)) [Hf : Πn, is_conn_fun 1 (f n)]
  include Hf
  local abbreviation I [constructor] := Z2

  -- definition D_sequence : graded_module rℤ I :=
  -- λv, LeftModule_int_of_AbGroup (πc[v.2] (A (v.1)))

  -- definition E_sequence : graded_module rℤ I :=
  -- λv, LeftModule_int_of_AbGroup (πc[v.2] (pconntype.mk (pfiber (f (v.1))) !Hf pt))

  /- first need LES of these connected homotopy groups -/

  -- definition exact_couple_sequence : exact_couple rℤ I :=
  -- exact_couple.mk D_sequence E_sequence sorry sorry sorry sorry sorry sorry

  end


end pointed

namespace spectrum
  open pointed int group is_trunc trunc is_conn prod prod.ops group fin chain_complex
  section

  parameters {A : ℤ → spectrum} (f : Π(s : ℤ), A s →ₛ A (s - 1))

--  protected definition I [constructor] : Set := gℤ ×g gℤ
  local abbreviation I [constructor] := Z2

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

  definition deg_j_seq_inv [constructor] : I ≃ I :=
  prod_equiv_prod (add_right_action 1) (add_right_action (- 1))

  definition fn_j_sequence [unfold 3] (x : I) :
    D_sequence (deg_j_seq_inv x) →lm E_sequence x :=
  begin
    induction x with n s,
    apply lm_hom_int.mk, esimp,
    rexact shomotopy_groups_fun (f s) (n, 2)
  end

  definition j_sequence : D_sequence →gm E_sequence :=
  graded_hom.mk_out deg_j_seq_inv⁻¹ᵉ fn_j_sequence

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
    { symmetry, exact graded_hom_mk_out_destruct deg_j_seq_inv⁻¹ᵉ fn_j_sequence },
    rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (m, 2)),
  end

  lemma jk_sequence : is_exact_gmod j_sequence k_sequence :=
  begin
    intro x y z p q, induction q,
    revert x y p, refine eq.rec_right_inv (deg j_sequence) _,
    intro x, induction x with n s,
    apply is_exact_homotopy,
    { symmetry, exact graded_hom_mk_out_destruct deg_j_seq_inv⁻¹ᵉ fn_j_sequence },
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
    (Aub : Π(s n : ℤ), s ≥ ub + 1 → is_equiv (f s n))
    (Alb : Π(s n : ℤ), s ≤ lb n → is_contr (πₛ[n] (A s)))

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

  definition converges_to_sequence : (λn s, πₛ[n] (sfiber (f s))) ⟹ᵍ (λn, πₛ[n] (A ub)) :=
  begin
    fapply converges_to.mk,
    { exact exact_couple_sequence },
    { exact is_bounded_sequence },
    { intro n, exact ub },
    { intro n, change max0 (ub - ub) = 0, exact ap max0 (sub_self ub) },
    { intro ns, reflexivity },
    { intro n, reflexivity }
  end

  end

-- Uncomment the next line to see that the proof uses univalence, but that there are no holes
--('sorry') in the proof:

-- print axioms is_bounded_sequence

-- I think it depends on univalence in an essential way. The reason is that the long exact sequence
-- of homotopy groups already depends on univalence. Namely, in that proof we need to show that if f
-- : A → B and g : B → C are exact at B, then ∥A∥₀ → ∥B∥₀ → ∥C∥₀ is exact at ∥B∥₀. For this we need
-- that the equality |b|₀ = |b'|₀ is equivalent to ∥b = b'∥₋₁, which requires univalence.
end spectrum
