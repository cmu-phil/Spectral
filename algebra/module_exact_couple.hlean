/- Exact couples of graded (left-) R-modules. -/

-- Author: Floris van Doorn

import .graded ..homotopy.spectrum .product_group

open algebra is_trunc left_module is_equiv equiv eq function nat

-- move
section
  open group int chain_complex pointed succ_str
  definition LeftModule_int_of_AbGroup [constructor] (A : AbGroup) : LeftModule rℤ :=
  LeftModule.mk A (left_module.mk sorry sorry sorry sorry 1 sorry sorry sorry sorry sorry sorry sorry sorry sorry)

  definition lm_hom_int.mk [constructor] {A B : AbGroup} (φ : A →g B) :
    LeftModule_int_of_AbGroup A →lm LeftModule_int_of_AbGroup B :=
 homomorphism.mk φ sorry

  definition is_exact_of_is_exact_at {N : succ_str} {A : chain_complex N} {n : N}
    (H : is_exact_at A n) : is_exact (cc_to_fn A (S n)) (cc_to_fn A n) :=
  is_exact.mk (cc_is_chain_complex A n) H

end
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

  parameters {R : Ring} {I : Set} (X : exact_couple R I) (B B' : I → ℕ)
    (Dub : Π⦃x y⦄ ⦃s : ℕ⦄, (deg (i X))^[s] x = y → B x ≤ s → is_contr (D X y))
    (Eub : Π⦃x y⦄ ⦃s : ℕ⦄, (deg (k X))⁻¹ (iterate (deg (i X)) s ((deg (j X))⁻¹ x)) = y →
           B x ≤ s → is_contr (E X y))
    (Dlb : Π⦃x y z⦄ ⦃s : ℕ⦄ (p : deg (i X) x = y),
    iterate (deg (i X)) s y = z → B' z ≤ s → is_surjective (i X ↘ p))
    (Elb : Π⦃x y⦄ ⦃s : ℕ⦄, deg (j X) (iterate (deg (i X))⁻¹ᵉ s (deg (k X) x)) = y → B x ≤ s →
           is_contr (E X y))
    (deg_ik_commute : deg (i X) ∘ deg (k X) ~ deg (k X) ∘ deg (i X))

  definition deg_iterate_ik_commute (n : ℕ) (x : I) :
    (deg (i X))^[n] (deg (k X) x) = deg (k X) ((deg (i X))^[n] x) :=
  iterate_commute _ deg_ik_commute x

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

  include Elb Eub
  definition Estable {x : I} {r : ℕ} (H : B x ≤ r) :
    E (page (r + 1)) x ≃lm E (page r) x :=
  begin
    change homology (d (page r) x) (d (page r) ← x) ≃lm E (page r) x,
    apply homology_isomorphism: apply is_contr_E,
    exact Eub (deg_d_inv r x)⁻¹ H, exact Elb (deg_d r x)⁻¹ H
  end

  include Dlb
  definition is_surjective_i {x y z : I} {r s : ℕ} (H : B' z ≤ s + r)
    (p : deg (i (page r)) x = y) (q : iterate (deg (i X)) s y = z) :
    is_surjective (i (page r) ↘ p) :=
  begin
    revert x y z s H p q, induction r with r IH: intro x y z s H p q,
    { exact Dlb p q H  },
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
  λx, E (page (B x)) x

  definition Dinf : graded_module R I :=
  λx, D (page (B' x)) x

  definition Einfstable {x y : I} {r : ℕ} (Hr : B y ≤ r) (p : x = y) :
    Einf y ≃lm E (page r) x :=
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Estable Hr ⬝lm IH

  definition Dinfstable {x y : I} {r : ℕ} (Hr : B' y ≤ r) (p : x = y) :
    Dinf y ≃lm D (page r) x :=
  by symmetry; induction p; induction Hr with r Hr IH; reflexivity; exact Dstable Hr ⬝lm IH

  parameters {x : I}

  definition r (n : ℕ) : ℕ :=
  max (max (B x + n + 1) (B ((deg (i X))^[n] x)))
      (max (B' (deg (k X) ((deg (i X))^[n] x)))
           (max (B' (deg (k X) ((deg (i X))^[n+1] x))) (B ((deg (j X))⁻¹ ((deg (i X))^[n] x)))))

  lemma rb0 (n : ℕ) : r n ≥ n + 1 :=
  ge.trans !le_max_left (ge.trans !le_max_left !le_add_left)
  lemma rb1 (n : ℕ) : B x ≤ r n - (n + 1) :=
  le_sub_of_add_le (le.trans !le_max_left !le_max_left)
  lemma rb2 (n : ℕ) : B ((deg (i X))^[n] x) ≤ r n :=
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

  include deg_ik_commute Dub
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
  -- move
  open pointed int group is_trunc trunc is_conn

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

  definition ab_group_homotopy_group_of_is_conn (n : ℕ) (A : Type*) [H : is_conn 1 A] : ab_group (π[n] A) :=
  begin
    have is_conn 0 A, from !is_conn_of_is_conn_succ,
    cases n with n,
    { unfold [homotopy_group, ptrunc], apply ab_group_of_is_contr },
    cases n with n,
    { unfold [homotopy_group, ptrunc], apply ab_group_of_is_contr },
    exact ab_group_homotopy_group n A
  end

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

  definition exact_couple_sequence : exact_couple rℤ I :=
  exact_couple.mk D_sequence E_sequence sorry sorry sorry sorry sorry sorry

  end


end pointed

namespace spectrum
  open pointed int group is_trunc trunc is_conn prod prod.ops group fin chain_complex
  section
--  notation `πₛ→[`:95 n:0 `]`:0 := shomotopy_group_fun n

  definition is_equiv_mul_right [constructor] {A : Group} (a : A) : is_equiv (λb, b * a) :=
  adjointify _ (λb : A, b * a⁻¹) (λb, !inv_mul_cancel_right) (λb, !mul_inv_cancel_right)

  definition right_action [constructor] {A : Group} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_mul_right a)

  definition is_equiv_add_right [constructor] {A : AddGroup} (a : A) : is_equiv (λb, b + a) :=
  adjointify _ (λb : A, b - a) (λb, !neg_add_cancel_right) (λb, !add_neg_cancel_right)

  definition add_right_action [constructor] {A : AddGroup} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_add_right a)

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
    intro v, induction v with n s,
    apply lm_hom_int.mk, esimp,
    -- exact homomorphism.mk _ (is_mul_hom_LES_of_shomotopy_groups (f s) (n, 0)),
--    exact shomotopy_groups_fun (f s) (n, 0)
    exact πₛ→[n] (f s)
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
    -- exact homomorphism.mk _ (is_mul_hom_LES_of_shomotopy_groups (f s) (n, 1)),
    -- exact shomotopy_groups_fun (f s) (n, 1)
    exact πₛ→[n] (spoint (f s))
  end

  lemma ij_sequence : is_exact_gmod i_sequence j_sequence :=
  begin
    intro i, induction i with n s,
    revert n, refine equiv_rect (add_right_action 1) _ _, intro n,
    esimp, intro j k p, unfold [i_sequence] at p,
    -- induction p,
    intro q, unfold [j_sequence] at q,
    note qq := left_inv (deg j_sequence) (n, s),
    unfold [j_sequence] at qq,
    revert k q,
    --refine eq.rec_to2 qq _ _
    --intro i j k p q,

--    revert k q,
  end

  lemma jk_sequence : is_exact_gmod j_sequence k_sequence :=
  sorry

local attribute i_sequence [reducible]
  lemma ki_sequence : is_exact_gmod k_sequence i_sequence :=
  begin
--    unfold [is_exact_gmod, is_exact_mod],
    intro i j k p q, induction p, induction q, induction i with n s,
    rexact is_exact_of_is_exact_at (is_exact_LES_of_shomotopy_groups (f s) (n, 0)),
  end


  definition exact_couple_sequence : exact_couple rℤ I :=
  exact_couple.mk D_sequence E_sequence i_sequence j_sequence k_sequence ij_sequence jk_sequence ki_sequence

  end




end spectrum
