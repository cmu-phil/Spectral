/-
Copyright (c) 2015 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Basic concepts of group theory
-/

import algebra.group_theory ..move_to_lib

open eq algebra is_trunc sigma sigma.ops prod trunc

namespace group

  /- #Subgroups -/
  /-- Recall that a subtype of a type A is the same thing as a family of mere propositions over A. Thus, we define a subgroup of a group G to be a family of mere propositions over (the underlying type of) G, closed under the constants and operations --/

  /-- Question: Why is this called subgroup_rel. Because it is a unary relation? --/
  structure subgroup_rel (G : Group) : Type :=
    (R : G → Prop)
    (Rone : R one)
    (Rmul : Π{g h}, R g → R h → R (g * h))
    (Rinv : Π{g}, R g → R (g⁻¹))

  attribute subgroup_rel.R [coercion]

  /-- Every group G has at least two subgroups, the trivial subgroup containing only one, and the full subgroup. --/
  definition trivial_subgroup.{u} (G : Group.{u}) : subgroup_rel.{u u} G :=
  begin
    fapply subgroup_rel.mk,
    { intro g, fapply trunctype.mk, exact (g = one), exact _ },
    { esimp },
    { intros g h p q, esimp at *, rewrite p, rewrite q, exact mul_one one},
    { intros g p, esimp at *, rewrite p, exact one_inv }
  end

  definition is_trivial_subgroup (G : Group) (R : subgroup_rel G) : Type :=
  (Π g : G, R g → g = 1)

  definition full_subgroup.{u} (G : Group.{u}) : subgroup_rel.{u 0} G :=
  begin
    fapply subgroup_rel.mk,
    { intro g, fapply trunctype.mk, exact unit, exact _ },
    { esimp, constructor },
    { intros g h p q, esimp, constructor },
    { intros g p, esimp, constructor }
  end

  definition is_full_subgroup (G : Group) (R : subgroup_rel G) : Prop :=
  trunctype.mk' -1 (Π g : G, R g)

  /-- Every group homomorphism f : G -> H determines a subgroup of H, the image of f, and a subgroup of G, the kernel of f. In the following definition we define the image of f. Since a subgroup is required to be closed under the group operations, showing that the image of f is closed under the group operations is part of the definition of the image of f. --/

  /-- TODO. We need to find some reasonable way of dealing with universe levels. The reason why it currently is what it is, is because lean is inflexible with universe leves once tactic mode is started --/
  definition image_subgroup.{u1 u2} {G : Group.{u1}} {H : Group.{u2}} (f : G →g H) : subgroup_rel.{u2 (max u1 u2)} H :=
    begin
      fapply subgroup_rel.mk,
        -- definition of the subset
      { intro h, apply ttrunc, exact fiber f h},
        -- subset contains 1
      { apply trunc.tr, fapply fiber.mk, exact 1, apply respect_one},
        -- subset is closed under multiplication
      { intro h h', intro u v,
        induction u with p, induction v with q,
        induction p with x p, induction q with y q,
        induction p, induction q,
        apply tr, apply fiber.mk (x * y), apply respect_mul},
        -- subset is closed under inverses
      { intro g, intro t, induction t, induction a with x p, induction p,
        apply tr, apply fiber.mk x⁻¹, apply respect_inv }
    end

  section kernels

  variables {G₁ G₂ : Group}

  -- TODO: maybe define this in more generality for pointed sets?
  definition kernel_pred [constructor] (φ : G₁ →g G₂) (g : G₁) : Prop := trunctype.mk (φ g = 1) _

  theorem kernel_mul (φ : G₁ →g G₂) (g h : G₁) (H₁ : kernel_pred φ g) (H₂ : kernel_pred φ h) : kernel_pred φ (g *[G₁] h) :=
  begin
    esimp at *,
    exact calc
      φ (g * h) = (φ g) * (φ h) : to_respect_mul
            ... = 1 * (φ h)     : H₁
            ... = 1 * 1         : H₂
            ... = 1             : one_mul
  end

  theorem kernel_inv (φ : G₁ →g G₂) (g : G₁) (H : kernel_pred φ g) : kernel_pred φ (g⁻¹) :=
  begin
    esimp at *,
    exact calc
      φ g⁻¹ = (φ g)⁻¹ : to_respect_inv
        ... = 1⁻¹     : H
        ... = 1       : one_inv
  end

  definition kernel_subgroup [constructor] (φ : G₁ →g G₂) : subgroup_rel G₁ :=
  ⦃ subgroup_rel,
    R := kernel_pred φ,
    Rone := respect_one φ,
    Rmul := kernel_mul φ,
    Rinv := kernel_inv φ
  ⦄

  end kernels

  /-- Now we should be able to show that if f is a homomorphism for which the kernel is trivial and the image is full, then f is an isomorphism, except that no one defined the proposition that f is an isomorphism :/ --/
  -- definition is_iso_from_kertriv_imfull {G H : Group} (f : G →g H) : is_trivial_subgroup G (kernel f) → is_full_subgroup H (image_subgroup f) → unit /- replace unit by is_isomorphism f -/ := sorry

  /- #Normal subgroups -/

  /-- Next, we formalize some aspects of normal subgroups. Recall that a normal subgroup H of a group G is a subgroup which is invariant under all inner automorophisms on G. --/

  definition is_normal.{u v} [constructor] {G : Group.{u}} (R : G → Prop.{v}) : Prop.{max u v} :=
  trunctype.mk (Π{g} h, R g → R (h * g * h⁻¹)) _

  structure normal_subgroup_rel (G : Group) extends subgroup_rel G :=
    (is_normal_subgroup : is_normal R)

  attribute subgroup_rel.R [coercion]
  abbreviation subgroup_to_rel      [unfold 2] := @subgroup_rel.R
  abbreviation subgroup_has_one     [unfold 2] := @subgroup_rel.Rone
  abbreviation subgroup_respect_mul [unfold 2] := @subgroup_rel.Rmul
  abbreviation subgroup_respect_inv [unfold 2] := @subgroup_rel.Rinv
  abbreviation is_normal_subgroup   [unfold 2] := @normal_subgroup_rel.is_normal_subgroup

  section
  variables {G G' G₁ G₂ G₃ : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : AbGroup}

  theorem is_normal_subgroup' (h : G) (r : N g) : N (h⁻¹ * g * h) :=
  inv_inv h ▸ is_normal_subgroup N h⁻¹ r

  definition normal_subgroup_rel_ab.{u} [constructor] (R : subgroup_rel.{_ u} A)
    : normal_subgroup_rel.{_ u} A :=
  ⦃normal_subgroup_rel, R,
    is_normal_subgroup := abstract begin
      intros g h r, xrewrite [mul.comm h g, mul_inv_cancel_right], exact r
      end end⦄

  theorem is_normal_subgroup_rev (h : G) (r : N (h * g * h⁻¹)) : N g :=
  have H : h⁻¹ * (h * g * h⁻¹) * h = g, from calc
    h⁻¹ * (h * g * h⁻¹) * h = h⁻¹ * (h * g) * h⁻¹ * h : by rewrite [-mul.assoc h⁻¹]
                        ... = h⁻¹ * (h * g)           : by rewrite [inv_mul_cancel_right]
                        ... = g                       : inv_mul_cancel_left,
  H ▸ is_normal_subgroup' N h r

  theorem is_normal_subgroup_rev' (h : G) (r : N (h⁻¹ * g * h)) : N g :=
  is_normal_subgroup_rev N h⁻¹ ((inv_inv h)⁻¹ ▸ r)

  theorem normal_subgroup_insert (r : N k) (r' : N (g * h)) : N (g * (k * h)) :=
  have H1 : N ((g * h) * (h⁻¹ * k * h)), from
    subgroup_respect_mul N r' (is_normal_subgroup' N h r),
  have H2 : (g * h) * (h⁻¹ * k * h) = g * (k * h), from calc
    (g * h) * (h⁻¹ * k * h) = g * (h * (h⁻¹ * k * h))   : mul.assoc
                        ... = g * (h * (h⁻¹ * (k * h))) : by rewrite [mul.assoc h⁻¹]
                        ... = g * (k * h)               : by rewrite [mul_inv_cancel_left],
  show N (g * (k * h)), from H2 ▸ H1
  /-- In the following, we show that the kernel of any group homomorphism f : G₁ →g G₂ is a normal subgroup of G₁ --/
  theorem is_normal_subgroup_kernel {G₁ G₂ : Group} (φ : G₁ →g G₂) (g : G₁) (h : G₁)
    : kernel_pred φ g → kernel_pred φ (h * g * h⁻¹) :=
  begin
    esimp at *,
    intro p,
    exact calc
      φ (h * g * h⁻¹) = (φ (h * g)) * φ (h⁻¹)   : to_respect_mul
                  ... = (φ h) * (φ g) * (φ h⁻¹) : to_respect_mul
                  ... = (φ h) * 1 * (φ h⁻¹)     : p
                  ... = (φ h) * (φ h⁻¹)         : mul_one
                  ... = (φ h) * (φ h)⁻¹         : to_respect_inv
                  ... = 1                       : mul.right_inv
  end

  /-- Thus, we extend the kernel subgroup to a normal subgroup --/
  definition normal_subgroup_kernel [constructor] {G₁ G₂ : Group} (φ : G₁ →g G₂) : normal_subgroup_rel G₁ :=
  ⦃ normal_subgroup_rel,
    kernel_subgroup φ,
    is_normal_subgroup := is_normal_subgroup_kernel φ
  ⦄

  -- this is just (Σ(g : G), H g), but only defined if (H g) is a prop
  definition sg : Type := {g : G | H g}
  local attribute sg [reducible]
  variable {H}
  definition subgroup_one [constructor] : sg H := ⟨one, !subgroup_has_one⟩
  definition subgroup_inv [unfold 3] : sg H → sg H :=
  λv, ⟨v.1⁻¹, subgroup_respect_inv H v.2⟩
  definition subgroup_mul [unfold 3 4] : sg H → sg H → sg H :=
  λv w, ⟨v.1 * w.1, subgroup_respect_mul H v.2 w.2⟩

  section
  local notation 1 := subgroup_one
  local postfix ⁻¹ := subgroup_inv
  local infix * := subgroup_mul

  theorem subgroup_mul_assoc (g₁ g₂ g₃ : sg H) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  subtype_eq !mul.assoc

  theorem subgroup_one_mul (g : sg H) : 1 * g = g :=
  subtype_eq !one_mul

  theorem subgroup_mul_one (g : sg H) : g * 1 = g :=
  subtype_eq !mul_one

  theorem subgroup_mul_left_inv (g : sg H) : g⁻¹ * g = 1 :=
  subtype_eq !mul.left_inv

  theorem subgroup_mul_comm {G : AbGroup} {H : subgroup_rel G} (g h : sg H)
    : g * h = h * g :=
  subtype_eq !mul.comm

  end

  variable (H)
  definition group_sg [constructor] : group (sg H) :=
  group.mk _ subgroup_mul subgroup_mul_assoc subgroup_one subgroup_one_mul subgroup_mul_one
           subgroup_inv subgroup_mul_left_inv

  definition subgroup [constructor] : Group :=
  Group.mk _ (group_sg H)

  definition ab_group_sg [constructor] {G : AbGroup} (H : subgroup_rel G)
    : ab_group (sg H) :=
  ⦃ab_group, group_sg H, mul_comm := subgroup_mul_comm⦄

  definition ab_subgroup [constructor] {G : AbGroup} (H : subgroup_rel G)
    : AbGroup :=
  AbGroup.mk _ (ab_group_sg H)

  definition kernel {G H : Group} (f : G →g H) : Group := subgroup (kernel_subgroup f)

  definition ab_kernel {G H : AbGroup} (f : G →g H) : AbGroup := ab_subgroup (kernel_subgroup f)

  definition incl_of_subgroup [constructor] {G : Group} (H : subgroup_rel G) : subgroup H →g G :=
  begin
    fapply homomorphism.mk,
      -- the underlying function
    { intro h, induction h with g, exact g},
      -- is a homomorphism
    intro g h, reflexivity
  end

  definition is_embedding_incl_of_subgroup {G : Group} (H : subgroup_rel G) : is_embedding (incl_of_subgroup H) :=
  function.is_embedding_pr1 _

  definition ab_kernel_incl {G H : AbGroup} (f : G →g H) : ab_kernel f →g G :=
  begin
    fapply incl_of_subgroup,
  end

  definition is_embedding_ab_kernel_incl {G H : AbGroup} (f : G →g H) : is_embedding (ab_kernel_incl f) :=
  begin
    fapply is_embedding_incl_of_subgroup,
  end

  definition subgroup_rel_of_subgroup {G : Group} (H1 H2 : subgroup_rel G) (hyp : Π (g : G), subgroup_rel.R H1 g → subgroup_rel.R H2 g) : subgroup_rel (subgroup H2) :=
  subgroup_rel.mk
      -- definition of the subset
    (λ h, H1 (incl_of_subgroup H2 h))
      -- contains 1
    (subgroup_has_one H1)
      -- closed under multiplication
    (λ g h p q, subgroup_respect_mul H1 p q)
      -- closed under inverses
    (λ h p, subgroup_respect_inv H1 p)

  definition image {G H : Group} (f : G →g H) : Group :=
    subgroup (image_subgroup f)

definition ab_image {G : AbGroup} {H : AbGroup} (f : G →g H) : AbGroup :=
 ab_subgroup (image_subgroup f)

definition image_incl {G H : Group} (f : G →g H) : image f →g H :=
    incl_of_subgroup (image_subgroup f)

definition ab_image_incl {A B : AbGroup} (f : A →g B) : ab_image f →g B := incl_of_subgroup (image_subgroup f)

definition is_equiv_surjection_ab_image_incl {A B : AbGroup} (f : A →g B) (H : is_surjective f) : is_equiv (ab_image_incl f ) :=
  begin
    fapply is_equiv.adjointify (ab_image_incl f),
    intro b,
    fapply sigma.mk,
    exact b,
    exact H b,
    intro b,
    reflexivity,
    intro x,
    apply subtype_eq,
    reflexivity
  end

definition iso_surjection_ab_image_incl [constructor] {A B : AbGroup} (f : A →g B) (H : is_surjective f) : ab_image f ≃g B :=
  begin
    fapply isomorphism.mk,
    exact (ab_image_incl f),
    exact is_equiv_surjection_ab_image_incl f H
  end

definition hom_lift [constructor] {G H : Group} (f : G →g H) (K : subgroup_rel H) (Hyp : Π (g : G), K (f g)) : G →g subgroup K :=
  begin
    fapply homomorphism.mk,
    intro g,
    fapply sigma.mk,
    exact f g,
    fapply Hyp,
    intro g h, apply subtype_eq, esimp, apply respect_mul
  end

definition hom_factors_through_lift {G H : Group} (f : G →g H) (K : subgroup_rel H) (Hyp : Π (g : G), K (f g)) : 
f = incl_of_subgroup K ∘g hom_lift f K Hyp :=
  begin
  fapply homomorphism_eq,
    reflexivity
  end

definition ab_hom_lift [constructor] {G H : AbGroup} (f : G →g H) (K : subgroup_rel H) (Hyp : Π (g : G), K (f g)) : G →g ab_subgroup K :=
  begin
    fapply homomorphism.mk,
    intro g,
    fapply sigma.mk,
    exact f g,
    fapply Hyp,
    intro g h, apply subtype_eq, apply respect_mul,
  end

definition ab_hom_factors_through_lift {G H : AbGroup} (f : G →g H) (K : subgroup_rel H) (Hyp : Π (g : G), K (f g)) : 
f = incl_of_subgroup K ∘g hom_lift f K Hyp :=
  begin
  fapply homomorphism_eq,
    reflexivity
  end

definition ab_hom_lift_kernel [constructor] {A B C : AbGroup} (f : A →g B) (g : B →g C) (Hyp : Π (a : A), g (f a) = 1) : A →g ab_kernel g :=
  begin
    fapply ab_hom_lift,
    exact f,
    intro a,
    exact Hyp a, 
  end

definition ab_hom_lift_kernel_factors {A B C : AbGroup} (f : A →g B) (g : B →g C) (Hyp : Π (a : A), g (f a) = 1) : 
f = ab_kernel_incl g ∘g ab_hom_lift_kernel f g Hyp :=
  begin
    fapply ab_hom_factors_through_lift,
  end

  definition image_lift [constructor] {G H : Group} (f : G →g H) : G →g image f :=
  begin
    fapply hom_lift f,
    intro g,
    apply tr,
    fapply fiber.mk,
    exact g, reflexivity
  end

definition ab_image_lift [constructor] {G H : AbGroup} (f : G →g H) : G →g image f :=
  begin
    fapply hom_lift f,
    intro g,
    apply tr,
    fapply fiber.mk,
    exact g, reflexivity
  end

  definition is_surjective_image_lift {G H : Group} (f : G →g H) : is_surjective (image_lift f) :=
  begin
    intro h,
    induction h with h p, induction p with x, induction x with g p,
    fapply image.mk,
    exact g, induction p, reflexivity
  end

  definition image_factor {G H : Group} (f : G →g H) : f = (image_incl f) ∘g (image_lift f) :=
  begin
    fapply homomorphism_eq,
    reflexivity
  end

  definition image_incl_injective {G H : Group} (f : G →g H) : Π (x y : image f), (image_incl f x = image_incl f y) → (x = y) :=
  begin
    intro x y,
    intro p,
    fapply subtype_eq,
    exact p
  end

  definition image_incl_eq_one {G H : Group} (f : G →g H) : Π (x : image f), (image_incl f x = 1) → x = 1 :=
  begin
    intro x,
    fapply image_incl_injective f x 1,
  end

  definition image_elim_lemma {f₁ : G₁ →g G₂} {f₂ : G₁ →g G₃} (h : Π⦃g⦄, f₁ g = 1 → f₂ g = 1)
    (g g' : G₁) (p : f₁ g = f₁ g') : f₂ g = f₂ g' :=
  have f₁ (g * g'⁻¹) = 1, from !to_respect_mul ⬝ ap (mul _) !to_respect_inv ⬝
    mul_inv_eq_of_eq_mul (p ⬝ !one_mul⁻¹),
  have f₂ (g * g'⁻¹) = 1, from h this,
  eq_of_mul_inv_eq_one (ap (mul _) !to_respect_inv⁻¹ ⬝ !to_respect_mul⁻¹ ⬝ this)

  open image
  definition image_elim {f₁ : G₁ →g G₂} (f₂ : G₁ →g G₃) (h : Π⦃g⦄, f₁ g = 1 → f₂ g = 1) :
    image f₁ →g G₃ :=
  homomorphism.mk (total_image.elim_set f₂ (image_elim_lemma h))
  begin
    refine total_image.rec _, intro g,
    refine total_image.rec _, intro g',
    exact to_respect_mul f₂ g g'
  end

  definition image_homomorphism {A B C : AbGroup} (f : A →g B) (g : B →g C) :
    ab_image f →g ab_image (g ∘g f) :=
  begin
    fapply image_elim,
    exact image_lift (g ∘g f),
    intro a p,
    fapply subtype_eq, unfold image_lift,
    exact calc
      g (f a) = g 1 : by exact ap g p
         ...  = 1   : to_respect_one,
  end

  definition image_homomorphism_square {A B C : AbGroup} (f : A →g B) (g : B →g C) :
    g ∘g image_incl f ~ image_incl (g ∘g f ) ∘g image_homomorphism f g :=
  begin
    intro x, induction x with b p, induction p with x, induction x with a p, induction p, reflexivity
  end

  end

  variables {G H K : Group} {R : subgroup_rel G} {S : subgroup_rel H} {T : subgroup_rel K}
  open function
  definition subgroup_functor_fun [unfold 7] (φ : G →g H) (h : Πg, R g → S (φ g)) (x : subgroup R) :
    subgroup S :=
  begin
    induction x with g hg,
    exact ⟨φ g, h g hg⟩
  end

  definition subgroup_functor [constructor] (φ : G →g H)
    (h : Πg, R g → S (φ g)) : subgroup R →g subgroup S :=
  begin
    fapply homomorphism.mk,
    { exact subgroup_functor_fun φ h },
    { intro x₁ x₂, induction x₁ with g₁ hg₁, induction x₂ with g₂ hg₂,
      exact sigma_eq !to_respect_mul !is_prop.elimo }
  end

  definition ab_subgroup_functor [constructor] {G H : AbGroup} {R : subgroup_rel G}
    {S : subgroup_rel H} (φ : G →g H)
    (h : Πg, R g → S (φ g)) : ab_subgroup R →g ab_subgroup S :=
  subgroup_functor φ h

  theorem subgroup_functor_compose (ψ : H →g K) (φ : G →g H)
    (hψ : Πg, S g → T (ψ g)) (hφ : Πg, R g → S (φ g)) :
    subgroup_functor ψ hψ ∘g subgroup_functor φ hφ ~
    subgroup_functor (ψ ∘g φ) (λg, proof hψ (φ g) qed ∘ hφ g) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_gid : subgroup_functor (gid G) (λg, id) ~ gid (subgroup R) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_mul {G H : AbGroup} {R : subgroup_rel G} {S : subgroup_rel H}
    (ψ φ : G →g H) (hψ : Πg, R g → S (ψ g)) (hφ : Πg, R g → S (φ g)) :
    homomorphism_mul (ab_subgroup_functor ψ hψ) (ab_subgroup_functor φ hφ) ~
    ab_subgroup_functor (homomorphism_mul ψ φ)
                        (λg hg, subgroup_respect_mul S (hψ g hg) (hφ g hg)) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_homotopy {ψ φ : G →g H} (hψ : Πg, R g → S (ψ g))
    (hφ : Πg, R g → S (φ g)) (p : φ ~ ψ) :
    subgroup_functor φ hφ ~ subgroup_functor ψ hψ :=
  begin
    intro g, induction g with g hg,
    exact subtype_eq (p g)
  end

  definition subgroup_of_subgroup_incl {R S : subgroup_rel G} (H : Π (g : G), R g -> S g) : subgroup R →g subgroup S
  :=
  subgroup_functor (gid G) H

  definition is_embedding_subgroup_of_subgroup_incl {R S : subgroup_rel G} (H : Π (g : G), R g -> S g) : is_embedding (subgroup_of_subgroup_incl H) :=
  begin
    fapply is_embedding_of_is_injective,
    intro x y p,
    induction x with x r, induction y with y s,
    fapply subtype_eq, esimp,
    unfold subgroup_of_subgroup_incl at p, exact ap pr1 p,
  end

  definition ab_subgroup_of_subgroup_incl {A : AbGroup} {R S : subgroup_rel A} (H : Π (a : A), R a -> S a) : ab_subgroup R →g ab_subgroup S
  :=
  ab_subgroup_functor (gid A) H

  definition is_embedding_ab_subgroup_of_subgroup_incl {A : AbGroup} {R S : subgroup_rel A} (H : Π (a : A), R a -> S a) : is_embedding (ab_subgroup_of_subgroup_incl H) :=
  begin
    fapply is_embedding_subgroup_of_subgroup_incl,
  end

  definition ab_subgroup_iso {A : AbGroup} {R S : subgroup_rel A} (H : Π (a : A), R a -> S a) (K : Π (a : A), S a -> R a) : 
    ab_subgroup R ≃g ab_subgroup S :=
  begin
    fapply isomorphism.mk,
    exact subgroup_of_subgroup_incl H,
    fapply is_equiv.adjointify,
    exact subgroup_of_subgroup_incl K,
    intro s, induction s with a p, fapply subtype_eq, reflexivity,
    intro r, induction r with a p, fapply subtype_eq, reflexivity
  end

  definition ab_subgroup_iso_triangle {A : AbGroup} {R S : subgroup_rel A} (H : Π (a : A), R a -> S a) (K : Π (a : A), S a -> R a) : incl_of_subgroup R  ~ incl_of_subgroup S ∘g ab_subgroup_iso H K :=
  begin
    intro r, induction r, reflexivity
  end 

end group

open group
attribute image_subgroup [constructor]
