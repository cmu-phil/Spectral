/-
Copyright (c) 2015 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke, Jeremy Avigad

Basic concepts of group theory
-/
import algebra.group_theory ..move_to_lib ..property

open eq algebra is_trunc sigma sigma.ops prod trunc property

namespace group

  /- #Subgroups -/
  /-- Recall that a subtype of a type A is the same thing as a family
      of mere propositions over A. Thus, we define a subgroup of a
      group G to be a family of mere propositions over (the underlying
     type of) G, closed under the constants and operations --/

  structure is_subgroup [class] (G : Group) (H : property G) : Type :=
    (one_mem : 1 ∈ H)
    (mul_mem : Π{g h}, g ∈ H → h ∈ H → g * h ∈ H)
    (inv_mem : Π{g}, g ∈ H → g⁻¹ ∈ H)

  definition is_prop_is_subgroup [instance] (G : Group) (H : property G) : is_prop (is_subgroup G H) :=
  proof -- this results in a simpler choice of universe metavariables
  have 1 ∈ H × (Π{g h}, g ∈ H → h ∈ H → g * h ∈ H) × (Π{g}, g ∈ H → g⁻¹ ∈ H) ≃ is_subgroup G H,
  begin
    fapply equiv.MK,
    { intro p, cases p with p1 p2, cases p2 with p2 p3, exact is_subgroup.mk p1 @p2 @p3 },
    { intro p, split, exact is_subgroup.one_mem H, split, apply @is_subgroup.mul_mem G H p, apply @is_subgroup.inv_mem G H p},
    { intro b, cases b, reflexivity },
    { intro a, cases a with a1 a2, cases a2, reflexivity }
  end,
  is_trunc_equiv_closed _ this
  qed

  /-- Every group G has at least two subgroups, the trivial subgroup containing only one, and the full subgroup. --/
  definition trivial_subgroup [instance] (G : Group) : is_subgroup G '{1} :=
  begin
    fapply is_subgroup.mk,
    { esimp, apply mem_insert },
    { intros g h p q, esimp at *, apply mem_singleton_of_eq, rewrite [eq_of_mem_singleton p, eq_of_mem_singleton q, mul_one]},
    { intros g p, esimp at *, apply mem_singleton_of_eq, rewrite [eq_of_mem_singleton p, one_inv] }
  end

  definition full_subgroup [instance] (G : Group) : is_subgroup G univ :=
  begin
    fapply is_subgroup.mk,
    { apply logic.trivial },
    { intros, apply logic.trivial },
    { intros, apply logic.trivial }
  end

  /-- Every group homomorphism f : G -> H determines a subgroup of H,
      the image of f, and a subgroup of G, the kernel of f. In the
      following definition we define the image of f. Since a subgroup
      is required to be closed under the group operations, showing
      that the image of f is closed under the group operations is part
      of the definition of the image of f. --/

  definition is_subgroup_image [instance] {G : Group} {H : Group} (f : G →g H) :
    is_subgroup H (image f) :=
    begin
      fapply is_subgroup.mk,
        -- subproperty contains 1
      { fapply image.mk, exact 1, apply respect_one},
        -- subproperty is closed under multiplication
      { intro h h', intro u v,
        induction u with x p, induction v with y q,
        induction p, induction q,
        apply image.mk (x * y), apply respect_mul},
        -- subproperty is closed under inverses
      { intro g, intro t, induction t with x p, induction p,
        apply image.mk x⁻¹, apply respect_inv }
    end

  section kernels

  variables {G₁ G₂ : Group}

  -- TODO: maybe define this in more generality for pointed propertys?
  definition kernel [constructor] (φ : G₁ →g G₂) : property G₁ := { g | trunctype.mk (φ g = 1) _}

  theorem mul_mem_kernel (φ : G₁ →g G₂) (g h : G₁) (H₁ : g ∈ kernel φ) (H₂ : h ∈ kernel φ) : g * h ∈ kernel φ :=
  calc
    φ (g * h) = (φ g) * (φ h) : to_respect_mul
          ... = 1 * (φ h)     : H₁
          ... = 1 * 1         : H₂
          ... = 1             : one_mul

  theorem inv_mem_kernel (φ : G₁ →g G₂) (g : G₁) (H : g ∈ kernel φ) : g⁻¹ ∈ kernel φ :=
  calc
    φ g⁻¹ = (φ g)⁻¹ : to_respect_inv
      ... = 1⁻¹     : H
      ... = 1       : one_inv

  definition is_subgroup_kernel [constructor] [instance] (φ : G₁ →g G₂) : is_subgroup G₁ (kernel φ) :=
  ⦃ is_subgroup,
    one_mem := respect_one φ,
    mul_mem := mul_mem_kernel φ,
    inv_mem := inv_mem_kernel φ
  ⦄

  end kernels

  /-- Now we should be able to show that if f is a homomorphism for which the kernel is trivial and the
     image is full, then f is an isomorphism, except that no one defined the proposition that f is an
      isomorphism :/ --/
  /- definition is_iso_from_kertriv_imfull {G H : Group} (f : G →g H) :
     is_trivial_subgroup G (kernel f) → is_full_subgroup H (image_subgroup f) → unit
     /- replace unit by is_isomorphism f -/ := sorry -/

  /- #Normal subgroups -/

  /-- Next, we formalize some aspects of normal subgroups. Recall that a normal subgroup H of a
      group G is a subgroup which is invariant under all inner automorophisms on G. --/

  definition is_normal.{u v} [constructor] (G : Group) (N : property.{u v} G) : Prop :=
  trunctype.mk (Π{g} h, g ∈ N → h * g * h⁻¹ ∈ N) _

  structure is_normal_subgroup [class] (G : Group) (N : property G) extends is_subgroup G N :=
    (is_normal : is_normal G N)

  abbreviation subgroup_one_mem   [unfold 2] := @is_subgroup.one_mem
  abbreviation subgroup_mul_mem   [unfold 2] := @is_subgroup.mul_mem
  abbreviation subgroup_inv_mem   [unfold 2] := @is_subgroup.inv_mem
  abbreviation subgroup_is_normal [unfold 2] := @is_normal_subgroup.is_normal

section
  variables {G G' G₁ G₂ G₃ : Group} {H N : property G} [is_subgroup G H]
            [is_normal_subgroup G N] {g g' h h' k : G}
            {A B : AbGroup}

  theorem is_normal_subgroup' (h : G) (r : g ∈ N) : h⁻¹ * g * h ∈ N :=
  inv_inv h ▸ subgroup_is_normal N h⁻¹ r

  definition is_normal_subgroup_ab [constructor] {C : property A} (subgrpA : is_subgroup A C)
    : is_normal_subgroup A C :=
  ⦃ is_normal_subgroup, subgrpA,
    is_normal := abstract begin
      intros g h r, xrewrite [mul.comm h g, mul_inv_cancel_right], exact r
      end end⦄

  theorem is_normal_subgroup_rev (h : G) (r : h * g * h⁻¹ ∈ N) : g ∈ N :=
  have H : h⁻¹ * (h * g * h⁻¹) * h = g, from calc
    h⁻¹ * (h * g * h⁻¹) * h = h⁻¹ * (h * g) * h⁻¹ * h : by rewrite [-mul.assoc h⁻¹]
                        ... = h⁻¹ * (h * g)           : by rewrite [inv_mul_cancel_right]
                        ... = g                       : inv_mul_cancel_left,
  H ▸ is_normal_subgroup' h r

  theorem is_normal_subgroup_rev' (h : G) (r : h⁻¹ * g * h ∈ N) : g ∈ N :=
  is_normal_subgroup_rev h⁻¹ ((inv_inv h)⁻¹ ▸ r)

  theorem normal_subgroup_insert (r : k ∈ N) (r' : g * h ∈ N) : g * (k * h) ∈ N :=
  have H1 : (g * h) * (h⁻¹ * k * h) ∈ N, from
    subgroup_mul_mem r' (is_normal_subgroup' h r),
  have H2 : (g * h) * (h⁻¹ * k * h) = g * (k * h), from calc
    (g * h) * (h⁻¹ * k * h) = g * (h * (h⁻¹ * k * h))   : mul.assoc
                        ... = g * (h * (h⁻¹ * (k * h))) : by rewrite [mul.assoc h⁻¹]
                        ... = g * (k * h)               : by rewrite [mul_inv_cancel_left],
  show N (g * (k * h)), from H2 ▸ H1

  /-- In the following, we show that the kernel of any group homomorphism f : G₁ →g G₂ is a normal subgroup of G₁ --/
  theorem is_normal_subgroup_kernel {G₁ G₂ : Group} (φ : G₁ →g G₂) (g : G₁) (h : G₁)
    : g ∈ kernel φ → h * g * h⁻¹ ∈ kernel φ :=
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

  -- this is just (Σ(g : G), H g), but only defined if (H g) is a prop
  definition sg {G : Group} (H : property G) : Type := subtype (λ x, x ∈ H)
  local attribute sg [reducible]

  definition subgroup_one [constructor] : sg H := ⟨one, subgroup_one_mem H⟩
  definition subgroup_inv [unfold 3] : sg H → sg H :=
  λv, ⟨v.1⁻¹, subgroup_inv_mem v.2⟩
  definition subgroup_mul [unfold 3 4] : sg H → sg H → sg H :=
  λv w, ⟨v.1 * w.1, subgroup_mul_mem v.2 w.2⟩

  definition subgroup_elt (x : sg H) : G := x.1

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

  theorem subgroup_mul_comm {G : AbGroup} {H : property G} [subgrpH : is_subgroup G H] (g h : sg H)
    : subgroup_mul g h = subgroup_mul h g :=
  subtype_eq !mul.comm

  end

  variable (H)

  definition group_sg [constructor] : group (sg H) :=
  group.mk _ subgroup_mul subgroup_mul_assoc subgroup_one subgroup_one_mul subgroup_mul_one
    subgroup_inv subgroup_mul_left_inv

  definition subgroup [constructor] : Group :=
  Group.mk _ (group_sg H)

  variable {H}

  definition ab_group_sg [constructor] {G : AbGroup} (H : property G) [is_subgroup G H]
    : ab_group (sg H) :=
  ⦃ab_group, (group_sg H), mul_comm := subgroup_mul_comm⦄

  definition ab_subgroup [constructor] {G : AbGroup} (H : property G) [is_subgroup G H]
    : AbGroup :=
  AbGroup.mk _ (ab_group_sg H)

  definition Kernel {G H : Group} (f : G →g H) : Group := subgroup (kernel f)

  definition ab_Kernel {G H : AbGroup} (f : G →g H) : AbGroup := ab_subgroup (kernel f)

  definition incl_of_subgroup [constructor] {G : Group} (H : property G) [is_subgroup G H] :
    subgroup H →g G :=
  begin
    fapply homomorphism.mk,
      -- the underlying function
    { intro h, induction h with g, exact g},
       -- is a homomorphism
    intro g h, reflexivity
  end

  definition is_embedding_incl_of_subgroup {G : Group} (H : property G) [is_subgroup G H] :
    is_embedding (incl_of_subgroup H) :=
  begin
    fapply function.is_embedding_of_is_injective,
    intro h h',
    fapply subtype_eq
  end

  definition ab_Kernel_incl {G H : AbGroup} (f : G →g H) : ab_Kernel f →g G :=
  begin
    fapply incl_of_subgroup,
  end

  definition is_embedding_ab_kernel_incl {G H : AbGroup} (f : G →g H) : is_embedding (ab_Kernel_incl f) :=
  begin
    fapply is_embedding_incl_of_subgroup,
  end

  definition is_subgroup_of_is_subgroup {G : Group} {H1 H2 : property G} [is_subgroup G H1]
    [is_subgroup G H2] (hyp : Π (g : G), g ∈ H1 → g ∈ H2) :
      is_subgroup (subgroup H2) {h | incl_of_subgroup H2 h ∈ H1} :=
  is_subgroup.mk
    (subgroup_one_mem H1)
    (begin
      intros g h p q,
      apply mem_property_of,
      apply subgroup_mul_mem (of_mem_property_of p) (of_mem_property_of q),
    end)
    (begin
      intros h p,
      apply mem_property_of,
      apply subgroup_inv_mem (of_mem_property_of p)
    end)

  definition Image {G H : Group} (f : G →g H) : Group :=
    subgroup (image f)

  definition ab_Image {G : AbGroup} {H : Group} (f : G →g H) : AbGroup :=
  AbGroup_of_Group (Image f)
  begin
    intro g h,
    induction g with x t, induction h with y s,
    fapply subtype_eq,
    induction t with g p, induction s with h q, induction p, induction q,
    refine (((respect_mul f g h)⁻¹ ⬝ _) ⬝ (respect_mul f h g)),
    apply (ap f),
    induction G, induction struct', apply mul_comm
  end

  definition image_incl {G H : Group} (f : G →g H) : Image f →g H :=
    incl_of_subgroup (image f)

definition ab_Image_incl {A B : AbGroup} (f : A →g B) : ab_Image f →g B := incl_of_subgroup (image f)

definition is_equiv_surjection_ab_image_incl {A B : AbGroup} (f : A →g B) (H : is_surjective f) : is_equiv (ab_Image_incl f ) :=
  begin
    fapply is_equiv.adjointify (ab_Image_incl f),
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

definition iso_surjection_ab_image_incl [constructor] {A B : AbGroup} (f : A →g B) (H : is_surjective f) : ab_Image f ≃g B :=
  begin
    fapply isomorphism.mk,
    exact (ab_Image_incl f),
    exact is_equiv_surjection_ab_image_incl f H
  end

  definition hom_lift [constructor] {G H : Group} (f : G →g H) (K : property H) [is_subgroup H K] (Hyp : Π (g : G), K (f g)) : G →g subgroup K :=
  begin
    fapply homomorphism.mk,
    intro g,
    fapply sigma.mk,
    exact f g,
    fapply Hyp,
    intro g h, apply subtype_eq, esimp, apply respect_mul
  end

definition hom_factors_through_lift {G H : Group} (f : G →g H) (K : property H) [is_subgroup H K]  (Hyp : Π (g : G), K (f g)) :
f = incl_of_subgroup K ∘g hom_lift f K Hyp :=
  begin
  fapply homomorphism_eq,
    reflexivity
  end

definition ab_hom_lift [constructor] {G H : AbGroup} (f : G →g H) (K : property H) [is_subgroup H K] (Hyp : Π (g : G), K (f g)) : G →g ab_subgroup K :=
  begin
    fapply homomorphism.mk,
    intro g,
    fapply sigma.mk,
    exact f g,
    fapply Hyp,
    intro g h, apply subtype_eq, apply respect_mul,
  end

definition ab_hom_factors_through_lift {G H : AbGroup} (f : G →g H) (K : property H) [is_subgroup H K] (Hyp : Π (g : G), K (f g)) :
f = incl_of_subgroup K ∘g hom_lift f K Hyp :=
  begin
  fapply homomorphism_eq,
    reflexivity
  end

definition ab_hom_lift_kernel [constructor] {A B C : AbGroup} (f : A →g B) (g : B →g C) (Hyp : Π (a : A), g (f a) = 1) : A →g ab_Kernel g :=
  begin
    fapply ab_hom_lift,
    exact f,
    intro a,
    exact Hyp a,
  end

definition ab_hom_lift_kernel_factors {A B C : AbGroup} (f : A →g B) (g : B →g C) (Hyp : Π (a : A), g (f a) = 1) :
f = ab_Kernel_incl g ∘g ab_hom_lift_kernel f g Hyp :=
  begin
    fapply ab_hom_factors_through_lift,
  end

  definition image_lift [constructor] {G H : Group} (f : G →g H) : G →g Image f :=
  begin
    fapply hom_lift f,
    intro g,
    apply tr,
    fapply fiber.mk,
    exact g, reflexivity
  end

definition ab_image_lift [constructor] {G H : AbGroup} (f : G →g H) : G →g Image f :=
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
    induction h with h p, induction p with g,
    fapply image.mk,
    exact g, induction p, reflexivity
  end

  definition image_factor {G H : Group} (f : G →g H) : f = (image_incl f) ∘g (image_lift f) :=
  begin
    fapply homomorphism_eq,
    reflexivity
  end

  definition image_incl_injective {G H : Group} (f : G →g H) : Π (x y : Image f),
    (image_incl f x = image_incl f y) → (x = y) :=
  begin
    intro x y,
    intro p,
    fapply subtype_eq,
    exact p
  end

  definition image_incl_eq_one {G H : Group} (f : G →g H) :
    Π (x : Image f), (image_incl f x = 1) → x = 1 :=
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
    Image f₁ →g G₃ :=
  homomorphism.mk (total_image.elim_set f₂ (image_elim_lemma h))
  begin
    refine total_image.rec _, intro g,
    refine total_image.rec _, intro g',
    exact to_respect_mul f₂ g g'
  end
end

  definition image_homomorphism {A B C : AbGroup} (f : A →g B) (g : B →g C) :
    ab_Image f →g ab_Image (g ∘g f) :=
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
    intro x, induction x with b p, induction p with x, induction p, reflexivity
  end

  variables {G H K : Group} {R : property G} [is_subgroup G R]
            {S : property H} [is_subgroup H S] {T : property K} [is_subgroup K T]
  open function

  definition subgroup_functor_fun [unfold 7] (φ : G →g H) (h : Πg, g ∈ R → φ g ∈ S)
      (x : subgroup R) :
    subgroup S :=
  begin
    induction x with g hg,
    exact ⟨φ g, h g hg⟩
  end

  definition subgroup_functor [constructor] (φ : G →g H)
    (h : Πg, g ∈ R → φ g ∈ S) : subgroup R →g subgroup S :=
  begin
    fapply homomorphism.mk,
    { exact subgroup_functor_fun φ h },
    { intro x₁ x₂, induction x₁ with g₁ hg₁, induction x₂ with g₂ hg₂,
      exact sigma_eq !to_respect_mul !is_prop.elimo }
  end

  definition ab_subgroup_functor [constructor] {G H : AbGroup}
    {R : property G} [is_subgroup G R]
    {S : property H} [is_subgroup H S]
    (φ : G →g H)
    (h : Πg, g ∈ R → φ g ∈ S) : ab_subgroup R →g ab_subgroup S :=
  subgroup_functor φ h

  theorem subgroup_functor_compose (ψ : H →g K) (φ : G →g H)
    (hψ : Πg, g ∈ S → ψ g ∈ T) (hφ : Πg, g ∈ R → φ g ∈ S) :
    subgroup_functor ψ hψ ∘g subgroup_functor φ hφ ~
    subgroup_functor (ψ ∘g φ) (λg, proof hψ (φ g) qed ∘ hφ g) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_gid : subgroup_functor (gid G) (λg, id) ~ gid (subgroup R) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_mul {G H : AbGroup} {R : property G} [subgroupR : is_subgroup G R]
    {S : property H} [subgroupS : is_subgroup H S]
    (ψ φ : G →g H) (hψ : Πg, g ∈ R → ψ g ∈ S) (hφ : Πg, g ∈ R → φ g ∈ S) :
    homomorphism_mul (ab_subgroup_functor ψ hψ) (ab_subgroup_functor φ hφ) ~
    ab_subgroup_functor (homomorphism_mul ψ φ)
                        (λg hg, subgroup_mul_mem (hψ g hg) (hφ g hg)) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_homotopy {ψ φ : G →g H} (hψ : Πg, R g → S (ψ g))
    (hφ : Πg, g ∈ R → φ g ∈ S) (p : φ ~ ψ) :
    subgroup_functor φ hφ ~ subgroup_functor ψ hψ :=
  begin
    intro g, induction g with g hg,
    exact subtype_eq (p g)
  end

  definition subgroup_of_subgroup_incl {R S : property G} [is_subgroup G R] [is_subgroup G S]
    (H : Π (g : G), g ∈ R → g ∈ S) : subgroup R →g subgroup S
  :=
  subgroup_functor (gid G) H

  definition is_embedding_subgroup_of_subgroup_incl {R S : property G} [is_subgroup G R] [is_subgroup G S]
    (H : Π (g : G), g ∈ R -> g ∈ S) : is_embedding (subgroup_of_subgroup_incl H) :=
  begin
    fapply is_embedding_of_is_injective,
    intro x y p,
    induction x with x r, induction y with y s,
    fapply subtype_eq, esimp,
    unfold subgroup_of_subgroup_incl at p, exact ap pr1 p,
  end

  definition ab_subgroup_of_subgroup_incl {A : AbGroup} {R S : property A} [is_subgroup A R] [is_subgroup A S]
    (H : Π (a : A), a ∈ R → a ∈ S) : ab_subgroup R →g ab_subgroup S
  :=
  ab_subgroup_functor (gid A) H

  definition is_embedding_ab_subgroup_of_subgroup_incl {A : AbGroup} {R S : property A} [is_subgroup A R] [is_subgroup A S]
    (H : Π (a : A), a ∈ R → a ∈ S) : is_embedding (ab_subgroup_of_subgroup_incl H) :=
  begin
    fapply is_embedding_subgroup_of_subgroup_incl
  end

  definition ab_subgroup_iso {A : AbGroup} {R S : property A} [is_subgroup A R] [is_subgroup A S]
      (H : Π (a : A), a ∈ R → a ∈ S) (K : Π (a : A), a ∈ S → a ∈ R) :
    ab_subgroup R ≃g ab_subgroup S :=
  begin
    fapply isomorphism.mk,
    exact subgroup_of_subgroup_incl H,
    fapply is_equiv.adjointify,
    exact subgroup_of_subgroup_incl K,
    intro s, induction s with a p, fapply subtype_eq, reflexivity,
    intro r, induction r with a p, fapply subtype_eq, reflexivity
  end

  definition ab_subgroup_iso_triangle {A : AbGroup} {R S : property A} [is_subgroup A R] [is_subgroup A S]
      (H : Π (a : A), a ∈ R → a ∈ S) (K : Π (a : A), a ∈ S → a ∈ R) :
    incl_of_subgroup R  ~ incl_of_subgroup S ∘g ab_subgroup_iso H K :=
  begin
    intro r, induction r, reflexivity
  end

end group

open group
attribute is_subgroup_image [constructor]
attribute is_subgroup_kernel [constructor]
