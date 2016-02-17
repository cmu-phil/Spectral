/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Basic group theory
-/


/-
  Groups are defined in the HoTT library in algebra/group, as part of the algebraic hierarchy.
  However, there is currently no group theory.
  The only relevant defintions are the trivial group (in types/unit) and some files in algebra/
-/

import types.pointed types.pi algebra.bundled algebra.category.category

open eq algebra pointed function is_trunc pi category equiv is_equiv
set_option class.force_new true

namespace group

  definition pointed_Group [instance] (G : Group) : pointed G := pointed.mk one
  definition pType_of_Group [reducible] (G : Group) : Type* := pointed.mk' G
  definition Set_of_Group (G : Group) : Set := trunctype.mk G _

  definition Group_of_CommGroup [coercion] [constructor] (G : CommGroup) : Group :=
  Group.mk G _

  definition comm_group_Group_of_CommGroup [instance] [constructor] (G : CommGroup)
    : comm_group (Group_of_CommGroup G) :=
  begin esimp, exact _ end

  definition group_pType_of_Group [instance] (G : Group) : group (pType_of_Group G) :=
  Group.struct G

  /- group homomorphisms -/

  definition is_homomorphism [class] [reducible]
    {G₁ G₂ : Type} [group G₁] [group G₂] (φ : G₁ → G₂) : Type :=
  Π(g h : G₁), φ (g * h) = φ g * φ h

  section
  variables {G G₁ G₂ G₃ : Type} {g h : G₁} (ψ : G₂ → G₃) {φ₁ φ₂ : G₁ → G₂} (φ : G₁ → G₂)
            [group G] [group G₁] [group G₂] [group G₃]
            [is_homomorphism ψ] [is_homomorphism φ₁] [is_homomorphism φ₂] [is_homomorphism φ]

  definition respect_mul /- φ -/ : Π(g h : G₁), φ (g * h) = φ g * φ h :=
  by assumption

  theorem respect_one /- φ -/ : φ 1 = 1 :=
  mul.right_cancel
    (calc
      φ 1 * φ 1 = φ (1 * 1) : respect_mul φ
            ... = φ 1 : ap φ !one_mul
            ... = 1 * φ 1 : one_mul)

  theorem respect_inv /- φ -/ (g : G₁) : φ g⁻¹ = (φ g)⁻¹ :=
  eq_inv_of_mul_eq_one (!respect_mul⁻¹ ⬝ ap φ !mul.left_inv ⬝ !respect_one)

  definition is_embedding_homomorphism /- φ -/ (H : Π{g}, φ g = 1 → g = 1) : is_embedding φ :=
  begin
    apply function.is_embedding_of_is_injective,
    intro g g' p,
    apply eq_of_mul_inv_eq_one,
    apply H,
    refine !respect_mul ⬝ _,
    rewrite [respect_inv φ, p],
    apply mul.right_inv
  end

  definition is_homomorphism_compose {ψ : G₂ → G₃} {φ : G₁ → G₂}
    (H1 : is_homomorphism ψ) (H2 : is_homomorphism φ) : is_homomorphism (ψ ∘ φ) :=
  λg h, ap ψ !respect_mul ⬝ !respect_mul

  definition is_homomorphism_id (G : Type) [group G] : is_homomorphism (@id G) :=
  λg h, idp

  end

  structure homomorphism (G₁ G₂ : Group) : Type :=
    (φ : G₁ → G₂)
    (p : is_homomorphism φ)

  infix ` →g `:55 := homomorphism

  definition group_fun [unfold 3] [coercion] := @homomorphism.φ
  definition homomorphism.struct [instance] [priority 2000] {G₁ G₂ : Group} (φ : G₁ →g G₂)
    : is_homomorphism φ :=
  homomorphism.p φ

  variables {G G₁ G₂ G₃ : Group} {g h : G₁} {ψ : G₂ →g G₃} {φ₁ φ₂ : G₁ →g G₂} (φ : G₁ →g G₂)

  definition to_respect_mul /- φ -/ (g h : G₁) : φ (g * h) = φ g * φ h :=
  respect_mul φ g h

  theorem to_respect_one /- φ -/ : φ 1 = 1 :=
  respect_one φ

  theorem to_respect_inv /- φ -/ (g : G₁) : φ g⁻¹ = (φ g)⁻¹ :=
  respect_inv φ g

  definition to_is_embedding_homomorphism /- φ -/ (H : Π{g}, φ g = 1 → g = 1) : is_embedding φ :=
  is_embedding_homomorphism φ @H

  definition is_set_homomorphism [instance] (G₁ G₂ : Group) : is_set (G₁ →g G₂) :=
  begin
    assert H : G₁ →g G₂ ≃ Σ(f : G₁ → G₂), Π(g₁ g₂ : G₁), f (g₁ * g₂) = f g₁ * f g₂,
    { fapply equiv.MK,
      { intro φ, induction φ, constructor, assumption},
      { intro v, induction v, constructor, assumption},
      { intro v, induction v, reflexivity},
      { intro φ, induction φ, reflexivity}},
    apply is_trunc_equiv_closed_rev, exact H
  end

  local attribute group_pType_of_Group pointed.mk' [reducible]
  definition pmap_of_homomorphism [constructor] /- φ -/ : pType_of_Group G₁ →* pType_of_Group G₂ :=
  pmap.mk φ (respect_one φ)

  definition homomorphism_eq (p : group_fun φ₁ ~ group_fun φ₂) : φ₁ = φ₂ :=
  begin
    induction φ₁ with φ₁ q₁, induction φ₂ with φ₂ q₂, esimp at p, induction p,
    exact ap (homomorphism.mk φ₁) !is_prop.elim
  end

  /- categorical structure of groups + homomorphisms -/

  definition homomorphism_compose [constructor] (ψ : G₂ →g G₃) (φ : G₁ →g G₂) : G₁ →g G₃ :=
  homomorphism.mk (ψ ∘ φ) (is_homomorphism_compose _ _)

  definition homomorphism_id [constructor] (G : Group) : G →g G :=
  homomorphism.mk (@id G) (is_homomorphism_id G)

  infixr ` ∘g `:75 := homomorphism_compose
  notation 1       := homomorphism_id _

  structure isomorphism (A B : Group) :=
    (to_hom : A →g B)
    (is_equiv_to_hom : is_equiv to_hom)

  infix ` ≃g `:25 := isomorphism
  attribute isomorphism.to_hom [coercion]
  attribute isomorphism.is_equiv_to_hom [instance]

  definition equiv_of_isomorphism [constructor] (φ : G₁ ≃g G₂) : G₁ ≃ G₂ :=
  equiv.mk φ _

  definition to_ginv [constructor] (φ : G₁ ≃g G₂) : G₂ →g G₁ :=
  homomorphism.mk φ⁻¹
    abstract begin
    intro g₁ g₂, apply eq_of_fn_eq_fn' φ,
    rewrite [respect_mul φ, +right_inv φ]
    end end

  definition isomorphism.refl [refl] [constructor] (G : Group) : G ≃g G :=
  isomorphism.mk 1 !is_equiv_id

  definition isomorphism.symm [symm] [constructor] (φ : G₁ ≃g G₂) : G₂ ≃g G₁ :=
  isomorphism.mk (to_ginv φ) !is_equiv_inv

  definition isomorphism.trans [trans] [constructor] (φ : G₁ ≃g G₂) (ψ : G₂ ≃g G₃)
    : G₁ ≃g G₃ :=
  isomorphism.mk (ψ ∘g φ) !is_equiv_compose

  postfix `⁻¹ᵍ`:(max + 1) := isomorphism.symm
  infixl ` ⬝g `:75 := isomorphism.trans

  -- TODO
  -- definition Group_univalence (G₁ G₂ : Group) : (G₁ ≃g G₂) ≃ (G₁ = G₂) :=
  -- begin
  --   fapply equiv.MK,
  --   { intro φ, fapply Group_eq, apply equiv_of_isomorphism φ, apply respect_mul},
  --   { intro p, apply transport _ p, reflexivity},
  --   { intro p, induction p, esimp, },
  --   { }
  -- end

  /- category of groups -/

  definition precategory_group [constructor] : precategory Group :=
  precategory.mk homomorphism
                 @homomorphism_compose
                 @homomorphism_id
                 (λG₁ G₂ G₃ G₄ φ₃ φ₂ φ₁, homomorphism_eq (λg, idp))
                 (λG₁ G₂ φ, homomorphism_eq (λg, idp))
                 (λG₁ G₂ φ, homomorphism_eq (λg, idp))

  -- TODO
  -- definition category_group : category Group :=
  -- category.mk precategory_group
  -- begin
  --   intro G₁ G₂,
  --   fapply adjointify,
  --   { intro φ, fapply Group_eq, },
  --   { },
  --   { }
  -- end

end group
