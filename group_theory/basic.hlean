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
  definition Pointed_of_Group (G : Group) : Type* := pointed.mk' G
  definition hset_of_Group (G : Group) : hset := trunctype.mk G _

 -- print Type*
 -- print Pointed

  definition Group_of_CommGroup [coercion] [constructor] (G : CommGroup) : Group :=
  Group.mk G _

  definition comm_group_Group_of_CommGroup [instance] [constructor] (G : CommGroup)
    : comm_group (Group_of_CommGroup G) :=
  begin esimp, exact _ end

  /- group homomorphisms -/

  structure homomorphism (G₁ G₂ : Group) : Type :=
    (φ : G₁ → G₂)
    (p : Π(g h : G₁), φ (g * h) = φ g * φ h)

  attribute homomorphism.φ [coercion]
  abbreviation group_fun [unfold 3] := @homomorphism.φ
  abbreviation respect_mul := @homomorphism.p
  infix ` →g `:55 := homomorphism

  variables {G G₁ G₂ G₃ : Group} {g h : G₁} {ψ : G₂ →g G₃} {φ φ' : G₁ →g G₂}

  theorem respect_one (φ : G₁ →g G₂) : φ 1 = 1 :=
  mul.right_cancel
    (calc
      φ 1 * φ 1 = φ (1 * 1) : respect_mul
            ... = φ 1 : ap φ !one_mul
            ... = 1 * φ 1 : one_mul)

  theorem respect_inv (φ : G₁ →g G₂) (g : G₁) : φ g⁻¹ = (φ g)⁻¹ :=
  eq_inv_of_mul_eq_one (!respect_mul⁻¹ ⬝ ap φ !mul.left_inv ⬝ !respect_one)

  definition is_hset_homomorphism [instance] (G₁ G₂ : Group) : is_hset (homomorphism G₁ G₂) :=
  begin
    assert H : G₁ →g G₂ ≃ Σ(f : G₁ → G₂), Π(g₁ g₂ : G₁), f (g₁ * g₂) = f g₁ * f g₂,
    { fapply equiv.MK,
      { intro φ, induction φ, constructor, assumption},
      { intro v, induction v, constructor, assumption},
      { intro v, induction v, reflexivity},
      { intro φ, induction φ, reflexivity}},
    apply is_trunc_equiv_closed_rev, exact H
  end

  definition pmap_of_homomorphism [constructor] (φ : G₁ →g G₂)
    : Pointed_of_Group G₁ →* Pointed_of_Group G₂ :=
  pmap.mk φ !respect_one

  definition homomorphism_eq (p : group_fun φ ~ group_fun φ') : φ = φ' :=
  begin
    induction φ with φ q, induction φ' with φ' q', esimp at p, induction p,
    exact ap (homomorphism.mk φ) !is_hprop.elim
  end

  /- categorical structure of groups + homomorphisms -/

  definition homomorphism_compose [constructor] (ψ : G₂ →g G₃) (φ : G₁ →g G₂) : G₁ →g G₃ :=
  homomorphism.mk (ψ ∘ φ) (λg h, ap ψ !respect_mul ⬝ !respect_mul)

  definition homomorphism_id [constructor] (G : Group) : G →g G :=
  homomorphism.mk id (λg h, idp)

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
    rewrite [respect_mul, +right_inv φ]
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
