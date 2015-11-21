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

import algebra.group types.pointed types.pi

open eq algebra pointed function is_trunc pi

namespace group

  definition pointed_Group [instance] (G : Group) : pointed G := pointed.mk one
  definition Pointed_of_Group (G : Group) : Type* := pointed.mk' G

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

  variables {G₁ G₂ G₃ : Group} {g h : G₁} {ψ : G₂ →g G₃} {φ φ' : G₁ →g G₂}

  theorem respect_one (φ : G₁ →g G₂) : φ 1 = 1 :=
  mul.right_cancel
    (calc
      φ 1 * φ 1 = φ (1 * 1) : respect_mul
            ... = φ 1 : ap φ !one_mul
            ... = 1 * φ 1 : one_mul)

  theorem respect_inv (φ : G₁ →g G₂) (g : G₁) : φ g⁻¹ = (φ g)⁻¹ :=
  eq_inv_of_mul_eq_one (!respect_mul⁻¹ ⬝ ap φ !mul.left_inv ⬝ !respect_one)

  local attribute Pointed_of_Group [coercion]
  definition pmap_of_homomorphism [constructor] (φ : G₁ →g G₂) : G₁ →* G₂ :=
  pmap.mk φ !respect_one

  definition homomorphism_eq (p : group_fun φ ~ group_fun φ') : φ = φ' :=
  begin
    induction φ with φ q, induction φ' with φ' q', esimp at p, induction p,
    exact ap (homomorphism.mk φ) !is_hprop.elim
  end

  /- categorical structure of groups + homomorphisms -/

  definition homomorphism_compose [constructor] (ψ : G₂ →g G₃) (φ : G₁ →g G₂) : G₁ → G₃ :=
  homomorphism.mk (ψ ∘ φ) (λg h, ap ψ !respect_mul ⬝ !respect_mul)

  definition homomorphism_id [constructor] (G : Group) : G → G :=
  homomorphism.mk id (λg h, idp)

  -- TODO: maybe define this in more generality for pointed types?
  definition kernel [constructor] (φ : G₁ →g G₂) (g : G₁) : hprop := trunctype.mk (φ g = 1) _


end group
