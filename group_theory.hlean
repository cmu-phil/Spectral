/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Basic group theory
-/

import algebra.group hit.set_quotient

open eq algebra is_trunc set_quotient relation

namespace group

  definition Group_of_CommGroup [coercion] [constructor] (G : CommGroup) : Group :=
  Group.mk G _

  structure subgroup (G : Group) :=
    (R : G → hprop)
    (Rone : R one)
    (Rmul : Π{g h}, R g → R h → R (g * h))
    (Rinv : Π{g}, R g → R (g⁻¹))

  structure normal_subgroup (G : Group) extends subgroup G :=
    (is_normal : Π{g} h, R g → R (h * g * h⁻¹))

  attribute subgroup.R [coercion]
  abbreviation subgroup_rel         [unfold 2] := @subgroup.R
  abbreviation subgroup_has_one     [unfold 2] := @subgroup.Rone
  abbreviation subgroup_respect_mul [unfold 2] := @subgroup.Rmul
  abbreviation subgroup_respect_inv [unfold 2] := @subgroup.Rinv
  abbreviation is_normal_subgroup   [unfold 2] := @normal_subgroup.is_normal

  variables {G : Group} (R : normal_subgroup G) {g g' h h' k : G}

  theorem is_normal_subgroup' (h : G) (r : R g) : R (h⁻¹ * g * h) :=
  inv_inv h ▸ is_normal_subgroup R h⁻¹ r

  theorem is_normal_subgroup_rev (h : G) (r : R (h * g * h⁻¹)) : R g :=
  have H : h⁻¹ * (h * g * h⁻¹) * h = g, from calc
    h⁻¹ * (h * g * h⁻¹) * h = h⁻¹ * (h * g) * h⁻¹ * h : by rewrite [-mul.assoc h⁻¹]
                        ... = h⁻¹ * (h * g)           : by rewrite [inv_mul_cancel_right]
                        ... = g                       : inv_mul_cancel_left,
  H ▸ is_normal_subgroup' R h r

  theorem is_normal_subgroup_rev' (h : G) (r : R (h⁻¹ * g * h)) : R g :=
  is_normal_subgroup_rev R h⁻¹ ((inv_inv h)⁻¹ ▸ r)

  theorem normal_subgroup_insert (r : R k) (r' : R (g * h)) : R (g * (k * h)) :=
  have H1 : R ((g * h) * (h⁻¹ * k * h)), from
    subgroup_respect_mul R r' (is_normal_subgroup' R h r),
  have H2 : (g * h) * (h⁻¹ * k * h) = g * (k * h), from calc
    (g * h) * (h⁻¹ * k * h) = g * (h * (h⁻¹ * k * h))   : mul.assoc
                        ... = g * (h * (h⁻¹ * (k * h))) : by rewrite [mul.assoc h⁻¹]
                        ... = g * (k * h)               : by rewrite [mul_inv_cancel_left],
  show R (g * (k * h)), from H2 ▸ H1

  definition quotient_rel (g h : G) : hprop := R (g * h⁻¹)

  variable {R}
  theorem quotient_rel_refl (g : G) : quotient_rel R g g :=
  transport (λx, R x) !mul.right_inv⁻¹ (subgroup_has_one R)
  theorem quotient_rel_symm (r : quotient_rel R g h) : quotient_rel R h g :=
  transport (λx, R x) (!mul_inv ⬝ ap (λx, x * _) !inv_inv) (subgroup_respect_inv R r)

  theorem quotient_rel_trans (r : quotient_rel R g h) (s : quotient_rel R h k)
    : quotient_rel R g k :=
  have H1 : R ((g * h⁻¹) * (h * k⁻¹)), from subgroup_respect_mul R r s,
  have H2 : (g * h⁻¹) * (h * k⁻¹) = g * k⁻¹, from calc
    (g * h⁻¹) * (h * k⁻¹) = ((g * h⁻¹) * h) * k⁻¹ : by rewrite [mul.assoc (g * h⁻¹)]
                      ... = g * k⁻¹               : by rewrite inv_mul_cancel_right,
  show R (g * k⁻¹), from H2 ▸ H1

  theorem quotient_rel_resp_inv (r : quotient_rel R g h) : quotient_rel R g⁻¹ h⁻¹ :=
  have H1 : R (g⁻¹ * (h * g⁻¹) * g), from
    is_normal_subgroup' R g (quotient_rel_symm r),
  have H2 : g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h⁻¹⁻¹, from calc
    g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h * g⁻¹ * g : by rewrite -mul.assoc
                    ... = g⁻¹ * h           : inv_mul_cancel_right
                    ... = g⁻¹ * h⁻¹⁻¹       : by rewrite algebra.inv_inv,
  show R (g⁻¹ * h⁻¹⁻¹), from H2 ▸ H1

  theorem quotient_rel_resp_mul (r : quotient_rel R g h) (r' : quotient_rel R g' h')
    : quotient_rel R (g * g') (h * h') :=
  have H1 : R (g * ((g' * h'⁻¹) * h⁻¹)), from
    normal_subgroup_insert R r' r,
  have H2 : g * ((g' * h'⁻¹) * h⁻¹) = (g * g') * (h * h')⁻¹, from calc
    g * ((g' * h'⁻¹) * h⁻¹) = g * (g' * (h'⁻¹ * h⁻¹)) : by rewrite [mul.assoc]
                        ... = (g * g') * (h'⁻¹ * h⁻¹) : mul.assoc
                        ... = (g * g') * (h * h')⁻¹ : by rewrite [mul_inv],
  show R ((g * g') * (h * h')⁻¹), from H2 ▸ H1

  theorem is_equivalence_quotient_rel : is_equivalence (quotient_rel R) :=
  is_equivalence.mk quotient_rel_refl
                    (λg h, quotient_rel_symm)
                    (λg h k, quotient_rel_trans)

  local attribute is_equivalence_quotient_rel [instance]
  variable (R)
  definition qg : Type := set_quotient (quotient_rel R)
  variable {R}
  local attribute qg [reducible]

  definition quotient_one [constructor] : qg R := class_of one
  definition quotient_inv [unfold 3] : qg R → qg R :=
  quotient_unary_map has_inv.inv (λg g' r, quotient_rel_resp_inv r)
  definition quotient_mul [unfold 3 4] : qg R → qg R → qg R :=
  quotient_binary_map has_mul.mul (λg g' r h h' r', quotient_rel_resp_mul r r')

  section
  local notation 1 := quotient_one
  local postfix ⁻¹ := quotient_inv
  local infix * := quotient_mul

  theorem quotient_mul_assoc (g₁ g₂ g₃ : qg R) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    refine set_quotient.rec_hprop _ g₁,
    refine set_quotient.rec_hprop _ g₂,
    refine set_quotient.rec_hprop _ g₃,
    clear g₁ g₂ g₃, intro g₁ g₂ g₃,
    exact ap class_of !mul.assoc
  end

  theorem quotient_one_mul (g : qg R) : 1 * g = g :=
  begin
    refine set_quotient.rec_hprop _ g, clear g, intro g,
    exact ap class_of !one_mul
  end

  theorem quotient_mul_one (g : qg R) : g * 1 = g :=
  begin
    refine set_quotient.rec_hprop _ g, clear g, intro g,
    exact ap class_of !mul_one
  end

  theorem quotient_mul_left_inv (g : qg R) : g⁻¹ * g = 1 :=
  begin
    refine set_quotient.rec_hprop _ g, clear g, intro g,
    exact ap class_of !mul.left_inv
  end

  theorem quotient_mul_comm {G : CommGroup} {R : normal_subgroup G} (g h : qg R)
    : g * h = h * g :=
  begin
    refine set_quotient.rec_hprop _ g, clear g, intro g,
    refine set_quotient.rec_hprop _ h, clear h, intro h,
    apply ap class_of, esimp, apply mul.comm
  end

  end

  variable (R)
  definition group_qg [constructor] : group (qg R) :=
  group.mk quotient_mul _ quotient_mul_assoc quotient_one quotient_one_mul quotient_mul_one
           quotient_inv quotient_mul_left_inv

  definition quotient_group [constructor] : Group :=
  Group.mk _ (group_qg R)

  definition comm_group_qg [constructor] {G : CommGroup} (R : normal_subgroup G)
    : comm_group (qg R) :=
  ⦃comm_group, group_qg R, mul_comm := quotient_mul_comm⦄

  definition quotient_comm_group [constructor] {G : CommGroup} (R : normal_subgroup G)
    : CommGroup :=
  CommGroup.mk _ (comm_group_qg R)

end group
