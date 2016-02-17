/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Constructions of groups
-/

import .basic hit.set_quotient types.sigma types.list types.sum

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function
     equiv
namespace group

  /- Subgroups -/

  structure subgroup_rel (G : Group) :=
    (R : G → Prop)
    (Rone : R one)
    (Rmul : Π{g h}, R g → R h → R (g * h))
    (Rinv : Π{g}, R g → R (g⁻¹))

  structure normal_subgroup_rel (G : Group) extends subgroup_rel G :=
    (is_normal : Π{g} h, R g → R (h * g * h⁻¹))

  attribute subgroup_rel.R [coercion]
  abbreviation subgroup_to_rel      [unfold 2] := @subgroup_rel.R
  abbreviation subgroup_has_one     [unfold 2] := @subgroup_rel.Rone
  abbreviation subgroup_respect_mul [unfold 2] := @subgroup_rel.Rmul
  abbreviation subgroup_respect_inv [unfold 2] := @subgroup_rel.Rinv
  abbreviation is_normal_subgroup   [unfold 2] := @normal_subgroup_rel.is_normal

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : CommGroup}

  theorem is_normal_subgroup' (h : G) (r : N g) : N (h⁻¹ * g * h) :=
  inv_inv h ▸ is_normal_subgroup N h⁻¹ r

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

  theorem subgroup_mul_comm {G : CommGroup} {H : subgroup_rel G} (g h : sg H)
    : g * h = h * g :=
  subtype_eq !mul.comm

  end

  variable (H)
  definition group_sg [constructor] : group (sg H) :=
  group.mk subgroup_mul _ subgroup_mul_assoc subgroup_one subgroup_one_mul subgroup_mul_one
           subgroup_inv subgroup_mul_left_inv

  definition subgroup [constructor] : Group :=
  Group.mk _ (group_sg H)

  definition comm_group_sg [constructor] {G : CommGroup} (H : subgroup_rel G)
    : comm_group (sg H) :=
  ⦃comm_group, group_sg H, mul_comm := subgroup_mul_comm⦄

  definition comm_subgroup [constructor] {G : CommGroup} (H : subgroup_rel G)
    : CommGroup :=
  CommGroup.mk _ (comm_group_sg H)

  /- Quotient Group -/

  definition quotient_rel (g h : G) : Prop := N (g * h⁻¹)

  variable {N}
  theorem quotient_rel_refl (g : G) : quotient_rel N g g :=
  transport (λx, N x) !mul.right_inv⁻¹ (subgroup_has_one N)
  theorem quotient_rel_symm (r : quotient_rel N g h) : quotient_rel N h g :=
  transport (λx, N x) (!mul_inv ⬝ ap (λx, x * _) !inv_inv) (subgroup_respect_inv N r)

  theorem quotient_rel_trans (r : quotient_rel N g h) (s : quotient_rel N h k)
    : quotient_rel N g k :=
  have H1 : N ((g * h⁻¹) * (h * k⁻¹)), from subgroup_respect_mul N r s,
  have H2 : (g * h⁻¹) * (h * k⁻¹) = g * k⁻¹, from calc
    (g * h⁻¹) * (h * k⁻¹) = ((g * h⁻¹) * h) * k⁻¹ : by rewrite [mul.assoc (g * h⁻¹)]
                      ... = g * k⁻¹               : by rewrite inv_mul_cancel_right,
  show N (g * k⁻¹), from H2 ▸ H1

  theorem quotient_rel_resp_inv (r : quotient_rel N g h) : quotient_rel N g⁻¹ h⁻¹ :=
  have H1 : N (g⁻¹ * (h * g⁻¹) * g), from
    is_normal_subgroup' N g (quotient_rel_symm r),
  have H2 : g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h⁻¹⁻¹, from calc
    g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h * g⁻¹ * g : by rewrite -mul.assoc
                    ... = g⁻¹ * h           : inv_mul_cancel_right
                    ... = g⁻¹ * h⁻¹⁻¹       : by rewrite algebra.inv_inv,
  show N (g⁻¹ * h⁻¹⁻¹), from H2 ▸ H1

  theorem quotient_rel_resp_mul (r : quotient_rel N g h) (r' : quotient_rel N g' h')
    : quotient_rel N (g * g') (h * h') :=
  have H1 : N (g * ((g' * h'⁻¹) * h⁻¹)), from
    normal_subgroup_insert N r' r,
  have H2 : g * ((g' * h'⁻¹) * h⁻¹) = (g * g') * (h * h')⁻¹, from calc
    g * ((g' * h'⁻¹) * h⁻¹) = g * (g' * (h'⁻¹ * h⁻¹)) : by rewrite [mul.assoc]
                        ... = (g * g') * (h'⁻¹ * h⁻¹) : mul.assoc
                        ... = (g * g') * (h * h')⁻¹ : by rewrite [mul_inv],
  show N ((g * g') * (h * h')⁻¹), from H2 ▸ H1

  theorem is_equivalence_quotient_rel : is_equivalence (quotient_rel N) :=
  is_equivalence.mk quotient_rel_refl
                    (λg h, quotient_rel_symm)
                    (λg h k, quotient_rel_trans)

  local attribute is_equivalence_quotient_rel [instance]
  variable (N)
  definition qg : Type := set_quotient (quotient_rel N)
  variable {N}
  local attribute qg [reducible]

  definition quotient_one [constructor] : qg N := class_of one
  definition quotient_inv [unfold 3] : qg N → qg N :=
  quotient_unary_map has_inv.inv (λg g' r, quotient_rel_resp_inv r)
  definition quotient_mul [unfold 3 4] : qg N → qg N → qg N :=
  quotient_binary_map has_mul.mul (λg g' r h h' r', quotient_rel_resp_mul r r')

  section
  local notation 1 := quotient_one
  local postfix ⁻¹ := quotient_inv
  local infix * := quotient_mul

  theorem quotient_mul_assoc (g₁ g₂ g₃ : qg N) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    refine set_quotient.rec_prop _ g₁,
    refine set_quotient.rec_prop _ g₂,
    refine set_quotient.rec_prop _ g₃,
    clear g₁ g₂ g₃, intro g₁ g₂ g₃,
    exact ap class_of !mul.assoc
  end

  theorem quotient_one_mul (g : qg N) : 1 * g = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !one_mul
  end

  theorem quotient_mul_one (g : qg N) : g * 1 = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !mul_one
  end

  theorem quotient_mul_left_inv (g : qg N) : g⁻¹ * g = 1 :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !mul.left_inv
  end

  theorem quotient_mul_comm {G : CommGroup} {N : normal_subgroup_rel G} (g h : qg N)
    : g * h = h * g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    refine set_quotient.rec_prop _ h, clear h, intro h,
    apply ap class_of, esimp, apply mul.comm
  end

  end

  variable (N)
  definition group_qg [constructor] : group (qg N) :=
  group.mk quotient_mul _ quotient_mul_assoc quotient_one quotient_one_mul quotient_mul_one
           quotient_inv quotient_mul_left_inv

  definition quotient_group [constructor] : Group :=
  Group.mk _ (group_qg N)

  definition comm_group_qg [constructor] {G : CommGroup} (N : normal_subgroup_rel G)
    : comm_group (qg N) :=
  ⦃comm_group, group_qg N, mul_comm := quotient_mul_comm⦄

  definition quotient_comm_group [constructor] {G : CommGroup} (N : normal_subgroup_rel G)
    : CommGroup :=
  CommGroup.mk _ (comm_group_qg N)

  /- Binary products (direct sums) of Groups -/
  definition product_one [constructor] : G × G' := (one, one)
  definition product_inv [unfold 3] : G × G' → G × G' :=
  λv, (v.1⁻¹, v.2⁻¹)
  definition product_mul [unfold 3 4] : G × G' → G × G' → G × G' :=
  λv w, (v.1 * w.1, v.2 * w.2)

  section
  local notation 1 := product_one
  local postfix ⁻¹ := product_inv
  local infix * := product_mul

  theorem product_mul_assoc (g₁ g₂ g₃ : G × G') : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  prod_eq !mul.assoc !mul.assoc

  theorem product_one_mul (g : G × G') : 1 * g = g :=
  prod_eq !one_mul !one_mul

  theorem product_mul_one (g : G × G') : g * 1 = g :=
  prod_eq !mul_one !mul_one

  theorem product_mul_left_inv (g : G × G') : g⁻¹ * g = 1 :=
  prod_eq !mul.left_inv !mul.left_inv

  theorem product_mul_comm {G G' : CommGroup} (g h : G × G') : g * h = h * g :=
  prod_eq !mul.comm !mul.comm

  end

  variables (G G')
  definition group_prod [constructor] : group (G × G') :=
  group.mk product_mul _ product_mul_assoc product_one product_one_mul product_mul_one
           product_inv product_mul_left_inv

  definition product [constructor] : Group :=
  Group.mk _ (group_prod G G')

  definition comm_group_prod [constructor] (G G' : CommGroup) : comm_group (G × G') :=
  ⦃comm_group, group_prod G G', mul_comm := product_mul_comm⦄

  definition comm_product [constructor] (G G' : CommGroup) : CommGroup :=
  CommGroup.mk _ (comm_group_prod G G')

  infix ` ×g `:30 := group.product

  /- Free Group of a set -/
  variables (X : Set) {l l' : list (X ⊎ X)}
  namespace free_group

  inductive free_group_rel : list (X ⊎ X) → list (X ⊎ X) → Type :=
  | rrefl   : Πl, free_group_rel l l
  | cancel1 : Πx, free_group_rel [inl x, inr x] []
  | cancel2 : Πx, free_group_rel [inr x, inl x] []
  | resp_append : Π{l₁ l₂ l₃ l₄}, free_group_rel l₁ l₂ → free_group_rel l₃ l₄ →
                             free_group_rel (l₁ ++ l₃) (l₂ ++ l₄)
  | rtrans : Π{l₁ l₂ l₃}, free_group_rel l₁ l₂ → free_group_rel l₂ l₃ →
                             free_group_rel l₁ l₃

  open free_group_rel
  local abbreviation R [reducible] := free_group_rel
  attribute free_group_rel.rrefl [refl]

  definition free_group_carrier [reducible] : Type := set_quotient (λx y, ∥R X x y∥)
  local abbreviation FG := free_group_carrier

  definition is_reflexive_R : is_reflexive (λx y, ∥R X x y∥) :=
  begin constructor, intro s, apply tr, unfold R end
  local attribute is_reflexive_R [instance]

  variable {X}
  theorem rel_respect_flip (r : R X l l') : R X (map sum.flip l) (map sum.flip l') :=
  begin
    induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
    { reflexivity},
    { repeat esimp [map], exact cancel2 x},
    { repeat esimp [map], exact cancel1 x},
    { rewrite [+map_append], exact resp_append IH₁ IH₂},
    { exact rtrans IH₁ IH₂}
  end

  theorem rel_respect_reverse (r : R X l l') : R X (reverse l) (reverse l') :=
  begin
    induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
    { reflexivity},
    { repeat esimp [map], exact cancel2 x},
    { repeat esimp [map], exact cancel1 x},
    { rewrite [+reverse_append], exact resp_append IH₂ IH₁},
    { exact rtrans IH₁ IH₂}
  end

  definition free_group_one [constructor] : FG X := class_of []
  definition free_group_inv [unfold 3] : FG X → FG X :=
  quotient_unary_map (reverse ∘ map sum.flip)
                     (λl l', trunc_functor -1 (rel_respect_reverse ∘ rel_respect_flip))
  definition free_group_mul [unfold 3 4] : FG X → FG X → FG X :=
  quotient_binary_map append (λl l', trunc.elim (λr m m', trunc.elim (λs, tr (resp_append r s))))

  section
  local notation 1 := free_group_one
  local postfix ⁻¹ := free_group_inv
  local infix * := free_group_mul

  theorem free_group_mul_assoc (g₁ g₂ g₃ : FG X) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    refine set_quotient.rec_prop _ g₁,
    refine set_quotient.rec_prop _ g₂,
    refine set_quotient.rec_prop _ g₃,
    clear g₁ g₂ g₃, intro g₁ g₂ g₃,
    exact ap class_of !append.assoc
  end

  theorem free_group_one_mul (g : FG X) : 1 * g = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !append_nil_left
  end

  theorem free_group_mul_one (g : FG X) : g * 1 = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !append_nil_right
  end

  theorem free_group_mul_left_inv (g : FG X) : g⁻¹ * g = 1 :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    apply eq_of_rel, apply tr,
    induction g with s l IH,
    { reflexivity},
    { rewrite [▸*, map_cons, reverse_cons, concat_append],
      refine rtrans _ IH,
      apply resp_append, reflexivity,
      change R X ([flip s, s] ++ l) ([] ++ l),
      apply resp_append,
        induction s, apply cancel2, apply cancel1,
        reflexivity}
  end

  end
  end free_group open free_group
--  export [reduce_hints] free_group
  variables (X)
  definition group_free_group [constructor] : group (free_group_carrier X) :=
  group.mk free_group_mul _ free_group_mul_assoc free_group_one free_group_one_mul free_group_mul_one
           free_group_inv free_group_mul_left_inv

  definition free_group [constructor] : Group :=
  Group.mk _ (group_free_group X)

  /- The universal property of the free group -/
  variables {X G}
  definition free_group_inclusion [constructor] (x : X) : free_group X :=
  class_of [inl x]

  definition fgh_helper [unfold 5] (f : X → G) (g : G) (x : X + X) : G :=
  g * sum.rec (λx, f x) (λx, (f x)⁻¹) x

  theorem fgh_helper_respect_rel (f : X → G) (r : free_group_rel X l l')
    : Π(g : G), foldl (fgh_helper f) g l = foldl (fgh_helper f) g l' :=
  begin
    induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂: intro g,
    { reflexivity},
    { unfold [foldl], apply mul_inv_cancel_right},
    { unfold [foldl], apply inv_mul_cancel_right},
    { rewrite [+foldl_append, IH₁, IH₂]},
    { exact !IH₁ ⬝ !IH₂}
  end

  theorem fgh_helper_mul (f : X → G) (l)
    : Π(g : G), foldl (fgh_helper f) g l = g * foldl (fgh_helper f) 1 l :=
  begin
    induction l with s l IH: intro g,
    { unfold [foldl], exact !mul_one⁻¹},
    { rewrite [+foldl_cons, IH], refine _ ⬝ (ap (λx, g * x) !IH⁻¹),
      rewrite [-mul.assoc, ↑fgh_helper, one_mul]}
  end

  definition free_group_hom [constructor] (f : X → G) : free_group X →g G :=
  begin
    fapply homomorphism.mk,
    { intro g, refine set_quotient.elim _ _ g,
      { intro l, exact foldl (fgh_helper f) 1 l},
      { intro l l' r, esimp at *, refine trunc.rec _ r, clear r, intro r,
        exact fgh_helper_respect_rel f r 1}},
    { refine set_quotient.rec_prop _, intro l, refine set_quotient.rec_prop _, intro l',
      esimp, refine !foldl_append ⬝ _, esimp, apply fgh_helper_mul}
  end

  definition fn_of_free_group_hom [unfold_full] (φ : free_group X →g G) : X → G :=
  φ ∘ free_group_inclusion

  variables (X G)
  definition free_group_hom_equiv_fn : (free_group X →g G) ≃ (X → G) :=
  begin
    fapply equiv.MK,
    { exact fn_of_free_group_hom},
    { exact free_group_hom},
    { intro f, apply eq_of_homotopy, intro x, esimp, unfold [foldl], apply one_mul},
    { intro φ, apply homomorphism_eq, refine set_quotient.rec_prop _, intro l, esimp,
      induction l with s l IH,
      { esimp [foldl], exact (respect_one φ)⁻¹},
      { rewrite [foldl_cons, fgh_helper_mul],
        refine _ ⬝ (respect_mul φ (class_of [s]) (class_of l))⁻¹,
        rewrite [IH], induction s: rewrite [▸*, one_mul], rewrite [-respect_inv φ]}}
  end

  /- Free Commutative Group of a set -/
  namespace free_comm_group

  inductive fcg_rel : list (X ⊎ X) → list (X ⊎ X) → Type :=
  | rrefl   : Πl, fcg_rel l l
  | cancel1 : Πx, fcg_rel [inl x, inr x] []
  | cancel2 : Πx, fcg_rel [inr x, inl x] []
  | rflip   : Πx y, fcg_rel [x, y] [y, x]
  | resp_append : Π{l₁ l₂ l₃ l₄}, fcg_rel l₁ l₂ → fcg_rel l₃ l₄ →
                             fcg_rel (l₁ ++ l₃) (l₂ ++ l₄)
  | rtrans : Π{l₁ l₂ l₃}, fcg_rel l₁ l₂ → fcg_rel l₂ l₃ →
                             fcg_rel l₁ l₃

  open fcg_rel
  local abbreviation R [reducible] := fcg_rel
  attribute fcg_rel.rrefl [refl]
  attribute fcg_rel.rtrans [trans]

  definition fcg_carrier [reducible] : Type := set_quotient (λx y, ∥R X x y∥)
  local abbreviation FG := fcg_carrier

  definition is_reflexive_R : is_reflexive (λx y, ∥R X x y∥) :=
  begin constructor, intro s, apply tr, unfold R end
  local attribute is_reflexive_R [instance]

  variable {X}
  theorem rel_respect_flip (r : R X l l') : R X (map sum.flip l) (map sum.flip l') :=
  begin
    induction r with l x x x y l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
    { reflexivity},
    { repeat esimp [map], exact cancel2 x},
    { repeat esimp [map], exact cancel1 x},
    { repeat esimp [map], apply rflip},
    { rewrite [+map_append], exact resp_append IH₁ IH₂},
    { exact rtrans IH₁ IH₂}
  end

  theorem rel_respect_reverse (r : R X l l') : R X (reverse l) (reverse l') :=
  begin
    induction r with l x x x y l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
    { reflexivity},
    { repeat esimp [map], exact cancel2 x},
    { repeat esimp [map], exact cancel1 x},
    { repeat esimp [map], apply rflip},
    { rewrite [+reverse_append], exact resp_append IH₂ IH₁},
    { exact rtrans IH₁ IH₂}
  end

  theorem rel_cons_concat (l s) : R X (s :: l) (concat s l) :=
  begin
    induction l with t l IH,
    { reflexivity},
    { rewrite [concat_cons], transitivity (t :: s :: l),
      { exact resp_append !rflip !rrefl},
      { exact resp_append (rrefl [t]) IH}}
  end

  definition fcg_one [constructor] : FG X := class_of []
  definition fcg_inv [unfold 3] : FG X → FG X :=
  quotient_unary_map (reverse ∘ map sum.flip)
                     (λl l', trunc_functor -1 (rel_respect_reverse ∘ rel_respect_flip))
  definition fcg_mul [unfold 3 4] : FG X → FG X → FG X :=
  quotient_binary_map append (λl l', trunc.elim (λr m m', trunc.elim (λs, tr (resp_append r s))))

  section
  local notation 1 := fcg_one
  local postfix ⁻¹ := fcg_inv
  local infix * := fcg_mul

  theorem fcg_mul_assoc (g₁ g₂ g₃ : FG X) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    refine set_quotient.rec_prop _ g₁,
    refine set_quotient.rec_prop _ g₂,
    refine set_quotient.rec_prop _ g₃,
    clear g₁ g₂ g₃, intro g₁ g₂ g₃,
    exact ap class_of !append.assoc
  end

  theorem fcg_one_mul (g : FG X) : 1 * g = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !append_nil_left
  end

  theorem fcg_mul_one (g : FG X) : g * 1 = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !append_nil_right
  end

  theorem fcg_mul_left_inv (g : FG X) : g⁻¹ * g = 1 :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    apply eq_of_rel, apply tr,
    induction g with s l IH,
    { reflexivity},
    { rewrite [▸*, map_cons, reverse_cons, concat_append],
      refine rtrans _ IH,
      apply resp_append, reflexivity,
      change R X ([flip s, s] ++ l) ([] ++ l),
      apply resp_append,
        induction s, apply cancel2, apply cancel1,
        reflexivity}
  end

  theorem fcg_mul_comm (g h : FG X) : g * h = h * g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    refine set_quotient.rec_prop _ h, clear h, intro h,
    apply eq_of_rel, apply tr,
    revert h, induction g with s l IH: intro h,
    { rewrite [append_nil_left, append_nil_right]},
    { rewrite [append_cons,-concat_append],
      transitivity concat s (l ++ h), apply rel_cons_concat,
      rewrite [-append_concat], apply IH}
  end
  end
  end free_comm_group open free_comm_group

  variables (X)
  definition group_free_comm_group [constructor] : comm_group (fcg_carrier X) :=
  comm_group.mk fcg_mul _ fcg_mul_assoc fcg_one fcg_one_mul fcg_mul_one
           fcg_inv fcg_mul_left_inv fcg_mul_comm

  definition free_comm_group [constructor] : CommGroup :=
  CommGroup.mk _ (group_free_comm_group X)

  /- The universal property of the free commutative group -/
  variables {X A}
  definition free_comm_group_inclusion [constructor] (x : X) : free_comm_group X :=
  class_of [inl x]

  theorem fgh_helper_respect_comm_rel (f : X → A) (r : fcg_rel X l l')
    : Π(g : A), foldl (fgh_helper f) g l = foldl (fgh_helper f) g l' :=
  begin
    induction r with l x x x y l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂: intro g,
    { reflexivity},
    { unfold [foldl], apply mul_inv_cancel_right},
    { unfold [foldl], apply inv_mul_cancel_right},
    { unfold [foldl, fgh_helper], apply mul.right_comm},
    { rewrite [+foldl_append, IH₁, IH₂]},
    { exact !IH₁ ⬝ !IH₂}
  end

  definition free_comm_group_hom [constructor] (f : X → A) : free_comm_group X →g A :=
  begin
    fapply homomorphism.mk,
    { intro g, refine set_quotient.elim _ _ g,
      { intro l, exact foldl (fgh_helper f) 1 l},
      { intro l l' r, esimp at *, refine trunc.rec _ r, clear r, intro r,
        exact fgh_helper_respect_comm_rel f r 1}},
    { refine set_quotient.rec_prop _, intro l, refine set_quotient.rec_prop _, intro l',
      esimp, refine !foldl_append ⬝ _, esimp, apply fgh_helper_mul}
  end

  definition fn_of_free_comm_group_hom [unfold_full] (φ : free_comm_group X →g A) : X → A :=
  φ ∘ free_comm_group_inclusion

  variables (X A)
  definition free_comm_group_hom_equiv_fn : (free_comm_group X →g A) ≃ (X → A) :=
  begin
    fapply equiv.MK,
    { exact fn_of_free_comm_group_hom},
    { exact free_comm_group_hom},
    { intro f, apply eq_of_homotopy, intro x, esimp, unfold [foldl], apply one_mul},
    { intro φ, apply homomorphism_eq, refine set_quotient.rec_prop _, intro l, esimp,
      induction l with s l IH,
      { esimp [foldl], symmetry, exact to_respect_one φ},
      { rewrite [foldl_cons, fgh_helper_mul],
        refine _ ⬝ (to_respect_mul φ (class_of [s]) (class_of l))⁻¹,
        rewrite [▸*,IH], induction s: rewrite [▸*, one_mul], apply ap (λx, x * _),
        exact !to_respect_inv⁻¹}}
  end

  /- Free Commutative Group of a set -/

/-  namespace tensor_group
  variables {A B}
  local abbreviation ι := @free_comm_group_inclusion

  inductive tensor_rel_type : free_comm_group (Set_of_Group A ×t Set_of_Group B) → Type :=
  | mul_left  : Π(a₁ a₂ : A) (b : B), tensor_rel_type (ι (a₁, b)  * ι (a₂, b)  * (ι (a₁ * a₂, b))⁻¹)
  | mul_right : Π(a : A) (b₁ b₂ : B), tensor_rel_type (ι (a, b₁)  * ι (a, b₂)  * (ι (a, b₁ * b₂))⁻¹)

  open tensor_rel_type

  definition tensor_rel' (x : free_comm_group (Set_of_Group A ×t Set_of_Group B)) : Prop :=
  ∥ tensor_rel_type x ∥

  definition tensor_group_rel (A B : CommGroup)
    : normal_subgroup_rel (free_comm_group (Set_of_Group A ×t Set_of_Group B)) :=
  sorry /- relation generated by tensor_rel'-/

  definition tensor_group [constructor] : CommGroup :=
  quotient_comm_group (tensor_group_rel A B)

  end tensor_group-/

  section kernels

  variables {G₁ G₂ : Group}

  -- TODO: maybe define this in more generality for pointed types?
  definition kernel [constructor] (φ : G₁ →g G₂) (g : G₁) : Prop := trunctype.mk (φ g = 1) _

  theorem kernel_mul (φ : G₁ →g G₂) (g h : G₁) (H₁ : kernel φ g) (H₂ : kernel φ h) : kernel φ (g *[G₁] h) :=
  begin
    esimp at *,
    exact calc
      φ (g * h) = (φ g) * (φ h) : to_respect_mul
            ... = 1 * (φ h)     : H₁
            ... = 1 * 1         : H₂
            ... = 1             : one_mul
  end

  theorem kernel_inv (φ : G₁ →g G₂) (g : G₁) (H : kernel φ g) : kernel φ (g⁻¹) :=
  begin
    esimp at *,
    exact calc
      φ g⁻¹ = (φ g)⁻¹ : to_respect_inv
        ... = 1⁻¹     : H
        ... = 1       : one_inv
  end

  definition subgroup_kernel [constructor] (φ : G₁ →g G₂) : subgroup_rel G₁ :=
  ⦃ subgroup_rel,
    R := kernel φ,
    Rone := respect_one φ,
    Rmul := kernel_mul φ,
    Rinv := kernel_inv φ
  ⦄

  theorem is_normal_subgroup_kernel (φ : G₁ →g G₂) (g : G₁) (h : G₁)
    : kernel φ g → kernel φ (h * g * h⁻¹) :=
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

  definition normal_subgroup_kernel [constructor] (φ : G₁ →g G₂) : normal_subgroup_rel G₁ :=
  ⦃ normal_subgroup_rel,
    subgroup_kernel φ,
    is_normal := is_normal_subgroup_kernel φ
  ⦄

  end kernels

end group
