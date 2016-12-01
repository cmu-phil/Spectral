/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import algebra.group_theory hit.set_quotient types.list types.sum

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod sum list trunc function equiv

namespace group

  variables {G G' : Group} {g g' h h' k : G} {A B : AbGroup}

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

  end group
