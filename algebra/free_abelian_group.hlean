/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import algebra.group_theory hit.set_quotient types.list types.sum .free_group

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod sum list trunc function equiv trunc_index
     group

namespace group

  variables {G G' : Group} {g g' h h' k : G} {A B : AbGroup}

  variables (X : Type) {Y : Type} [is_set X] [is_set Y] {l l' : list (X ⊎ X)}

  /- Free Abelian Group of a set -/
  namespace free_ab_group

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
    { repeat esimp [map], apply fcg_rel.rflip},
    { rewrite [+map_append], exact resp_append IH₁ IH₂},
    { exact rtrans IH₁ IH₂}
  end

  theorem rel_respect_reverse (r : R X l l') : R X (reverse l) (reverse l') :=
  begin
    induction r with l x x x y l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
    { reflexivity},
    { repeat esimp [map], exact cancel2 x},
    { repeat esimp [map], exact cancel1 x},
    { repeat esimp [map], apply fcg_rel.rflip},
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
  end free_ab_group open free_ab_group

  variables (X)
  definition group_free_ab_group [constructor] : ab_group (fcg_carrier X) :=
  ab_group.mk _ fcg_mul fcg_mul_assoc fcg_one fcg_one_mul fcg_mul_one
           fcg_inv fcg_mul_left_inv fcg_mul_comm

  definition free_ab_group [constructor] : AbGroup :=
  AbGroup.mk _ (group_free_ab_group X)

  /- The universal property of the free commutative group -/
  variables {X A}
  definition free_ab_group_inclusion [constructor] (x : X) : free_ab_group X :=
  class_of [inl x]

  theorem fgh_helper_respect_fcg_rel (f : X → A) (r : fcg_rel X l l')
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

  definition free_ab_group_elim [constructor] (f : X → A) : free_ab_group X →g A :=
  begin
    fapply homomorphism.mk,
    { intro g, refine set_quotient.elim _ _ g,
      { intro l, exact foldl (fgh_helper f) 1 l},
      { intro l l' r, esimp at *, refine trunc.rec _ r, clear r, intro r,
        exact fgh_helper_respect_fcg_rel f r 1}},
    { refine set_quotient.rec_prop _, intro l, refine set_quotient.rec_prop _, intro l',
      esimp, refine !foldl_append ⬝ _, esimp, apply fgh_helper_mul}
  end

  definition fn_of_free_ab_group_elim [unfold_full] (φ : free_ab_group X →g A) : X → A :=
  φ ∘ free_ab_group_inclusion

  definition free_ab_group_elim_unique [constructor] (f : X → A) (k : free_ab_group X →g A)
    (H : k ∘ free_ab_group_inclusion ~ f) : k ~ free_ab_group_elim f :=
  begin
    refine set_quotient.rec_prop _, intro l, esimp,
      induction l with s l IH,
      { esimp [foldl], exact to_respect_one k},
      { rewrite [foldl_cons, fgh_helper_mul],
        refine to_respect_mul k (class_of [s]) (class_of l) ⬝ _,
        rewrite [IH], apply ap (λx, x * _), induction s: rewrite [▸*, one_mul, -H a],
        apply to_respect_inv }
  end

  variables (X A)
  definition free_ab_group_elim_equiv_fn [constructor] : (free_ab_group X →g A) ≃ (X → A) :=
  begin
    fapply equiv.MK,
    { exact fn_of_free_ab_group_elim},
    { exact free_ab_group_elim},
    { intro f, apply eq_of_homotopy, intro x, esimp, unfold [foldl], apply one_mul},
    { intro k, symmetry, apply homomorphism_eq, apply free_ab_group_elim_unique,
      reflexivity }
  end

  definition free_ab_group_functor (f : X → Y) : free_ab_group X →g free_ab_group Y :=
  free_ab_group_elim (free_ab_group_inclusion ∘ f)

-- set_option pp.all true
--   definition free_ab_group.rec {P : free_ab_group X → Type} [H : Πg, is_prop (P g)]
--     (h₁ : Πx, P (free_ab_group_inclusion x))
--     (h₂ : P 0)
--     (h₃ : Πg h, P g → P h → P (g * h))
--     (h₄ : Πg, P g → P g⁻¹) :
--     Πg, P g :=
--   begin
--     refine @set_quotient.rec_prop _ _ _ H _,
--     refine @set_quotient.rec_prop _ _ _ (λx, !H) _,
--     esimp, intro l, induction l with s l ih,
--       exact h₂,
--     induction s with v v,
--       induction v with i y,
--       exact h₃ _ _ (h₁ i y) ih,
--     induction v with i y,
--     refine h₃ (gqg_map _ _ (class_of [inr ⟨i, y⟩])) _ _ ih,
--     refine transport P _ (h₁ i y⁻¹),
--     refine _ ⬝ !mul_one,
--     refine _ ⬝ ap (mul _) (to_respect_one (dirsum_incl i)),
--     apply gqg_eq_of_rel',
--     apply tr, esimp,
--     refine transport dirsum_rel _ (dirsum_rel.rmk i y⁻¹ y),
--     rewrite [mul.left_inv, mul.assoc],
--     apply ap (mul _),
--     refine _ ⬝ (mul_inv (class_of [inr ⟨i, y⟩]) (ι ⟨i, 1⟩))⁻¹ᵖ,
--     refine ap011 mul _ _,
--   end

end group
