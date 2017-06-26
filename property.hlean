/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import types.trunc .logic
open funext eq trunc is_trunc logic

definition property (X : Type) := X → Prop

namespace property

variable {X : Type}

/- membership and subproperty -/

definition mem (x : X) (a : property X) := a x
infix ∈ := mem
notation a ∉ b := ¬ mem a b

/-theorem ext {a b : property X} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
eq_of_homotopy (take x, propext (H x))
-/

definition subproperty (a b : property X) : Prop := Prop.mk (∀⦃x⦄, x ∈ a → x ∈ b) _
infix ⊆ := subproperty

definition superproperty (s t : property X) : Prop := t ⊆ s
infix ⊇ := superproperty

theorem subproperty.refl (a : property X) : a ⊆ a := take x, assume H, H

theorem subproperty.trans {a b c : property X} (subab : a ⊆ b) (subbc : b ⊆ c) : a ⊆ c :=
take x, assume ax, subbc (subab ax)

/-
theorem subproperty.antisymm {a b : property X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))
-/

-- an alterantive name
/-
theorem eq_of_subproperty_of_subproperty {a b : property X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subproperty.antisymm h₁ h₂
-/

theorem mem_of_subproperty_of_mem {s₁ s₂ : property X} {a : X} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ _ h₂

/- empty property -/

definition empty : property X := λx, false
notation `∅` := property.empty

theorem not_mem_empty (x : X) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, false.elim H

theorem mem_empty_eq (x : X) : x ∈ ∅ = false := rfl

/-
theorem eq_empty_of_forall_not_mem {s : property X} (H : ∀ x, x ∉ s) : s = ∅ :=
ext (take x, iff.intro
  (assume xs, absurd xs (H x))
  (assume xe, absurd xe (not_mem_empty x)))
-/

theorem ne_empty_of_mem {s : property X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
  begin intro Hs, rewrite Hs at H, apply not_mem_empty x H end

theorem empty_subproperty (s : property X) : ∅ ⊆ s :=
take x, assume H, false.elim H

/-theorem eq_empty_of_subproperty_empty {s : property X} (H : s ⊆ ∅) : s = ∅ :=
subproperty.antisymm H (empty_subproperty s)

theorem subproperty_empty_iff (s : property X) : s ⊆ ∅ ↔ s = ∅ :=
iff.intro eq_empty_of_subproperty_empty (take xeq, by rewrite xeq; apply subproperty.refl ∅)
-/

/- universal property -/

definition univ : property X := λx, true

theorem mem_univ (x : X) : x ∈ univ := trivial

theorem mem_univ_eq (x : X) : x ∈ univ = true := rfl

theorem empty_ne_univ [h : inhabited X] : (empty : property X) ≠ univ :=
assume H : empty = univ,
absurd (mem_univ (inhabited.value h)) (eq.rec_on H (not_mem_empty (arbitrary X)))

theorem subproperty_univ (s : property X) : s ⊆ univ := λ x H, trivial

/-
theorem eq_univ_of_univ_subproperty {s : property X} (H : univ ⊆ s) : s = univ :=
eq_of_subproperty_of_subproperty (subproperty_univ s) H
-/

/-
theorem eq_univ_of_forall {s : property X} (H : ∀ x, x ∈ s) : s = univ :=
ext (take x, iff.intro (assume H', trivial) (assume H', H x))
-/

/- property-builder notation -/

-- {x : X | P}
definition property_of (P : X → Prop) : property X := P
notation `{` binder ` | ` r:(scoped:1 P, property_of P) `}` := r

theorem mem_property_of {P : X → Prop} {a : X} (h : P a) : a ∈ {x | P x} := h

theorem of_mem_property_of {P : X → Prop} {a : X} (h : a ∈ {x | P x}) : P a := h

-- {x ∈ s | P}
definition sep (P : X → Prop) (s : property X) : property X := λx, x ∈ s ∧ P x
notation `{` binder ` ∈ ` s ` | ` r:(scoped:1 p, sep p s) `}` := r

/- insert -/

definition insert (x : X) (a : property X) : property X := {y : X | y = x ∨ y ∈ a}

abbreviation insert_same_level.{u} := @insert.{u u}

-- '{x, y, z}
notation `'{`:max a:(foldr `, ` (x b, insert_same_level x b) ∅) `}`:0 := a

theorem subproperty_insert (x : X) (a : property X) : a ⊆ insert x a :=
take y, assume ys, or.inr ys

theorem mem_insert (x : X) (s : property X) : x ∈ insert x s :=
or.inl rfl

theorem mem_insert_of_mem {x : X} {s : property X} (y : X) : x ∈ s → x ∈ insert y s :=
assume h, or.inr h

theorem eq_or_mem_of_mem_insert {x a : X} {s : property X} : x ∈ insert a s → x = a ∨ x ∈ s :=
assume h, h

/- singleton -/

open trunc_index

theorem mem_singleton_iff {X : Type} [is_set X] (a b : X) : a ∈ '{b} ↔ a = b :=
iff.intro
  (assume ainb, or.elim ainb (λ aeqb, aeqb) (λ f, false.elim f))
  (assume aeqb, or.inl aeqb)

theorem mem_singleton (a : X) : a ∈ '{a} := !mem_insert

theorem eq_of_mem_singleton {X : Type} [is_set X] {x y : X} (h : x ∈ '{y}) : x = y :=
or.elim (eq_or_mem_of_mem_insert h)
  (suppose x = y, this)
  (suppose x ∈ ∅, absurd this (not_mem_empty x))

theorem mem_singleton_of_eq {x y : X} (H : x = y) : x ∈ '{y} :=
eq.symm H ▸ mem_singleton y

/-
theorem insert_eq (x : X) (s : property X) : insert x s = '{x} ∪ s :=
ext (take y, iff.intro
  (suppose y ∈ insert x s,
    or.elim this (suppose y = x, or.inl (or.inl this)) (suppose y ∈ s, or.inr this))
  (suppose y ∈ '{x} ∪ s,
    or.elim this
      (suppose y ∈ '{x}, or.inl (eq_of_mem_singleton this))
      (suppose y ∈ s, or.inr this)))
-/

/-
theorem pair_eq_singleton (a : X) : '{a, a} = '{a} :=
by rewrite [insert_eq_of_mem !mem_singleton]
-/
/-
theorem singleton_ne_empty (a : X) : '{a} ≠ ∅ :=
begin
  intro H,
  apply not_mem_empty a,
  rewrite -H,
  apply mem_insert
end
-/

end property
