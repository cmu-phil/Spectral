/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import types.trunc
open funext eq trunc is_trunc

definition set (X : Type) := X → Prop

section
open trunc_index

definition propext {p q : Prop} (h : p ↔ q) : p = q :=
tua (equiv_of_iff_of_is_prop h)

end

definition tempty {n : trunc_index} : (n.+1)-Type := trunctype.mk empty _

namespace set

variable {X : Type}

/- membership and subset -/

definition mem (x : X) (a : set X) := a x
infix ∈ := mem
notation a ∉ b := ¬ mem a b

theorem ext {a b : set X} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
eq_of_homotopy (take x, propext (H x))

definition subset (a b : set X) : Prop := Prop.mk (∀⦃x⦄, x ∈ a → x ∈ b) _
infix ⊆ := subset

definition superset (s t : set X) : Prop := t ⊆ s
infix ⊇ := superset

theorem subset.refl (a : set X) : a ⊆ a := take x, assume H, H

theorem subset.trans {a b c : set X} (subab : a ⊆ b) (subbc : b ⊆ c) : a ⊆ c :=
take x, assume ax, subbc (subab ax)

theorem subset.antisymm {a b : set X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))

-- an alterantive name
theorem eq_of_subset_of_subset {a b : set X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subset.antisymm h₁ h₂

theorem mem_of_subset_of_mem {s₁ s₂ : set X} {a : X} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ _ h₂

/- empty set -/

definition empty : set X := λx, tempty
notation `∅` := empty

theorem not_mem_empty (x : X) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, H

theorem mem_empty_eq (x : X) : x ∈ ∅ = tempty := rfl

/-
theorem eq_empty_of_forall_not_mem {s : set X} (H : ∀ x, x ∉ s) : s = ∅ :=
ext (take x, iff.intro
  (assume xs, absurd xs (H x))
  (assume xe, absurd xe (not_mem_empty _)))

theorem ne_empty_of_mem {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
  begin intro Hs, rewrite Hs at H, apply not_mem_empty _ H end

theorem empty_subset (s : set X) : ∅ ⊆ s :=
take x, assume H, false.elim H

theorem eq_empty_of_subset_empty {s : set X} (H : s ⊆ ∅) : s = ∅ :=
subset.antisymm H (empty_subset s)

theorem subset_empty_iff (s : set X) : s ⊆ ∅ ↔ s = ∅ :=
iff.intro eq_empty_of_subset_empty (take xeq, by rewrite xeq; apply subset.refl ∅)

lemma bounded_forall_empty_iff {P : X → Prop} :
  (∀₀x∈∅, P x) ↔ true :=
iff.intro (take H, true.intro) (take H, by contradiction)
-/

end set
