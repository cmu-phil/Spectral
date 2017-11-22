/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import hit.two_quotient .seq_colim

open eq prod sum two_quotient sigma function relation e_closure nat seq_colim

namespace localization
section quasi_local_extension

  universe variables u v w
  parameters {A : Type.{u}} {P : A → Type.{v}} {Q : A → Type.{w}} (F : Πa, P a → Q a)
  definition is_local [class] (Y : Type) : Type :=
  Π(a : A), is_equiv (λg, g ∘ F a : (Q a → Y) → (P a → Y))



  section
  parameter (X : Type.{max u v w})
  local abbreviation Y := X + Σa, (P a → X) × Q a

  -- do we want to remove the contractible pairs?
  inductive qleR : Y → Y → Type :=
  | J : Π{a : A} (f : P a → X) (p : P a), qleR (inr ⟨a, (f, F a p)⟩) (inl (f p))
  | k : Π{a : A} (g : Q a → X) (q : Q a), qleR (inl (g q)) (inr ⟨a, (g ∘ F a, q)⟩)

  inductive qleQ : Π⦃y₁ y₂ : Y⦄, e_closure qleR y₁ y₂ → e_closure qleR y₁ y₂ → Type :=
  | K : Π{a : A} (g : Q a → X) (p : P a), qleQ [qleR.k g (F a p)] [qleR.J (g ∘ F a) p]⁻¹ʳ

  definition one_step_localization : Type := two_quotient qleR qleQ
  definition incl : X → one_step_localization := incl0 _ _ ∘ inl

  end
  variables (X : Type.{max u v w}) {Z : Type}

  definition n_step_localization : ℕ → Type :=
  nat.rec X (λn Y, localization.one_step_localization F Y)

  definition incln (n : ℕ) :
    n_step_localization X n → n_step_localization X (succ n) :=
  localization.incl F (n_step_localization X n)

  -- localization if P and Q consist of ω-compact types
  definition localization : Type := seq_colim (incln X)
  definition incll : X → localization X := ι' _ 0

  protected definition rec {P : localization X → Type} [Πz, is_local (P z)]
    (H : Πx, P (incll X x)) (z : localization X) : P z :=
  begin
    exact sorry
  end

  definition extend {Y Z : Type} (f : Y → Z) [is_local Z] (x : one_step_localization Y) : Z :=
  begin
    induction x,
    { induction a,
      { exact f a},
      { induction a with a v, induction v with f q, exact sorry}},
    { exact sorry},
    { exact sorry}
  end

  protected definition elim {Y : Type} [is_local Y]
    (H : X → Y) (z : localization X) : Y :=
  begin
    induction z with n x n x,
    { induction n with n IH,
      { exact H x},
      induction x,
      { induction a,
        { exact IH a},
        { induction a with a v, induction v with f q, exact sorry}},
      { exact sorry},
      exact sorry},
    exact sorry
  end


end quasi_local_extension
end localization
