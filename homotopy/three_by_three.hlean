-- WIP

import ..move_to_lib
open function eq

namespace pushout
  section

  -- structure span2 : Type :=
  --   {A₀₀ A₀₂ A₀₄ A₂₀ A₂₂ A₂₄ A₄₀ A₄₂ A₄₄ : Type}
  --   {f₀₁ : A₀₂ → A₀₀} {f₂₁ : A₂₂ → A₂₀} {f₄₁ : A₄₂ → A₄₀}
  --   {f₀₃ : A₀₂ → A₀₄} {f₂₃ : A₂₂ → A₂₄} {f₄₃ : A₄₂ → A₄₄}
  --   {f₁₀ : A₂₀ → A₀₀} {f₁₂ : A₂₂ → A₀₂} {f₁₄ : A₂₄ → A₀₄}
  --   {f₃₀ : A₂₀ → A₄₀} {f₃₂ : A₂₂ → A₄₂} {f₃₄ : A₂₄ → A₄₄}
  --   (s₁₁ : f₀₁ ∘ f₁₂ ~ f₁₀ ∘ f₂₁) (s₃₁ : f₄₁ ∘ f₃₂ ~ f₃₀ ∘ f₂₁)
  --   (s₁₃ : f₀₃ ∘ f₁₂ ~ f₁₄ ∘ f₂₃) (s₃₃ : f₄₃ ∘ f₃₂ ~ f₃₄ ∘ f₂₃)

  structure three_by_three_span : Type :=
    {A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type}
    {f₁₀ : A₂₀ → A₀₀} {f₃₀ : A₂₀ → A₄₀}
    {f₁₂ : A₂₂ → A₀₂} {f₃₂ : A₂₂ → A₄₂}
    {f₁₄ : A₂₄ → A₀₄} {f₃₄ : A₂₄ → A₄₄}
    {f₀₁ : A₀₂ → A₀₀} {f₀₃ : A₀₂ → A₀₄}
    {f₂₁ : A₂₂ → A₂₀} {f₂₃ : A₂₂ → A₂₄}
    {f₄₁ : A₄₂ → A₄₀} {f₄₃ : A₄₂ → A₄₄}
    (s₁₁ : f₀₁ ∘ f₁₂ ~ f₁₀ ∘ f₂₁) (s₃₁ : f₄₁ ∘ f₃₂ ~ f₃₀ ∘ f₂₁)
    (s₁₃ : f₀₃ ∘ f₁₂ ~ f₁₄ ∘ f₂₃) (s₃₃ : f₄₃ ∘ f₃₂ ~ f₃₄ ∘ f₂₃)

  open three_by_three_span
  variable (E : three_by_three_span)
check (pushout.functor (f₂₁ E) (f₀₁ E) (f₄₁ E) (s₁₁ E) (s₃₁ E))
  definition pushout2hv (E : three_by_three_span) : Type :=
  pushout (pushout.functor (f₂₁ E) (f₀₁ E) (f₄₁ E) (s₁₁ E) (s₃₁ E))
          (pushout.functor (f₂₃ E) (f₀₃ E) (f₄₃ E) (s₁₃ E) (s₃₃ E))

  definition pushout2vh (E : three_by_three_span) : Type :=
  pushout (pushout.functor (f₁₂ E) (f₁₀ E) (f₁₄ E) (s₁₁ E)⁻¹ʰᵗʸ (s₁₃ E)⁻¹ʰᵗʸ)
          (pushout.functor (f₃₂ E) (f₃₀ E) (f₃₄ E) (s₃₁ E)⁻¹ʰᵗʸ (s₃₃ E)⁻¹ʰᵗʸ)

  definition three_by_three (E : three_by_three_span) : pushout2hv E ≃ pushout2vh E := sorry

  end
end pushout
