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

    parameters {A₀₀ A₀₂ A₀₄ A₂₀ A₂₂ A₂₄ A₄₀ A₄₂ A₄₄ : Type}
               {f₀₁ : A₀₂ → A₀₀} {f₂₁ : A₂₂ → A₂₀} {f₄₁ : A₄₂ → A₄₀}
               {f₀₃ : A₀₂ → A₀₄} {f₂₃ : A₂₂ → A₂₄} {f₄₃ : A₄₂ → A₄₄}
               {f₁₀ : A₂₀ → A₀₀} {f₁₂ : A₂₂ → A₀₂} {f₁₄ : A₂₄ → A₀₄}
               {f₃₀ : A₂₀ → A₄₀} {f₃₂ : A₂₂ → A₄₂} {f₃₄ : A₂₄ → A₄₄}
               (s₁₁ : f₀₁ ∘ f₁₂ ~ f₁₀ ∘ f₂₁) (s₃₁ : f₄₁ ∘ f₃₂ ~ f₃₀ ∘ f₂₁)
               (s₁₃ : f₀₃ ∘ f₁₂ ~ f₁₄ ∘ f₂₃) (s₃₃ : f₄₃ ∘ f₃₂ ~ f₃₄ ∘ f₂₃)

    definition pushout2 : Type :=
    pushout (pushout.functor f₂₁ f₀₁ f₄₁ s₁₁ s₃₁) (pushout.functor f₂₃ f₀₃ f₄₃ s₁₃ s₃₃)

    definition pushout2' : Type :=
    pushout (pushout.functor f₁₂ f₁₀ f₁₄ s₁₁⁻¹ʰᵗʸ s₁₃⁻¹ʰᵗʸ) (pushout.functor f₃₂ f₃₀ f₃₄ s₃₁⁻¹ʰᵗʸ s₃₃⁻¹ʰᵗʸ)

  end
end pushout
