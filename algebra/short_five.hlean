/-
Author: Jeremy Avigad
-/
import .module_chain_complex
open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc nat trunc
open algebra function succ_str
open left_module

section short_five
  variable  {R : Ring}
  variables {A₀ B₀ C₀ A₁ B₁ C₁ : LeftModule R}
  variables {f₀ : A₀ →lm B₀} {g₀ : B₀ →lm C₀}
  variables {f₁ : A₁ →lm B₁} {g₁ : B₁ →lm C₁}
  variables {h  : A₀ →lm A₁} {k  : B₀ →lm B₁} {l  : C₀ →lm C₁}

  premise   (short_exact₀ : is_short_exact f₀ g₀)
  premise   (short_exact₁ : is_short_exact f₁ g₁)
  premise   (hsquare₁ : hsquare f₀ f₁ h k)
  premise   (hsquare₂ : hsquare g₀ g₁ k l)

  include short_exact₀ short_exact₁ hsquare₁ hsquare₂

  open algebra.is_short_exact

  lemma short_five_mono [embh : is_embedding h] [embl : is_embedding l] :
    is_embedding k :=
  have is_embedding f₁, from is_emb short_exact₁,
  is_embedding_of_is_add_hom k
    (take b, suppose k b = 0,
      have l (g₀ b) = 0, by rewrite [hsquare₂, ▸*, this, respect_zero],
      have g₀ b = 0, from eq_zero_of_eq_zero_of_is_embedding this,
      image.elim (ker_in_im short_exact₀ _ this)
      (take a,
        suppose f₀ a = b,
        have f₁ (h a) = 0, by rewrite [-hsquare₁, ▸*, this]; assumption,
        have h a = 0, from eq_zero_of_eq_zero_of_is_embedding this,
        have a = 0, from eq_zero_of_eq_zero_of_is_embedding this,
        show b = 0, by rewrite [-`f₀ a = b`, this, respect_zero]))

  lemma short_five_epi (surjh : is_surjective h) (surjl : is_surjective l) :
    is_surjective k :=
  have surjg₀ : is_surjective g₀, from is_surj short_exact₀,
  take b₁ : B₁,
  image.elim (surjl (g₁ b₁)) (
  take c₀ : C₀,
  assume lc₀ : l c₀ = g₁ b₁,
  image.elim (surjg₀ c₀) (
  take b₀ : B₀,
  assume g₀b₀ : g₀ b₀ = c₀,
  have g₁ (k b₀ - b₁) = 0, by rewrite [respect_sub, -hsquare₂, ▸*, g₀b₀, lc₀, sub_self],
  image.elim (ker_in_im short_exact₁ _ this) (
  take a₁ : A₁,
  assume f₁a₁ : f₁ a₁ = k b₀ - b₁,
  image.elim (surjh a₁) (
  take a₀ : A₀,
  assume ha₀ : h a₀ = a₁,
  have k (f₀ a₀) = k b₀ - b₁, by rewrite [hsquare₁, ▸*, ha₀, f₁a₁],
  have k (b₀ - f₀ a₀) = b₁, by rewrite [respect_sub, this, sub_sub_self],
  image.mk _ this))))
end short_five

section short_exact
  open module_chain_complex
  variables {R : Ring} {N : succ_str}

  record is_short_exact_at (C : module_chain_complex R N) (n : N) :=
  (is_contr_0 : is_contr (C n))
  (is_exact_at_1 : is_exact_at_m C n)
  (is_exact_at_2 : is_exact_at_m C (S n))
  (is_exact_at_3 : is_exact_at_m C (S (S n)))
  (is_contr_4 : is_contr (C (S (S (S (S n))))))

  /- TODO: show that this gives rise to a short exact sequence in the sense above -/
end short_exact

section short_five_redux
  open module_chain_complex
  variables {R : Ring} {N : succ_str}

  /- TODO: restate short five in these terms -/
end short_five_redux


/- TODO: state and prove strong_four, adapting the template below.

section strong_four
  variables {R : Type} [ring R]
  variables {A B C D A' B' C' D' : Type}
  variables [left_module R A] [left_module R B] [left_module R C] [left_module R D]
  variables [left_module R A'] [left_module R B'] [left_module R C'] [left_module R D']

  variables (ρ : A → B) [is_module_hom R ρ]
  variables (σ : B → C) [is_module_hom R σ]
  variables (τ : C → D) [is_module_hom R τ]
  variable  (chainρσ : ∀ a, σ (ρ a) = 0)
  variable  (exactρσ : ∀ {b}, σ b = 0 → ∃ a, ρ a = b)
  variable  (chainστ : ∀ b, τ (σ b) = 0)
  variable  (exactστ : ∀ {c}, τ c = 0 → ∃ b, σ b = c)

  variables (ρ' : A' → B') [is_module_hom R ρ']
  variables (σ' : B' → C') [is_module_hom R σ']
  variables (τ' : C' → D') [is_module_hom R τ']
  variable  (chainρ'σ' : ∀ a', σ' (ρ' a') = 0)
  variable  (exactρ'σ' : ∀ {b'}, σ' b' = 0 → ∃ a', ρ' a' = b')
  variable  (chainσ'τ' : ∀ b', τ' (σ' b') = 0)
  variable  (exactσ'τ' : ∀ {c'}, τ' c' = 0 → ∃ b', σ' b' = c')

  variables (α : A → A') [is_module_hom R α]
  variables (β : B → B') [is_module_hom R β]
  variables (γ : C → C') [is_module_hom R γ]
  variables (δ : D → D') [is_module_hom R δ]

  variables (sq₁ : comm_square ρ ρ' α β)
  variables (sq₂ : comm_square σ σ' β γ)
  variables (sq₃ : comm_square τ τ' γ δ)

include sq₃ σ' sq₂ exactρ'σ' sq₁ chainρσ

theorem strong_four_a (epiα : is_surjective α) (monoδ : is_embedding δ) (c : C) (γc0 : γ c = 0) :
  Σ b, (β b = 0 × σ b = c) :=
have δ (τ c) = 0, by rewrite [sq₃, γc0, hom_zero],
have τ c = 0, from eq_zero_of_eq_zero_of_is_embedding this,
obtain b (σbc : σ b = c), from exactστ this,
have σ' (β b) = 0, by rewrite [-sq₂, σbc, γc0],
obtain a' (ρ'a'βb : ρ' a' = β b), from exactρ'σ' this,
obtain a (αaa' : α a = a'), from epiα a',
exists.intro (b - ρ a)
  (pair
    (show β (b - ρ a) = 0, by rewrite [hom_sub, -ρ'a'βb, sq₁, αaa', sub_self])
    (show σ (b - ρ a) = c, from calc
       σ (b - ρ a) = σ b - σ (ρ a) : hom_sub _
               ... = σ b           : by rewrite [chainρσ, sub_zero]
               ... = c             : σbc))

end strong_four
-/
