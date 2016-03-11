import homotopy.join homotopy.smash

open eq equiv trunc function bool join sphere sphere_index sphere.ops prod
open pointed sigma smash

namespace spherical_fibrations

  /- classifying type of spherical fibrations -/
  definition BG (n : ℕ) : Type₁ :=
  Σ(X : Type₀), ∥ X ≃ S n..-1 ∥

  definition pointed_BG [instance] [constructor] (n : ℕ) : pointed (BG n) :=
  pointed.mk ⟨ S n..-1 , tr erfl ⟩

  definition pBG [constructor] (n : ℕ) : Type* := pointed.mk' (BG n)

  definition BG_succ (n : ℕ) : BG n → BG (n+1) :=
  begin
    intro X, cases X with X p,
    apply sigma.mk (susp X), induction p with f, apply tr,
    apply susp.equiv f
  end

  /- classifying type of pointed spherical fibrations -/
  definition BF (n : ℕ) : Type₁ :=
  Σ(X : Type*), ∥ X ≃* S. n ∥

  definition pointed_BF [instance] [constructor] (n : ℕ) : pointed (BF n) :=
  pointed.mk ⟨ S. n , tr pequiv.rfl ⟩

  definition pBF [constructor] (n : ℕ) : Type* := pointed.mk' (BF n)

  definition BF_succ (n : ℕ) : BF n → BF (n+1) :=
  begin
    intro X, cases X with X p,
    apply sigma.mk (psusp X), induction p with f, apply tr,
    apply susp.psusp_equiv f
  end

  definition BF_of_BG {n : ℕ} : BG n → BF n :=
  begin
    intro X, cases X with X p,
    apply sigma.mk (pointed.MK (susp X) susp.north),
    induction p with f, apply tr,
    apply pequiv_of_equiv (susp.equiv f),
    reflexivity
  end

  definition BG_of_BF {n : ℕ} : BF n → BG (n + 1) :=
  begin
    intro X, cases X with X hX,
    apply sigma.mk (carrier X), induction hX with fX,
    apply tr, exact fX
  end

  definition BG_mul {n m : ℕ} (X : BG n) (Y : BG m) : BG (n + m) :=
  begin
    cases X with X pX, cases Y with Y pY,
    apply sigma.mk (join X Y),
    induction pX with fX, induction pY with fY,
    apply tr, rewrite add_sub_one,
    exact (join.equiv_closed fX fY) ⬝e (join.spheres n..-1 m..-1)
  end

  definition BF_mul {n m : ℕ} (X : BF n) (Y : BF m) : BF (n + m) :=
  begin
    cases X with X hX, cases Y with Y hY,
    apply sigma.mk (psmash X Y),
    induction hX with fX, induction hY with fY, apply tr,
    exact sorry -- needs smash.spheres : psmash (S. n) (S. m) ≃ S. (n + m)
  end

  definition BF_of_BG_mul (n m : ℕ) (X : BG n) (Y : BG m)
    : BF_of_BG (BG_mul X Y) = BF_mul (BF_of_BG X) (BF_of_BG Y) :=
  sorry

  -- Thom spaces
  namespace thom
    variables {X : Type} {n : ℕ} (α : X → BF n)

    -- the canonical section of an F-object
    protected definition sec (x : X) : carrier (sigma.pr1 (α x)) :=
    Point _

    open pushout sigma

    definition thom_space : Type :=
    pushout (λx : X, ⟨x , thom.sec α x⟩) (const X unit.star)
  end thom

/-
  Things to do:
  - Orientability and orientations
    * Thom class u ∈ ~Hⁿ(Tξ)
    * eventually prove Thom-Isomorphism (Rudyak IV.5.7)
  - define BG∞ and BF∞ as colimits of BG n and BF n
  - Ω(BF n) = ΩⁿSⁿ₁ + ΩⁿSⁿ₋₁ (self-maps of degree ±1)
  - succ_BF n is (n - 2) connected (from Freudenthal)
  - pfiber (BG_of_BF n) ≃ S. n
  - π₁(BF n)=π₁(BG n)=ℤ/2ℤ
  - double covers BSG and BSF
  - O : BF n → BG 1 = Σ(A : Type), ∥ A = bool ∥
  - BSG n = sigma O
  - π₁(BSG n)=π₁(BSF n)=O
  - BSO(n), BSTop(n)
  - find BF' n : Type₀ with BF' n ≃ BF n etc.
  - canonical bundle γₙ : ℝP(n) → ℝP∞=BO(1) → Type₀
     prove T(γₙ) = ℝP(n+1)
-/
end spherical_fibrations
