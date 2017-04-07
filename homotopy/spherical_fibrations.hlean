import homotopy.join homotopy.smash

open eq equiv trunc function bool join sphere sphere_index sphere.ops prod
open pointed sigma smash is_trunc

namespace spherical_fibrations

  /- classifying type of spherical fibrations -/
  definition BG (n : ℕ) : Type₁ :=
  Σ(X : Type₀), ∥ X ≃ S n..-1 ∥

  definition pointed_BG [instance] [constructor] (n : ℕ) : pointed (BG n) :=
  pointed.mk ⟨ S n..-1 , tr erfl ⟩

  definition pBG [constructor] (n : ℕ) : Type* := pointed.mk' (BG n)

  definition G (n : ℕ) : Type₁ :=
  pt = pt :> BG n

  definition G_char (n : ℕ) : G n ≃ (S n..-1 ≃ S n..-1) :=
  calc
    G n ≃ Σ(p : S n..-1 = S n..-1), _ : sigma_eq_equiv
    ... ≃ (S n..-1 = S n..-1) : sigma_equiv_of_is_contr_right
    ... ≃ (S n..-1 ≃ S n..-1) : eq_equiv_equiv

  definition mirror (n : ℕ) : S n..-1 → G n :=
  begin
    intro v, apply to_inv (G_char n),
    exact sorry
  end

/-
  Can we give a fibration P : S n → Type, P base = F n = Ω(BF n) = (S. n ≃* S. n)
  and total space sigma P ≃ G (n+1) = Ω(BG (n+1)) = (S n.+1 ≃ S .n+1)

  Yes, let eval : BG (n+1) → S n be the evaluation map
-/

  definition S_of_BG (n : ℕ) : Ω(pBG (n+1)) → S n :=
  λ f, f..1 ▸ base

  definition BG_succ (n : ℕ) : BG n → BG (n+1) :=
  begin
    intro X, cases X with X p,
    apply sigma.mk (susp X), induction p with f, apply tr,
    apply susp.equiv f
  end

  /- classifying type of pointed spherical fibrations -/
  definition BF (n : ℕ) : Type₁ :=
  Σ(X : Type*), ∥ X ≃* S* n ∥

  definition pointed_BF [instance] [constructor] (n : ℕ) : pointed (BF n) :=
  pointed.mk ⟨ S* n , tr pequiv.rfl ⟩

  definition pBF [constructor] (n : ℕ) : Type* := pointed.mk' (BF n)

  definition BF_succ (n : ℕ) : BF n → BF (n+1) :=
  begin
    intro X, cases X with X p,
    apply sigma.mk (psusp X), induction p with f, apply tr,
    apply susp.psusp_pequiv f
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
    apply sigma.mk (smash X Y),
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
  - pfiber (BG_of_BF n) ≃* S. n
  - π₁(BF n)=π₁(BG n)=ℤ/2ℤ
  - double covers BSG and BSF
  - O : BF n → BG 1 = Σ(A : Type), ∥ A = bool ∥
  - BSG n = sigma O
  - π₁(BSG n)=π₁(BSF n)=O
  - BSO(n),
  - find BF' n : Type₀ with BF' n ≃ BF n etc.
  - canonical bundle γₙ : ℝP(n) → ℝP∞=BO(1) → Type₀
     prove T(γₙ) = ℝP(n+1)
  - BG∞ = BF∞ (in fact = BGL₁(S), the group of units of the sphere spectrum)
  - clutching construction:
     any f : S n → SG(n)  gives S n.+1 → BSG(n)  (mut.mut. for O(n),SO(n),etc.)
  - all bundles on S 3 are trivial, incl. tangent bundle
  - Adams' result on vector fields on spheres:
     there are maximally ρ(n)-1 indep.sections of the tangent bundle of S (n-1)
     where ρ(n) is the n'th Radon-Hurwitz number.→
-/

-- tangent bundle on S 2:

  namespace two_sphere

    definition tau : S 2 → BG 2 :=
    begin
      intro v, induction v with x, do 2 exact pt,
      exact sorry
    end

  end two_sphere

end spherical_fibrations
