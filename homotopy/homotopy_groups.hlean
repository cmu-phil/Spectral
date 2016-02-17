/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

-/

-- to be moved to algebra/homotopy_group in the Lean library

import group_theory.basic algebra.homotopy_group

open eq algebra pointed group trunc is_trunc nat algebra equiv equiv.ops is_equiv

namespace my

  section
  variables {A B C : Type*}
  definition apn_compose (n : ℕ) (g : B →* C) (f : A →* B) : apn n (g ∘* f) ~* apn n g ∘* apn n f :=
  begin
    induction n with n IH,
    { reflexivity},
    { refine ap1_phomotopy IH ⬝* _, apply ap1_compose}
  end

  theorem ap1_con (f : A →* B) (p q : Ω A) : ap1 f (p ⬝ q) = ap1 f p ⬝ ap1 f q :=
  begin
    rewrite [▸*, ap_con, +con.assoc, con_inv_cancel_left]
  end

  definition apn_con {n : ℕ} (f : A →* B) (p q : Ω[n + 1] A)
    : apn (n+1) f (p ⬝ q) = apn (n+1) f p ⬝ apn (n+1) f q :=
  ap1_con (apn n f) p q

  definition tr_mul {n : ℕ} (p q : Ω[n + 1] A) : @mul (πg[n+1] A) _ (tr p ) (tr q) = tr (p ⬝ q) :=
  by reflexivity
  end

  section

    parameters {A B : Type} (f : A ≃ B) [group A]

    definition group_equiv_mul (b b' : B) : B := f (f⁻¹ᶠ b * f⁻¹ᶠ b')

    definition group_equiv_one : B := f one

    definition group_equiv_inv (b : B) : B := f (f⁻¹ᶠ b)⁻¹

    local infix * := my.group_equiv_mul f
    local postfix ^ := my.group_equiv_inv f
    local notation 1 := my.group_equiv_one f

    theorem group_equiv_mul_assoc (b₁ b₂ b₃ : B) : (b₁ * b₂) * b₃ = b₁ * (b₂ * b₃) :=
    by rewrite [↑group_equiv_mul, +left_inv f, mul.assoc]

    theorem group_equiv_one_mul (b : B) : 1 * b = b :=
    by rewrite [↑group_equiv_mul, ↑group_equiv_one, left_inv f, one_mul, right_inv f]

    theorem group_equiv_mul_one (b : B) : b * 1 = b :=
    by rewrite [↑group_equiv_mul, ↑group_equiv_one, left_inv f, mul_one, right_inv f]

    theorem group_equiv_mul_left_inv (b : B) : b^ * b = 1 :=
    by rewrite [↑group_equiv_mul, ↑group_equiv_one, ↑group_equiv_inv,
                +left_inv f, mul.left_inv]

    definition group_equiv_closed : group B :=
    ⦃group,
      mul          := group_equiv_mul,
      mul_assoc    := group_equiv_mul_assoc,
      one          := group_equiv_one,
      one_mul      := group_equiv_one_mul,
      mul_one      := group_equiv_mul_one,
      inv          := group_equiv_inv,
      mul_left_inv := group_equiv_mul_left_inv,
    is_set_carrier := is_trunc_equiv_closed 0 f⦄

  end

end my open my

namespace eq

  local attribute mul [unfold 2]
  definition homotopy_group_homomorphism [constructor] (n : ℕ) {A B : Type*} (f : A →* B)
    : πg[n+1] A →g πg[n+1] B :=
  begin
    fconstructor,
    { exact phomotopy_group_functor (n+1) f},
    { intro g,
      refine @trunc.rec _ _ _ (λx, !is_trunc_eq) _, intro h,
      refine @trunc.rec _ _ _ (λx, !is_trunc_eq) _ g, clear g, intro g,
      rewrite [tr_mul, ▸*],
      apply ap tr, apply apn_con}
  end

  notation `π→g[`:95  n:0 ` +1] `:0 f:95 := homotopy_group_homomorphism n f

end eq
