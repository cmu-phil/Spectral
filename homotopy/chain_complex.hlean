/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

-/

import types.int types.pointed2 types.trunc

open eq pointed int unit is_equiv equiv is_trunc trunc equiv.ops

namespace eq
  definition transport_eq_Fl_idp_left {A B : Type} {a : A} {b : B} (f : A → B) (q : f a = b)
    : transport_eq_Fl idp q = !idp_con⁻¹ :=
  by induction q; reflexivity

  definition whisker_left_idp_con_eq_assoc
    {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃)
    : whisker_left p (idp_con q)⁻¹ = con.assoc p idp q :=
  by induction q; reflexivity

end eq open eq

namespace chain_complex

  -- are chain complexes with the "set"-requirement removed interesting?
  structure type_chain_complex : Type :=
    (car : ℤ → Type*)
    (fn : Π(n : ℤ), car (n + 1) →* car n)
    (is_chain_complex : Π{n : ℤ} (x : car ((n + 1) + 1)), fn n (fn (n+1) x) = pt)

  structure left_type_chain_complex : Type := -- chain complex on the naturals with maps going down
    (car : ℕ → Type*)
    (fn : Π(n : ℕ), car (n + 1) →* car n)
    (is_chain_complex : Π{n : ℕ} (x : car ((n + 1) + 1)), fn n (fn (n+1) x) = pt)

  structure right_type_chain_complex : Type := -- chain complex on the naturals with maps going up
    (car : ℕ → Type*)
    (fn : Π(n : ℕ), car n →* car (n + 1))
    (is_chain_complex : Π{n : ℕ} (x : car n), fn (n+1) (fn n x) = pt)

  definition  tcc_to_car [unfold 1] [coercion] := @type_chain_complex.car
  definition  tcc_to_fn  [unfold 1]            := @type_chain_complex.fn
  definition  tcc_is_chain_complex  [unfold 1] := @type_chain_complex.is_chain_complex
  definition ltcc_to_car [unfold 1] [coercion] := @left_type_chain_complex.car
  definition ltcc_to_fn  [unfold 1]            := @left_type_chain_complex.fn
  definition ltcc_is_chain_complex  [unfold 1] := @left_type_chain_complex.is_chain_complex
  definition rtcc_to_car [unfold 1] [coercion] := @right_type_chain_complex.car
  definition rtcc_to_fn  [unfold 1]            := @right_type_chain_complex.fn
  definition rtcc_is_chain_complex  [unfold 1] := @right_type_chain_complex.is_chain_complex

  -- important: these notions are shifted by one! (this is to avoid transports)
  definition is_exact_at_t [reducible] (X : type_chain_complex) (n : ℤ) : Type :=
  Π(x : X (n + 1)), tcc_to_fn X n x = pt → fiber (tcc_to_fn X (n+1)) x
  definition is_exact_at_lt [reducible] (X : left_type_chain_complex) (n : ℕ) : Type :=
  Π(x : X (n + 1)), ltcc_to_fn X n x = pt → fiber (ltcc_to_fn X (n+1)) x
  definition is_exact_at_rt [reducible] (X : right_type_chain_complex) (n : ℕ) : Type :=
  Π(x : X (n + 1)), rtcc_to_fn X (n+1) x = pt → fiber (rtcc_to_fn X n) x

  definition is_exact_t   [reducible] (X : type_chain_complex) : Type :=
  Π(n : ℤ), is_exact_at_t X n
  definition is_exact_lt [reducible] (X : left_type_chain_complex) : Type :=
  Π(n : ℕ), is_exact_at_lt X n
  definition is_exact_rt [reducible] (X : right_type_chain_complex) : Type :=
  Π(n : ℕ), is_exact_at_rt X n

  definition type_chain_complex_from_left (X : left_type_chain_complex) : type_chain_complex :=
  type_chain_complex.mk (int.rec X (λn, punit))
    begin
      intro n, fconstructor,
      { induction n with n n,
        { exact @ltcc_to_fn X n},
        { esimp, intro x, exact star}},
      { induction n with n n,
        { apply respect_pt},
        { reflexivity}}
    end
    begin
      intro n, induction n with n n,
      { exact ltcc_is_chain_complex X},
      { esimp, intro x, reflexivity}
    end

  definition is_exact_t_from_left {X : left_type_chain_complex} {n : ℕ} (H : is_exact_at_lt X n)
    : is_exact_at_t (type_chain_complex_from_left X) n :=
  H

  definition transfer_left_type_chain_complex [constructor] (X : left_type_chain_complex)
    {Y : ℕ → Type*} (g : Π{n : ℕ}, Y (n + 1) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (n + 1)), e (ltcc_to_fn X n x) = g (e x)) : left_type_chain_complex :=
  left_type_chain_complex.mk Y @g
    begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)⁻¹ ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (ltcc_is_chain_complex X _) ⬝ _,
      apply respect_pt
    end

  definition is_exact_at_lt_transfer {X : left_type_chain_complex} {Y : ℕ → Type*}
    {g : Π{n : ℕ}, Y (n + 1) →* Y n} (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (n + 1)), e (ltcc_to_fn X n x) = g (e x)) {n : ℕ}
    (H : is_exact_at_lt X n) : is_exact_at_lt (transfer_left_type_chain_complex X @g @e @p) n :=
  begin
    intro y q, esimp at *,
    assert H2 : ltcc_to_fn X n (e⁻¹ᵉ* y) = pt,
    { refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      refine ap _ q ⬝ _,
      exact respect_pt e⁻¹ᵉ*},
    cases (H _ H2) with x r,
    refine fiber.mk (e x) _,
    refine (p x)⁻¹ ⬝ _,
    refine ap e r ⬝ _,
    apply right_inv
  end

  definition trunc_left_type_chain_complex [constructor] (X : left_type_chain_complex)
    (k : trunc_index) : left_type_chain_complex :=
  left_type_chain_complex.mk
    (λn, ptrunc k (X n))
    (λn, ptrunc_functor k (ltcc_to_fn X n))
    begin
      intro n x, esimp at *,
      refine trunc.rec _ x, -- why doesn't induction work here?
      clear x, intro x, esimp,
      exact ap tr (ltcc_is_chain_complex X x)
    end

  /- actual (set) chain complexes -/

  structure chain_complex : Type :=
    (car : ℤ → Set*)
    (fn : Π(n : ℤ), car (n + 1) →* car n)
    (is_chain_complex : Π{n : ℤ} (x : car ((n + 1) + 1)), fn n (fn (n+1) x) = pt)

  structure left_chain_complex : Type := -- chain complex on the naturals with maps going down
    (car : ℕ → Set*)
    (fn : Π(n : ℕ), car (n + 1) →* car n)
    (is_chain_complex : Π{n : ℕ} (x : car ((n + 1) + 1)), fn n (fn (n+1) x) = pt)

  structure right_chain_complex : Type := -- chain complex on the naturals with maps going up
    (car : ℕ → Set*)
    (fn : Π(n : ℕ), car n →* car (n + 1))
    (is_chain_complex : Π{n : ℕ} (x : car n), fn (n+1) (fn n x) = pt)

  definition  cc_to_car [unfold 1] [coercion] := @chain_complex.car
  definition  cc_to_fn  [unfold 1]            := @chain_complex.fn
  definition  cc_is_chain_complex  [unfold 1] := @chain_complex.is_chain_complex
  definition lcc_to_car [unfold 1] [coercion] := @left_chain_complex.car
  definition lcc_to_fn  [unfold 1]            := @left_chain_complex.fn
  definition lcc_is_chain_complex  [unfold 1] := @left_chain_complex.is_chain_complex
  definition rcc_to_car [unfold 1] [coercion] := @right_chain_complex.car
  definition rcc_to_fn  [unfold 1]            := @right_chain_complex.fn
  definition rcc_is_chain_complex  [unfold 1] := @right_chain_complex.is_chain_complex

  -- important: these notions are shifted by one! (this is to avoid transports)
  definition is_exact_at [reducible] (X : chain_complex) (n : ℤ) : Type :=
  Π(x : X (n + 1)), cc_to_fn X n x = pt → image (cc_to_fn X (n+1)) x
  definition is_exact_at_l [reducible] (X : left_chain_complex) (n : ℕ) : Type :=
  Π(x : X (n + 1)), lcc_to_fn X n x = pt → image (lcc_to_fn X (n+1)) x
  definition is_exact_at_r [reducible] (X : right_chain_complex) (n : ℕ) : Type :=
  Π(x : X (n + 1)), rcc_to_fn X (n+1) x = pt → image (rcc_to_fn X n) x

  definition is_exact   [reducible] (X : chain_complex) : Type := Π(n : ℤ), is_exact_at X n
  definition is_exact_l [reducible] (X : left_chain_complex) : Type := Π(n : ℕ), is_exact_at_l X n
  definition is_exact_r [reducible] (X : right_chain_complex) : Type := Π(n : ℕ), is_exact_at_r X n

  definition chain_complex_from_left (X : left_chain_complex) : chain_complex :=
  chain_complex.mk (int.rec X (λn, punit))
    begin
      intro n, fconstructor,
      { induction n with n n,
        { exact @lcc_to_fn X n},
        { esimp, intro x, exact star}},
      { induction n with n n,
        { apply respect_pt},
        { reflexivity}}
    end
    begin
      intro n, induction n with n n,
      { exact lcc_is_chain_complex X},
      { esimp, intro x, reflexivity}
    end

  definition is_exact_from_left {X : left_chain_complex} {n : ℕ} (H : is_exact_at_l X n)
    : is_exact_at (chain_complex_from_left X) n :=
  H

  definition transfer_left_chain_complex [constructor] (X : left_chain_complex) {Y : ℕ → Set*}
    (g : Π{n : ℕ}, Y (n + 1) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (n + 1)), e (lcc_to_fn X n x) = g (e x)) : left_chain_complex :=
  left_chain_complex.mk Y @g
    begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)⁻¹ ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (lcc_is_chain_complex X _) ⬝ _,
      apply respect_pt
    end

  definition transfer_is_exact_at_l (X : left_chain_complex) {Y : ℕ → Set*}
    (g : Π{n : ℕ}, Y (n + 1) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (n + 1)), e (lcc_to_fn X n x) = g (e x))
    {n : ℕ} (H : is_exact_at_l X n) : is_exact_at_l (transfer_left_chain_complex X @g @e @p) n :=
  begin
    intro y q, esimp at *,
    assert H2 : lcc_to_fn X n (e⁻¹ᵉ* y) = pt,
    { refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      refine ap _ q ⬝ _,
      exact respect_pt e⁻¹ᵉ*},
    induction (H _ H2) with x,
    induction x with x r,
    refine image.mk (e x) _,
    refine (p x)⁻¹ ⬝ _,
    refine ap e r ⬝ _,
    apply right_inv
  end

  definition trunc_left_chain_complex [constructor] (X : left_type_chain_complex)
    : left_chain_complex :=
  left_chain_complex.mk
    (λn, ptrunc 0 (X n))
    (λn, ptrunc_functor 0 (ltcc_to_fn X n))
    begin
      intro n x, esimp at *,
      refine @trunc.rec _ _ _ (λH, !is_trunc_eq) _ x,
      clear x, intro x, esimp,
      exact ap tr (ltcc_is_chain_complex X x)
    end

  definition is_exact_at_l_trunc (X : left_type_chain_complex) {n : ℕ}
    (H : is_exact_at_lt X n) : is_exact_at_l (trunc_left_chain_complex X) n :=
  begin
    intro x p, esimp at *,
    induction x with x, esimp at *,
    note q := !tr_eq_tr_equiv p,
    induction q with q,
    induction H x q with y r,
    refine image.mk (tr y) _,
    esimp, exact ap tr r
  end

end chain_complex
