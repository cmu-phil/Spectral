/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

-/

import types.int types.pointed2 types.trunc algebra.hott ..group_theory.basic .fin

open eq pointed int unit is_equiv equiv is_trunc trunc equiv.ops function algebra group sigma.ops
     sum prod nat bool fin
namespace eq
  definition transport_eq_Fl_idp_left {A B : Type} {a : A} {b : B} (f : A → B) (q : f a = b)
    : transport_eq_Fl idp q = !idp_con⁻¹ :=
  by induction q; reflexivity

  definition whisker_left_idp_con_eq_assoc
    {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃)
    : whisker_left p (idp_con q)⁻¹ = con.assoc p idp q :=
  by induction q; reflexivity

end eq open eq

structure succ_str : Type :=
  (carrier : Type)
  (succ : carrier → carrier)

attribute succ_str.carrier [coercion]

definition succ_str.S {X : succ_str} : X → X := succ_str.succ X

open succ_str

definition snat [reducible] [constructor] : succ_str := succ_str.mk ℕ nat.succ
definition snat' [reducible] [constructor] : succ_str := succ_str.mk ℕ nat.pred
definition sint [reducible] [constructor] : succ_str := succ_str.mk ℤ int.succ
definition sint' [reducible] [constructor] : succ_str := succ_str.mk ℤ int.pred

notation `+ℕ` := snat
notation `-ℕ` := snat'
notation `+ℤ` := sint
notation `-ℤ` := sint'

definition stratified_type [reducible] (N : succ_str) (n : ℕ) : Type₀ := N × fin (succ n)

-- definition stratified_succ' {N : succ_str}  : Π{n : ℕ}, N → ifin n → stratified_type N n
-- | (succ k) n (fz k) := (S n, ifin.max k)
-- | (succ k) n (fs x) := (n, ifin.incl x)

-- definition stratified_succ {N : succ_str} {n : ℕ} (x : stratified_type N n) : stratified_type N n :=
-- stratified_succ' (pr1 x) (pr2 x)

definition stratified_succ {N : succ_str} {n : ℕ} (x : stratified_type N n)
  : stratified_type N n :=
(if val (pr2 x) = n then S (pr1 x) else pr1 x, my_succ (pr2 x))

definition stratified [reducible] [constructor] (N : succ_str) (n : ℕ) : succ_str :=
succ_str.mk (stratified_type N n) stratified_succ

--example (n : ℕ) : flatten (n, (2 : ifin (nat.succ (nat.succ 4)))) = 6*n+2 := proof rfl qed

notation `+3ℕ` := stratified +ℕ 2
notation `-3ℕ` := stratified -ℕ 2
notation `+3ℤ` := stratified +ℤ 2
notation `-3ℤ` := stratified -ℤ 2
notation `+6ℕ` := stratified +ℕ 5
notation `-6ℕ` := stratified -ℕ 5
notation `+6ℤ` := stratified +ℤ 5
notation `-6ℤ` := stratified -ℤ 5

-- definition triple_type (N : succ_str) : Type₀ := N ⊎ N ⊎ N
-- definition triple_succ {N : succ_str} : triple_type N → triple_type N
-- | (inl n)       := inr (inl n)
-- | (inr (inl n)) := inr (inr n)
-- | (inr (inr n)) := inl (S n)

-- definition triple [reducible] [constructor] (N : succ_str) : succ_str :=
-- succ_str.mk (triple_type N) triple_succ

-- notation `+3ℕ` := triple +ℕ
-- notation `-3ℕ` := triple -ℕ
-- notation `+3ℤ` := triple +ℤ
-- notation `-3ℤ` := triple -ℤ

namespace chain_complex

  -- are chain complexes with the "set"-requirement removed interesting?
  structure type_chain_complex (N : succ_str) : Type :=
    (car : N → Type*)
    (fn : Π(n : N), car (S n) →* car n)
    (is_chain_complex : Π(n : N) (x : car (S (S n))), fn n (fn (S n) x) = pt)

  section
  variables {N : succ_str} (X : type_chain_complex N) (n : N)

  definition tcc_to_car [unfold 2] [coercion] := @type_chain_complex.car
  definition tcc_to_fn  [unfold 2] : X (S n) →* X n := type_chain_complex.fn X n
  definition tcc_is_chain_complex  [unfold 2]
    : Π(x : X (S (S n))), tcc_to_fn X n (tcc_to_fn X (S n) x) = pt :=
  type_chain_complex.is_chain_complex X n

  -- important: these notions are shifted by one! (this is to avoid transports)
  definition is_exact_at_t [reducible] /- X n -/ : Type :=
  Π(x : X (S n)), tcc_to_fn X n x = pt → fiber (tcc_to_fn X (S n)) x

  definition is_exact_t [reducible] /- X -/ : Type :=
  Π(n : N), is_exact_at_t X n

  -- definition type_chain_complex_from_left (X : type_chain_complex) : type_chain_complex :=
  -- type_chain_complex.mk (int.rec X (λn, punit))
  --   begin
  --     intro n, fconstructor,
  --     { induction n with n n,
  --       { exact @ltcc_to_fn X n},
  --       { esimp, intro x, exact star}},
  --     { induction n with n n,
  --       { apply respect_pt},
  --       { reflexivity}}
  --   end
  --   begin
  --     intro n, induction n with n n,
  --     { exact ltcc_is_chain_complex X},
  --     { esimp, intro x, reflexivity}
  --   end

  -- definition is_exact_t_from_left {X : type_chain_complex} {n : ℕ} (H : is_exact_at_lt X n)
  --   : is_exact_at_t (type_chain_complex_from_left X) n :=
  -- H

  definition transfer_type_chain_complex [constructor]
    {Y : N → Type*} (g : Π{n : N}, Y (S n) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (tcc_to_fn X n x) = g (e x)) : type_chain_complex N :=
  type_chain_complex.mk Y @g
    abstract begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)⁻¹ ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (tcc_is_chain_complex X n _) ⬝ _,
      apply respect_pt
    end end

  theorem is_exact_at_t_transfer {X : type_chain_complex N} {Y : N → Type*}
    {g : Π{n : N}, Y (S n) →* Y n} (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (tcc_to_fn X n x) = g (e x)) {n : N}
    (H : is_exact_at_t X n) : is_exact_at_t (transfer_type_chain_complex X @g @e @p) n :=
  begin
    intro y q, esimp at *,
    have H2 : tcc_to_fn X n (e⁻¹ᵉ* y) = pt,
    begin
      refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      refine ap _ q ⬝ _,
      exact respect_pt e⁻¹ᵉ*
    end,
    cases (H _ H2) with x r,
    refine fiber.mk (e x) _,
    refine (p x)⁻¹ ⬝ _,
    refine ap e r ⬝ _,
    apply right_inv
  end

  -- move to init.equiv. This is inv_commute for A ≡ unit
  definition inv_commute1' {B C : Type} (f : B → C) [is_equiv f] (h : B → B) (h' : C → C)
    (p : Π(b : B), f (h b) = h' (f b)) (c : C) : f⁻¹ (h' c) = h (f⁻¹ c) :=
  eq_of_fn_eq_fn' f (right_inv f (h' c) ⬝ ap h' (right_inv f c)⁻¹ ⬝ (p (f⁻¹ c))⁻¹)

  definition inv_commute1 {B C : Type} (f : B ≃ C) (h : B → B) (h' : C → C)
    (p : Π(b : B), f (h b) =   h' (f b)) (c : C) : f⁻¹ (h' c) = h (f⁻¹ c) :=
  inv_commute1' (to_fun f) h h' p c

  definition fn_cast_eq_cast_fn {A : Type} {P Q : A → Type} {x y : A} (p : x = y)
    (f : Πx, P x → Q x) (z : P x) : f y (cast (ap P p) z) = cast (ap Q p) (f x z) :=
  by induction p; reflexivity

  definition cast_cast_inv {A : Type} {P : A → Type} {x y : A} (p : x = y) (z : P y) :
    cast (ap P p) (cast (ap P p⁻¹) z) = z :=
  by induction p; reflexivity

  definition cast_inv_cast {A : Type} {P : A → Type} {x y : A} (p : x = y) (z : P x) :
    cast (ap P p⁻¹) (cast (ap P p) z) = z :=
  by induction p; reflexivity

  -- more general transfer, where the base type can also change by an equivalence.
  definition transfer_type_chain_complex2 [constructor] {M : succ_str} {Y : M → Type*}
    (f : M ≃ N) (c : Π(m : M), S (f m) = f (S m))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{m}, X (f m) ≃* Y m)
    (p : Π{m} (x : X (S (f m))), e (tcc_to_fn X (f m) x) = g (e (cast (ap (λx, X x) (c m)) x)))
    : type_chain_complex M :=
  type_chain_complex.mk Y @g
    begin
      intro m,
      apply equiv_rect (equiv_of_pequiv e),
      apply equiv_rect (equiv_of_eq (ap (λx, X x) (c (S m)))), esimp,
      apply equiv_rect (equiv_of_eq (ap (λx, X (S x)) (c m))), esimp,
      intro x, refine ap g (p _)⁻¹ ⬝ _,
      refine ap g (ap e (fn_cast_eq_cast_fn (c m) (tcc_to_fn X) x)) ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (tcc_is_chain_complex X (f m) _) ⬝ _,
      apply respect_pt
    end

  definition is_exact_at_transfer2 {X : type_chain_complex N} {M : succ_str} {Y : M → Type*}
    (f : M ≃ N) (c : Π(m : M), S (f m) = f (S m))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{m}, X (f m) ≃* Y m)
    (p : Π{m} (x : X (S (f m))), e (tcc_to_fn X (f m) x) = g (e (cast (ap (λx, X x) (c m)) x)))
    {m : M} (H : is_exact_at_t X (f m))
    : is_exact_at_t (transfer_type_chain_complex2 X f c @g @e @p) m :=
  begin
    intro y q, esimp at *,
    have H2 : tcc_to_fn X (f m) ((equiv_of_eq (ap (λx, X x) (c m)))⁻¹ᵉ (e⁻¹ y)) = pt,
    begin
      refine _ ⬝ ap e⁻¹ᵉ* q ⬝ (respect_pt (e⁻¹ᵉ*)), apply eq_inv_of_eq, clear q, revert y,
      refine inv_homotopy_of_homotopy (pequiv.to_equiv e) _,
      apply inv_homotopy_of_homotopy, apply p
    end,
    induction (H _ H2) with x r,
    refine fiber.mk (e (cast (ap (λx, X x) (c (S m))) (cast (ap (λx, X (S x)) (c m)) x))) _,
    refine (p _)⁻¹ ⬝ _,
    refine ap e (fn_cast_eq_cast_fn (c m) (tcc_to_fn X) x) ⬝ _,
    refine ap (λx, e (cast _ x)) r ⬝ _,
    esimp [equiv.symm], rewrite [-ap_inv],
    refine ap e !cast_cast_inv ⬝ _,
    apply right_inv
  end

  -- definition trunc_type_chain_complex [constructor] (X : type_chain_complex N)
  --   (k : trunc_index) : type_chain_complex N :=
  -- type_chain_complex.mk
  --   (λn, ptrunc k (X n))
  --   (λn, ptrunc_functor k (tcc_to_fn X n))
  --   begin
  --     intro n x, esimp at *,
  --     refine trunc.rec _ x, -- why doesn't induction work here?
  --     clear x, intro x, esimp,
  --     exact ap tr (tcc_is_chain_complex X n x)
  --   end
  end

  /- actual (set) chain complexes -/
  structure chain_complex (N : succ_str) : Type :=
    (car : N → Set*)
    (fn : Π(n : N), car (S n) →* car n)
    (is_chain_complex : Π(n : N) (x : car (S (S n))), fn n (fn (S n) x) = pt)

  section
  variables {N : succ_str} (X : chain_complex N) (n : N)

  definition cc_to_car [unfold 2] [coercion] := @chain_complex.car
  definition cc_to_fn  [unfold 2] : X (S n) →* X n := @chain_complex.fn N X n
  definition cc_is_chain_complex  [unfold 2]
    : Π(x : X (S (S n))), cc_to_fn X n (cc_to_fn X (S n) x) = pt :=
  @chain_complex.is_chain_complex N X n

  -- important: these notions are shifted by one! (this is to avoid transports)
  definition is_exact_at [reducible] /- X n -/ : Type :=
  Π(x : X (S n)), cc_to_fn X n x = pt → image (cc_to_fn X (S n)) x

  definition is_exact [reducible] /- X -/ : Type := Π(n : N), is_exact_at X n

  -- definition chain_complex_from_left (X : chain_complex) : chain_complex :=
  -- chain_complex.mk (int.rec X (λn, punit))
  --   begin
  --     intro n, fconstructor,
  --     { induction n with n n,
  --       { exact @lcc_to_fn X n},
  --       { esimp, intro x, exact star}},
  --     { induction n with n n,
  --       { apply respect_pt},
  --       { reflexivity}}
  --   end
  --   begin
  --     intro n, induction n with n n,
  --     { exact lcc_is_chain_complex X},
  --     { esimp, intro x, reflexivity}
  --   end

  -- definition is_exact_from_left {X : chain_complex} {n : ℕ} (H : is_exact_at_l X n)
  --   : is_exact_at (chain_complex_from_left X) n :=
  -- H

  definition transfer_chain_complex [constructor] {Y : N → Set*}
    (g : Π{n : N}, Y (S n) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (e x)) : chain_complex N :=
  chain_complex.mk Y @g
    abstract begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)⁻¹ ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (cc_is_chain_complex X n _) ⬝ _,
      apply respect_pt
    end end

  theorem is_exact_at_transfer {X : chain_complex N} {Y : N → Set*}
    (g : Π{n : N}, Y (S n) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (e x))
    {n : N} (H : is_exact_at X n) : is_exact_at (transfer_chain_complex X @g @e @p) n :=
  begin
    intro y q, esimp at *,
    have H2 : cc_to_fn X n (e⁻¹ᵉ* y) = pt,
    begin
      refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      refine ap _ q ⬝ _,
      exact respect_pt e⁻¹ᵉ*
    end,
    induction (H _ H2) with x,
    induction x with x r,
    refine image.mk (e x) _,
    refine (p x)⁻¹ ⬝ _,
    refine ap e r ⬝ _,
    apply right_inv
  end

  definition trunc_chain_complex [constructor] (X : type_chain_complex N)
    : chain_complex N :=
  chain_complex.mk
    (λn, ptrunc 0 (X n))
    (λn, ptrunc_functor 0 (tcc_to_fn X n))
    begin
      intro n x, esimp at *,
      refine @trunc.rec _ _ _ (λH, !is_trunc_eq) _ x,
      clear x, intro x, esimp,
      exact ap tr (tcc_is_chain_complex X n x)
    end

  definition is_exact_at_trunc (X : type_chain_complex N) {n : N}
    (H : is_exact_at_t X n) : is_exact_at (trunc_chain_complex X) n :=
  begin
    intro x p, esimp at *,
    induction x with x, esimp at *,
    note q := !tr_eq_tr_equiv p,
    induction q with q,
    induction H x q with y r,
    refine image.mk (tr y) _,
    esimp, exact ap tr r
  end

  definition transfer_chain_complex2' [constructor] {M : succ_str} {Y : M → Set*}
    (f : N ≃ M) (c : Π(n : N), f (S n) = S (f n))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{n}, X n ≃* Y (f n))
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (c n ▸ e x)) : chain_complex M :=
  chain_complex.mk Y @g
    begin
      refine equiv_rect f _ _, intro n,
      have H : Π (x : Y (f (S (S n)))), g (c n ▸ g (c (S n) ▸ x)) = pt,
      begin
        apply equiv_rect (equiv_of_pequiv e), intro x,
        refine ap (λx, g (c n ▸ x)) (@p (S n) x)⁻¹ᵖ ⬝ _,
        refine (p _)⁻¹ ⬝ _,
        refine ap e (cc_is_chain_complex X n _) ⬝ _,
        apply respect_pt
      end,
      refine pi.pi_functor _ _ H,
      { intro x, exact (c (S n))⁻¹ ▸ (c n)⁻¹ ▸ x}, -- with implicit arguments, this is:
      -- transport (λx, Y x) (c (S n))⁻¹ (transport (λx, Y (S x)) (c n)⁻¹ x)
      { intro x, intro p, refine _ ⬝ p, rewrite [tr_inv_tr, fn_tr_eq_tr_fn (c n)⁻¹ @g, tr_inv_tr]}
    end

  definition is_exact_at_transfer2' {X : chain_complex N} {M : succ_str} {Y : M → Set*}
    (f : N ≃ M) (c : Π(n : N), f (S n) = S (f n))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{n}, X n ≃* Y (f n))
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (c n ▸ e x))
    {n : N} (H : is_exact_at X n) : is_exact_at (transfer_chain_complex2' X f c @g @e @p) (f n) :=
  begin
    intro y q, esimp at *,
    have H2 : cc_to_fn X n (e⁻¹ᵉ* ((c n)⁻¹ ▸ y)) = pt,
    begin
      refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      rewrite [tr_inv_tr, q],
      exact respect_pt e⁻¹ᵉ*
    end,
    induction (H _ H2) with x,
    induction x with x r,
    refine image.mk (c n ▸ c (S n) ▸ e x) _,
    rewrite [fn_tr_eq_tr_fn (c n) @g],
    refine ap (λx, c n ▸ x) (p x)⁻¹ ⬝ _,
    refine ap (λx, c n ▸ e x) r ⬝ _,
    refine ap (λx, c n ▸ x) !right_inv ⬝ _,
    apply tr_inv_tr,
  end

  -- structure group_chain_complex : Type :=
  --   (car : N → Group)
  --   (fn : Π(n : N), car (S n) →g car n)
  --   (is_chain_complex : Π{n : N} (x : car ((S n) + 1)), fn n (fn (S n) x) = 1)

  -- structure group_chain_complex : Type := -- chain complex on the naturals with maps going down
  --   (car : N → Group)
  --   (fn : Π(n : N), car (S n) →g car n)
  --   (is_chain_complex : Π{n : N} (x : car ((S n) + 1)), fn n (fn (S n) x) = 1)

  -- structure right_group_chain_complex : Type := -- chain complex on the naturals with maps going up
  --   (car : N → Group)
  --   (fn : Π(n : N), car n →g car (S n))
  --   (is_chain_complex : Π{n : N} (x : car n), fn (S n) (fn n x) = 1)

  -- definition  gcc_to_car [unfold 1] [coercion] := @group_chain_complex.car
  -- definition  gcc_to_fn  [unfold 1]            := @group_chain_complex.fn
  -- definition  gcc_is_chain_complex  [unfold 1] := @group_chain_complex.is_chain_complex
  -- definition lgcc_to_car [unfold 1] [coercion] := @left_group_chain_complex.car
  -- definition lgcc_to_fn  [unfold 1]            := @left_group_chain_complex.fn
  -- definition lgcc_is_chain_complex  [unfold 1] := @left_group_chain_complex.is_chain_complex
  -- definition rgcc_to_car [unfold 1] [coercion] := @right_group_chain_complex.car
  -- definition rgcc_to_fn  [unfold 1]            := @right_group_chain_complex.fn
  -- definition rgcc_is_chain_complex  [unfold 1] := @right_group_chain_complex.is_chain_complex

  -- -- important: these notions are shifted by one! (this is to avoid transports)
  -- definition is_exact_at_g [reducible] (X : group_chain_complex) (n : N) : Type :=
  -- Π(x : X (S n)), gcc_to_fn X n x = 1 → image (gcc_to_fn X (S n)) x
  -- definition is_exact_at_lg [reducible] (X : left_group_chain_complex) (n : N) : Type :=
  -- Π(x : X (S n)), lgcc_to_fn X n x = 1 → image (lgcc_to_fn X (S n)) x
  -- definition is_exact_at_rg [reducible] (X : right_group_chain_complex) (n : N) : Type :=
  -- Π(x : X (S n)), rgcc_to_fn X (S n) x = 1 → image (rgcc_to_fn X n) x

  -- definition is_exact_g   [reducible] (X : group_chain_complex) : Type :=
  -- Π(n : N), is_exact_at_g X n
  -- definition is_exact_lg [reducible] (X : left_group_chain_complex) : Type :=
  -- Π(n : N), is_exact_at_lg X n
  -- definition is_exact_rg [reducible] (X : right_group_chain_complex) : Type :=
  -- Π(n : N), is_exact_at_rg X n

  -- definition group_chain_complex_from_left (X : left_group_chain_complex) : group_chain_complex :=
  -- group_chain_complex.mk (int.rec X (λn, G0))
  --   begin
  --     intro n, fconstructor,
  --     { induction n with n n,
  --       { exact @lgcc_to_fn X n},
  --       { esimp, intro x, exact star}},
  --     { induction n with n n,
  --       { apply respect_mul},
  --       { intro g h, reflexivity}}
  --   end
  --   begin
  --     intro n, induction n with n n,
  --     { exact lgcc_is_chain_complex X},
  --     { esimp, intro x, reflexivity}
  --   end

  -- definition is_exact_g_from_left {X : left_group_chain_complex} {n : N} (H : is_exact_at_lg X n)
  --   : is_exact_at_g (group_chain_complex_from_left X) n :=
  -- H

  -- definition transfer_left_group_chain_complex [constructor] (X : left_group_chain_complex)
  --   {Y : N → Group} (g : Π{n : N}, Y (S n) →g Y n) (e : Π{n}, X n ≃* Y n)
  --   (p : Π{n} (x : X (S n)), e (lgcc_to_fn X n x) = g (e x)) : left_group_chain_complex :=
  -- left_group_chain_complex.mk Y @g
  --   begin
  --     intro n, apply equiv_rect (pequiv_of_equiv e), intro x,
  --     refine ap g (p x)⁻¹ ⬝ _,
  --     refine (p _)⁻¹ ⬝ _,
  --     refine ap e (lgcc_is_chain_complex X _) ⬝ _,
  --     exact respect_pt
  --   end

  -- definition is_exact_at_t_transfer {X : left_group_chain_complex} {Y : N → Type*}
  --   {g : Π{n : N}, Y (S n) →* Y n} (e : Π{n}, X n ≃* Y n)
  --   (p : Π{n} (x : X (S n)), e (lgcc_to_fn X n x) = g (e x)) {n : N}
  --   (H : is_exact_at_lg X n) : is_exact_at_lg (transfer_left_group_chain_complex X @g @e @p) n :=
  -- begin
  --   intro y q, esimp at *,
  --   have H2 : lgcc_to_fn X n (e⁻¹ᵉ* y) = pt,
  --   begin
  --     refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
  --     refine ap _ q ⬝ _,
  --     exact respect_pt e⁻¹ᵉ*
  --   end,
  --   cases (H _ H2) with x r,
  --   refine image.mk (e x) _,
  --   refine (p x)⁻¹ ⬝ _,
  --   refine ap e r ⬝ _,
  --   apply right_inv
  -- end

  -- TODO: move
  definition is_trunc_ptrunctype [instance] {n : trunc_index} (X : ptrunctype n)
    : is_trunc n (ptrunctype.to_pType X) :=
  trunctype.struct X

  /- a group where the point in the pointed corresponds with 1 in the group -/
  structure pgroup [class] (X : Type*) extends semigroup X, has_inv X :=
    (pt_mul : Πa, mul pt a = a)
    (mul_pt : Πa, mul a pt = a)
    (mul_left_inv_pt : Πa, mul (inv a) a = pt)

  definition group_of_pgroup [reducible] [instance] (X : Type*) [H : pgroup X]
    : group X :=
  ⦃group, H,
          one := pt,
          one_mul := pgroup.pt_mul ,
          mul_one := pgroup.mul_pt,
          mul_left_inv := pgroup.mul_left_inv_pt⦄

  definition pgroup_of_group (X : Type*) [H : group X] (p : one = pt :> X) : pgroup X :=
  begin
    cases X with X x, esimp at *, induction p,
    exact ⦃pgroup, H,
            pt_mul := one_mul,
            mul_pt := mul_one,
            mul_left_inv_pt := mul.left_inv⦄

  end

  -- the following theorems would also be true of the replace "is_contr" by "is_prop"
  definition is_embedding_of_trivial (X : chain_complex N) {n : N}
    (H : is_exact_at X n) [HX : is_contr (X (S (S n)))]
    [pgroup (X n)] [pgroup (X (S n))] [is_homomorphism (cc_to_fn X n)]
      : is_embedding (cc_to_fn X n) :=
  begin
    apply is_embedding_homomorphism,
    intro g p,
    induction H g p with v,
    induction v with x q,
    have r : pt = x, from !is_prop.elim,
    induction r,
    refine q⁻¹ ⬝ _,
    apply respect_pt
  end

  definition is_surjective_of_trivial (X : chain_complex N) {n : N}
    (H : is_exact_at X n) [HX : is_contr (X n)] : is_surjective (cc_to_fn X (S n)) :=
  begin
    intro g,
    refine trunc.elim _ (H g !is_prop.elim),
    apply tr
  end

  definition is_equiv_of_trivial (X : chain_complex N) {n : N}
    (H1 : is_exact_at X n) (H2 : is_exact_at X (S n))
    [HX1 : is_contr (X n)] [HX2 : is_contr (X (S (S (S n))))]
    [pgroup (X (S n))] [pgroup (X (S (S n)))] [is_homomorphism (cc_to_fn X (S n))]
    : is_equiv (cc_to_fn X (S n)) :=
  begin
    apply is_equiv_of_is_surjective_of_is_embedding,
    { apply is_embedding_of_trivial X, apply H2},
    { apply is_surjective_of_trivial X, apply H1},
  end

  end

end chain_complex
