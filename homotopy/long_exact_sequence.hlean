import types.pointed types.int types.fiber

open algebra nat int pointed unit sigma fiber sigma.ops eq equiv prod is_trunc equiv.ops

namespace chain_complex

  structure chain_complex : Type :=
    (car : ℤ → Type*)
    (fn : Π{n : ℤ}, car (n + 1) →* car n)
    (is_chain_complex : Π{n : ℤ} (x : car ((n + 1) + 1)), fn (fn x) = pt)

  structure left_chain_complex : Type := -- chain complex on the naturals with maps going down
    (car : ℕ → Type*)
    (fn : Π{n : ℕ}, car (n + 1) →* car n)
    (is_chain_complex : Π{n : ℕ} (x : car ((n + 1) + 1)), fn (fn x) = pt)

  structure right_chain_complex : Type := -- chain complex on the naturals with maps going up
    (car : ℕ → Type*)
    (fn : Π{n : ℕ}, car n →* car (n + 1))
    (is_chain_complex : Π{n : ℕ} (x : car n), fn (fn x) = pt)

  definition cc_to_car [coercion] := @chain_complex.car
  definition cc_to_fn := @chain_complex.fn
  definition cc_is_chain_complex := @chain_complex.is_chain_complex
  definition lcc_to_car [coercion] := @left_chain_complex.car
  definition lcc_to_fn := @left_chain_complex.fn
  definition lcc_is_chain_complex := @left_chain_complex.is_chain_complex
  definition rcc_to_car [coercion] := @right_chain_complex.car
  definition rcc_to_fn := @right_chain_complex.fn
  definition rcc_is_chain_complex := @right_chain_complex.is_chain_complex

  -- note: these notions are shifted by one!
  definition is_exact_at [reducible] (X : chain_complex) (n : ℤ) : Type :=
  Π(x : X (n + 1)), cc_to_fn X x = pt → Σ(y : X ((n + 1) + 1)), cc_to_fn X y = x
  definition is_exact_at_l [reducible] (X : left_chain_complex) (n : ℕ) : Type :=
  Π(x : X (n + 1)), lcc_to_fn X x = pt → Σ(y : X ((n + 1) + 1)), lcc_to_fn X y = x
  definition is_exact_at_r [reducible] (X : right_chain_complex) (n : ℕ) : Type :=
  Π(x : X (n + 1)), rcc_to_fn X x = pt → Σ(y : X n), rcc_to_fn X y = x

  definition is_exact   [reducible] (X : chain_complex) : Type := Π(n : ℤ), is_exact_at X n
  definition is_exact_l [reducible] (X : left_chain_complex) : Type := Π(n : ℕ), is_exact_at_l X n
  definition is_exact_r [reducible] (X : right_chain_complex) : Type := Π(n : ℕ), is_exact_at_r X n

  definition chain_complex_from_left (X : left_chain_complex) : chain_complex :=
  chain_complex.mk (int.rec X (λn, Unit))
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

  -- move to pointed
  definition pfiber [constructor] {X Y : Type*} (f : X →* Y) : Type* :=
  pointed.MK (fiber f pt) (fiber.mk pt !respect_pt)

  definition pequiv_of_equiv [constructor] {A B : Type*} (f : A ≃ B) (H : f pt = pt) : A ≃* B :=
  pequiv.mk' (pmap.mk f H)

  definition fiber_sequence_helper [constructor] (v : Σ(X Y : Type*), X →* Y)
    : Σ(Z X : Type*), Z →* X :=
  ⟨pfiber v.2.2, v.1, pmap.mk point rfl⟩

  definition fiber_sequence_carrier {X Y : Type*} (f : X →* Y) (n : ℕ) : Type* :=
  nat.cases_on n Y (λk, (iterate fiber_sequence_helper k ⟨X, Y, f⟩).1)

  definition fiber_sequence_fun {X Y : Type*} (f : X →* Y) (n : ℕ)
    : fiber_sequence_carrier f (n + 1) →* fiber_sequence_carrier f n :=
  nat.cases_on n f proof (λk, pmap.mk point rfl) qed

  /- Definition 8.4.3 -/
  definition fiber_sequence.{u} {X Y : Pointed.{u}} (f : X →* Y) : left_chain_complex.{u} :=
  begin
    fconstructor,
    { exact fiber_sequence_carrier f},
    { exact fiber_sequence_fun f},
    { intro n x, cases n with n,
      { exact point_eq x},
      { exact point_eq x}}
  end

  definition is_exact_fiber_sequence {X Y : Type*} (f : X →* Y) : is_exact_l (fiber_sequence f) :=
  begin
    intro n x p, cases n with n,
    { exact ⟨fiber.mk x p, rfl⟩},
    { exact ⟨fiber.mk x p, rfl⟩}
  end

  -- move to types.sigma
  definition sigma_assoc_comm_equiv [constructor] {A : Type} (B C : A → Type)
    : (Σ(v : Σa, B a), C v.1) ≃ (Σ(u : Σa, C a), B u.1) :=
  calc    (Σ(v : Σa, B a), C v.1)
        ≃ (Σa (b : B a), C a)     : !sigma_assoc_equiv⁻¹
    ... ≃ (Σa, B a × C a)         : sigma_equiv_sigma_id (λa, !equiv_prod)
    ... ≃ (Σa, C a × B a)         : sigma_equiv_sigma_id (λa, !prod_comm_equiv)
    ... ≃ (Σa (c : C a), B a)     : sigma_equiv_sigma_id (λa, !equiv_prod)
    ... ≃ (Σ(u : Σa, C a), B u.1) : sigma_assoc_equiv

  attribute is_equiv_sigma_functor is_equiv.is_equiv_id pequiv.mk' [constructor]
  attribute sigma.eta [unfold 3]

--  set_option pp.notation false
  /- Lemma 8.4.4(i) -/
  definition fiber_sequence_carrier_equiv0.{u} {X Y : Pointed.{u}} (f : X →* Y)
    : fiber_sequence_carrier f 3 ≃* Ω Y :=
  pequiv_of_equiv
    (calc
    fiber_sequence_carrier f 3 ≃ fiber (fiber_sequence_fun f 1) pt          : erfl
    ... ≃ Σ(x : fiber_sequence_carrier f 2), fiber_sequence_fun f 1 x = pt  : fiber.sigma_char
    ... ≃ Σ(v : fiber f pt), fiber_sequence_fun f 1 v = pt                  : erfl
    ... ≃ Σ(v : Σ(x : X), f x = pt), fiber_sequence_fun f 1 (fiber.mk v.1 v.2) = pt
                                               : sigma_equiv_sigma_left !fiber.sigma_char
    ... ≃ Σ(v : Σ(x : X), f x = pt), v.1 = pt  : erfl
    ... ≃ Σ(v : Σ(x : X), x = pt), f v.1 = pt  : sigma_assoc_comm_equiv
    ... ≃ f !center.1 = pt                     : sigma_equiv_of_is_contr_left _
    ... ≃ f pt = pt                            : erfl
    ... ≃ pt = pt                              : by exact !equiv_eq_closed_left !respect_pt
    ... ≃ Ω Y                                  : erfl)
    begin
      change (respect_pt f)⁻¹ ⬝
             ((center_eq ⟨Pointed.Point X, refl (Pointed.Point X)⟩)⁻¹ ▸ respect_pt f) = idp,
      rewrite tr_constant,
      apply con.left_inv
    end

  /- (generalization of) Lemma 8.4.4(ii) -/
  definition fiber_sequence_carrier_equiv1.{u} {X Y : Pointed.{u}} (f : X →* Y) (n : ℕ)
    : fiber_sequence_carrier f (n+4) ≃* Ω(fiber_sequence_carrier f (n+1)) :=
  pequiv_of_equiv
    (calc
    fiber_sequence_carrier f (n+4) ≃ fiber (fiber_sequence_fun f (n+2)) pt : erfl
    ... ≃ Σ(x : fiber_sequence_carrier f _), fiber_sequence_fun f (n+2) x = pt
      : fiber.sigma_char
    ... ≃ Σ(x : fiber (fiber_sequence_fun f (n+1)) pt), fiber_sequence_fun f _ x = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), fiber_sequence_fun f _ x = pt),
            fiber_sequence_fun f _ (fiber.mk v.1 v.2) = pt
      : by exact sigma_equiv_sigma !fiber.sigma_char (λa, erfl)
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), fiber_sequence_fun f _ x = pt),
            v.1 = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), x = pt),
            fiber_sequence_fun f _ v.1 = pt
      : sigma_assoc_comm_equiv
    ... ≃ fiber_sequence_fun f _ !center.1 = pt
      : @(sigma_equiv_of_is_contr_left _) !is_contr_sigma_eq'
    ... ≃ fiber_sequence_fun f _ pt = pt
      : erfl
    ... ≃ pt = pt
      : by exact !equiv_eq_closed_left !respect_pt
    ... ≃ Ω(fiber_sequence_carrier f (n+1)) : erfl)
    begin reflexivity end

  /- Lemma 8.4.4 (i)(ii), combined -/
  definition fiber_sequence_carrier_equiv {X Y : Type*} (f : X →* Y) (n : ℕ)
    : fiber_sequence_carrier f (n+3) ≃* Ω(fiber_sequence_carrier f n) :=
  nat.cases_on n (fiber_sequence_carrier_equiv0 f) (fiber_sequence_carrier_equiv1 f)
exit
  /- Lemma 8.4.4(iii) -/
  definition fiber_sequence_function0 {X Y : Type*} (f : X →* Y)
    : Π(x : fiber_sequence_carrier f 4), ap1 f (fiber_sequence_carrier_equiv f 1 x)⁻¹ᵖ =
      fiber_sequence_carrier_equiv f 0 (fiber_sequence_fun f 3 x) :=
  take (x : fiber (fiber_sequence_fun f 2) pt),
  obtain (v : fiber (fiber_sequence_fun f 1) pt) (q : _), from x,
  begin
      unfold [fiber_sequence_carrier_equiv,fiber_sequence_carrier_equiv0,fiber_sequence_carrier_equiv1,equiv.trans, equiv.symm, pequiv._trans_of_to_pmap],
      esimp [sigma_assoc_equiv, equiv.symm, equiv.trans], unfold [fiber_sequence_fun, fiber_sequence_carrier]
  end

end chain_complex
