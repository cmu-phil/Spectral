import types.pointed types.int types.fiber

open algebra nat int pointed unit sigma fiber sigma.ops eq equiv prod is_trunc

namespace tactic
definition replace (old : expr) (new : with_expr) (loc : location) : tactic := builtin
end tactic

namespace LES

  structure LES : Type :=
    (car : ℤ → Type*)
    (fn : Π{n : ℤ}, car (n + 1) →* car n)
    (chain_complex : Π{n : ℤ} (x : car ((n + 1) + 1)), fn (fn x) = pt)
    (is_exact : Π{n : ℤ} (x : car (n + 1)), fn x = pt → Σ(y : car ((n + 1) + 1)), fn y = x)

  structure LLES : Type := -- "left" long exact sequence
    (car : ℕ → Type*)
    (fn : Π{n : ℕ}, car (n + 1) →* car n)
    (chain_complex : Π{n : ℕ} (x : car ((n + 1) + 1)), fn (fn x) = pt)
    (is_exact : Π{n : ℕ} (x : car (n + 1)), fn x = pt → Σ(y : car ((n + 1) + 1)), fn y = x)

  structure RLES : Type := -- "right" long exact sequence
    (car : ℕ → Type*)
    (fn : Π{n : ℕ}, car n →* car (n + 1))
    (chain_complex : Π{n : ℕ} (x : car n), fn (fn x) = pt)
    (is_exact : Π{n : ℕ} (x : car (n + 1)), fn x = pt → Σ(y : car n), fn y = x)

  open LES LLES RLES

  /-
    this construction is currently wrong. We need to add one element between the sequence
  -/
/-  definition LES_of_LLES (X : LLES) : LES :=
  LES.mk (int.rec (car X) (λn, Unit))
    begin
      intro n, fconstructor,
      { induction n with n n,
        { exact @fn X n},
        { esimp, intro x, exact star}},
      { induction n with n n,
        { apply respect_pt},
        { reflexivity}}
    end
    begin
      intro n, induction n with n n,
      { exact chain_complex X},
      { esimp, intro x, reflexivity}
    end
    begin
      intro n, induction n with n n,
      { exact is_exact X},
      { esimp, intro x p, exact sorry}
    end-/

  definition pfiber {X Y : Type*} (f : X →* Y) : Type* :=
  pointed.MK (fiber f pt) (fiber.mk pt !respect_pt)

  definition fiber_sequence_helper (v : Σ(X Y : Type*), X →* Y) : Σ(Z X : Type*), Z →* X :=
  ⟨pfiber v.2.2, v.1, pmap.mk point rfl⟩

  definition fiber_sequence_carrier {X Y : Type*} (f : X →* Y) (n : ℕ) : Type* :=
  nat.cases_on n Y (λk, (iterate fiber_sequence_helper k ⟨X, Y, f⟩).1)

  definition fiber_sequence_arrow {X Y : Type*} (f : X →* Y) (n : ℕ)
    : fiber_sequence_carrier f (n + 1) →* fiber_sequence_carrier f n :=
  nat.cases_on n f proof (λk, pmap.mk point rfl) qed

  /- Definition 8.4.3 -/
  definition fiber_sequence.{u} {X Y : Pointed.{u}} (f : X →* Y) : LLES.{u} :=
  begin
    fconstructor,
    { exact fiber_sequence_carrier f},
    { exact fiber_sequence_arrow f},
    { intro n x, cases n with n,
      { exact point_eq x},
      { exact point_eq x}},
    { intro n x p, cases n with n,
      { exact ⟨fiber.mk x p, rfl⟩},
      { exact ⟨fiber.mk x p, rfl⟩}}
  end

  -- move to types.sigma
  definition sigma_assoc_comm_equiv {A : Type} (B C : A → Type)
    : (Σ(v : Σa, B a), C v.1) ≃ (Σ(u : Σa, C a), B u.1) :=
  calc    (Σ(v : Σa, B a), C v.1)
        ≃ (Σa (b : B a), C a)     : sigma_assoc_equiv
    ... ≃ (Σa, B a × C a)         : sigma_equiv_sigma_id (λa, !equiv_prod)
    ... ≃ (Σa, C a × B a)         : sigma_equiv_sigma_id (λa, !prod_comm_equiv)
    ... ≃ (Σa (c : C a), B a)     : sigma_equiv_sigma_id (λa, !equiv_prod)
    ... ≃ (Σ(u : Σa, C a), B u.1) : sigma_assoc_equiv

  /- Lemma 8.4.4(i) -/
  definition fiber_sequence_carrier_equiv0.{u} {X Y : Pointed.{u}} (f : X →* Y)
    : fiber_sequence_carrier f 3 ≃ Ω Y :=
  calc
    fiber_sequence_carrier f 3 ≃ fiber (fiber_sequence_arrow f 1) pt          : erfl
    ... ≃ Σ(x : fiber_sequence_carrier f 2), fiber_sequence_arrow f 1 x = pt  : fiber.sigma_char
    ... ≃ Σ(v : fiber f pt), fiber_sequence_arrow f 1 v = pt                  : erfl
    ... ≃ Σ(v : Σ(x : X), f x = pt), fiber_sequence_arrow f 1 (fiber.mk v.1 v.2) = pt
                                               : sigma_equiv_sigma_left !fiber.sigma_char
    ... ≃ Σ(v : Σ(x : X), f x = pt), v.1 = pt  : erfl
    ... ≃ Σ(v : Σ(x : X), x = pt), f v.1 = pt  : sigma_assoc_comm_equiv
    ... ≃ f !center.1 = pt                     : sigma_equiv_of_is_contr_left _
    ... ≃ f pt = pt                            : erfl
    ... ≃ pt = pt                              : by exact !equiv_eq_closed_left !respect_pt
    ... ≃ Ω Y                                  : erfl

  /- (generalization of) Lemma 8.4.4(ii) -/
  definition fiber_sequence_carrier_equiv1.{u} {X Y : Pointed.{u}} (f : X →* Y) (n : ℕ)
    : fiber_sequence_carrier f (n+4) ≃ Ω(fiber_sequence_carrier f (n+1)) :=
  calc
    fiber_sequence_carrier f (n+4) ≃ fiber (fiber_sequence_arrow f (n+2)) pt : erfl
    ... ≃ Σ(x : fiber_sequence_carrier f _), fiber_sequence_arrow f (n+2) x = pt
      : fiber.sigma_char
    ... ≃ Σ(x : fiber (fiber_sequence_arrow f (n+1)) pt), fiber_sequence_arrow f _ x = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), fiber_sequence_arrow f _ x = pt),
            fiber_sequence_arrow f _ (fiber.mk v.1 v.2) = pt
      : by exact sigma_equiv_sigma !fiber.sigma_char (λa, erfl)
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), fiber_sequence_arrow f _ x = pt),
            v.1 = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), x = pt),
            fiber_sequence_arrow f _ v.1 = pt
      : sigma_assoc_comm_equiv
    ... ≃ fiber_sequence_arrow f _ !center.1 = pt
      : @(sigma_equiv_of_is_contr_left _) !is_contr_sigma_eq'
    ... ≃ fiber_sequence_arrow f _ pt = pt
      : erfl
    ... ≃ pt = pt
      : by exact !equiv_eq_closed_left !respect_pt
   ... ≃ Ω(fiber_sequence_carrier f (n+1)) : erfl

  /- Lemma 8.4.4 (i)(ii), combined -/
  attribute bit0 bit1 add nat.add [reducible]
  definition fiber_sequence_carrier_equiv {X Y : Type*} (f : X →* Y) (n : ℕ)
    : fiber_sequence_carrier f (n+3) ≃ Ω(fiber_sequence_carrier f n) :=
  nat.cases_on n (fiber_sequence_carrier_equiv0 f) (fiber_sequence_carrier_equiv1 f)


end LES
