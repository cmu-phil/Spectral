import types.pointed types.int types.fiber

open algebra nat int pointed unit sigma fiber sigma.ops eq

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
  definition LES_of_LLES (X : LLES) : LES :=
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
    end

  definition fiber_sequence_helper (v : Σ(X Y : Type*), X →* Y) : Σ(Z X : Type*), Z →* X :=
  ⟨pointed_fiber v.2.2 pt, v.1, pmap.mk point rfl⟩
  -- match v with
  -- | ⟨X, Y, f⟩ := ⟨pointed_fiber f pt, X, pmap.mk point rfl⟩
  -- end

exit
  definition fiber_sequence.{u} {X Y : Pointed.{u}} (f : X →* Y) : LLES.{u} :=
  begin
    fconstructor,
    { intro n, cases n with n,
      { exact Y},
      { exact (iterate fiber_sequence_helper n ⟨X, Y, f⟩).1}},
    { intro n, cases n with n,
      { exact f},
      { exact pmap.mk point rfl}},
    { intro n x, exact sorry},
    { exact sorry}
  end

end LES
