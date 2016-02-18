-- Section 8.3

import types.trunc types.pointed homotopy.connectedness homotopy.sphere homotopy.circle algebra.group algebra.homotopy_group

open eq is_trunc is_equiv nat equiv trunc function circle algebra pointed is_trunc.trunc_index homotopy

notation `Floris` := sorry

-- Lemma 8.3.1

definition homotopy_group_of_is_trunc (A : Type*) (n : ℕ) (p : is_trunc n A) : ∀(k : ℕ), πG[n+k+1] A = G0 :=
begin
  intro k,
  apply @trivial_group_of_is_contr,
  apply is_trunc_trunc_of_is_trunc,
  apply is_contr_loop_of_is_trunc,
  apply @is_trunc_of_leq A n _,
  induction k with k IHk,
  {
    apply is_trunc.trunc_index.le.refl
  },
  {
    induction n with n IHn,
    {
      constructor
    },
    {
      exact Floris
    }
  }
end

-- Lemma 8.3.2
definition trunc_trunc (n k : ℕ₋₂) (p : k ≤ n) (A : Type)
  : trunc k (trunc n A) ≃ trunc k A :=
sorry

definition zero_trunc_of_iterated_loop_space (k : ℕ) (A : Type*)
  : trunc 0 (Ω[k] A) ≃ Ω[k](pointed.MK (trunc k A) (tr pt)) := 
sorry


definition homotopy_group_of_is_conn (A : Type*) (n : ℕ) (p : is_conn n A) : ∀(k : ℕ), (k ≤ n) → is_contr(π[k] A) :=
begin
  intros k H,
  exact Floris
end

-- Corollary 8.3.3
