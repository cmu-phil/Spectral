/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Cofiber sequence of a pointed map
-/

import .cohomology .pushout

open pointed eq cohomology sigma sigma.ops fiber cofiber chain_complex nat succ_str algebra prod group pushout int

namespace cohomology

  definition pred_fun {A : ℕ → Type*} (f : Πn, A n →* A (n+1)) (n : ℕ) : A (pred n) →* A n :=
  begin cases n with n, exact pconst (A 0) (A 0), exact f n end

  definition type_chain_complex_snat' [constructor] (A : ℕ → Type*) (f : Πn, A n →* A (n+1))
    (p : Πn (x : A n), f (n+1) (f n x) = pt) : type_chain_complex -ℕ :=
  type_chain_complex.mk A (pred_fun f)
    begin
      intro n, cases n with n, intro x, reflexivity, cases n with n,
      intro x, exact respect_pt (f 0), exact p n
    end

  definition chain_complex_snat' [constructor] (A : ℕ → Set*) (f : Πn, A n →* A (n+1))
    (p : Πn (x : A n), f (n+1) (f n x) = pt) : chain_complex -ℕ :=
  chain_complex.mk A (pred_fun f)
    begin
      intro n, cases n with n, intro x, reflexivity, cases n with n,
      intro x, exact respect_pt (f 0), exact p n
    end

  definition is_exact_at_t_snat' [constructor] {A : ℕ → Type*} (f : Πn, A n →* A (n+1))
    (p : Πn (x : A n), f (n+1) (f n x) = pt) (q : Πn x, f (n+1) x = pt → fiber (f n) x) (n : ℕ)
    : is_exact_at_t (type_chain_complex_snat' A f p) (n+2) :=
  q n

  definition cofiber_sequence_helper [constructor] (v : Σ(X Y : Type*), X →* Y)
    : Σ(Y Z : Type*), Y →* Z :=
  ⟨v.2.1, pcofiber v.2.2, pcod v.2.2⟩

  definition cofiber_sequence_helpern (v : Σ(X Y : Type*), X →* Y) (n : ℕ)
    : Σ(Z X : Type*), Z →* X :=
  iterate cofiber_sequence_helper n v

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)
  include f

  definition cofiber_sequence_carrier (n : ℕ) : Type* :=
  (cofiber_sequence_helpern ⟨X, Y, f⟩ n).1

  definition cofiber_sequence_fun (n : ℕ)
    : cofiber_sequence_carrier n →* cofiber_sequence_carrier (n+1) :=
  (cofiber_sequence_helpern ⟨X, Y, f⟩ n).2.2

  definition cofiber_sequence : type_chain_complex.{0 u} -ℕ :=
  begin
    fapply type_chain_complex_snat',
    { exact cofiber_sequence_carrier },
    { exact cofiber_sequence_fun },
    { intro n x, exact pcod_pcompose (cofiber_sequence_fun n) x }
  end

  end

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y) (H : cohomology_theory.{u})
  include f

  definition cohomology_groups [reducible] : -3ℤ → AbGroup
  | (n, fin.mk 0 p) := H n X
  | (n, fin.mk 1 p) := H n Y
  | (n, fin.mk k p) := H n (pcofiber f)

--   definition cohomology_groups_pequiv_loop_spaces2 [reducible]
--     : Π(n : -3ℤ), ptrunc 0 (loop_spaces2 n) ≃* cohomology_groups n
--   | (n, fin.mk 0 p) := by reflexivity
--   | (n, fin.mk 1 p) := by reflexivity
--   | (n, fin.mk 2 p) := by reflexivity
--   | (n, fin.mk (k+3) p) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition coboundary (n : ℤ) : H (pred n) X →g H n (pcofiber f) :=
  H ^→ n (pcofiber_pcod f ∘* pcod (pcod f)) ∘g (Hsusp_neg H n X)⁻¹ᵍ

  definition cohomology_groups_fun : Π(n : -3ℤ), cohomology_groups (S n) →g cohomology_groups n
  | (n, fin.mk 0 p) := proof H ^→ n f qed
  | (n, fin.mk 1 p) := proof H ^→ n (pcod f) qed
  | (n, fin.mk 2 p) := proof coboundary n qed
  | (n, fin.mk (k+3) p) := begin exfalso, apply lt_le_antisymm p, apply le_add_left end

  -- definition cohomology_groups_fun_pcohomology_loop_spaces_fun2 [reducible]
  --   : Π(n : -3ℤ), cohomology_groups_pequiv_loop_spaces2 n ∘* ptrunc_functor 0 (loop_spaces_fun2 n) ~*
  --     cohomology_groups_fun n ∘* cohomology_groups_pequiv_loop_spaces2 (S n)
  -- | (n, fin.mk 0 p) := by reflexivity
  -- | (n, fin.mk 1 p) := by reflexivity
  -- | (n, fin.mk 2 p) :=
  --   begin
  --     refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹*,
  --     refine !ptrunc_functor_pcompose
  --   end
  -- | (n, fin.mk (k+3) p) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  open cohomology_theory

  definition cohomology_groups_chain_0 (n : ℤ) (x : H n (pcofiber f)) : H ^→ n f (H ^→ n (pcod f) x) = 1 :=
  begin
    refine (Hcompose H n (pcod f) f x)⁻¹ ⬝ _,
    refine Hhomotopy H n (pcod_pcompose f) x ⬝ _,
    exact Hconst H n x
  end

  definition cohomology_groups_chain_1 (n : ℤ) (x : H (pred n) X) : H ^→ n (pcod f) (coboundary n x) = 1 :=
  begin
    refine (Hcompose H n (pcofiber_pcod f ∘* pcod (pcod f)) (pcod f) ((Hsusp_neg H n X)⁻¹ᵍ x))⁻¹ ⬝ _,
    refine Hhomotopy H n (!passoc ⬝* pwhisker_left _ !pcod_pcompose ⬝* !pcompose_pconst) _ ⬝ _,
    exact Hconst H n _
  end

  definition cohomology_groups_chain_2 (n : ℤ) (x : H (pred n) Y) : coboundary n (H ^→ (pred n) f x) = 1 :=
  begin
    exact sorry
    -- refine ap (H ^→ n (pcofiber_pcod f ∘* pcod (pcod f))) _ ⬝ _,
--Hsusp_neg_inv_natural H n (pcofiber_pcod f ∘* pcod (pcod f)) _
  end

  definition cohomology_groups_chain : Π(n : -3ℤ) (x : cohomology_groups (S (S n))),
    cohomology_groups_fun n (cohomology_groups_fun (S n) x) = 1
  | (n, fin.mk 0 p) := cohomology_groups_chain_0 n
  | (n, fin.mk 1 p) := cohomology_groups_chain_1 n
  | (n, fin.mk 2 p) := cohomology_groups_chain_2 n
  | (n, fin.mk (k+3) p) := begin exfalso, apply lt_le_antisymm p, apply le_add_left end

  definition LES_of_cohomology_groups [constructor] : chain_complex -3ℤ :=
  chain_complex.mk (λn, cohomology_groups n) (λn, pmap_of_homomorphism (cohomology_groups_fun n)) cohomology_groups_chain

  definition is_exact_LES_of_cohomology_groups : is_exact LES_of_cohomology_groups :=
  begin
    intro n,
    exact sorry
  end

  end

end cohomology
