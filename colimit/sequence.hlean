/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import ..move_to_lib types.fin types.trunc

open nat eq equiv sigma sigma.ops is_equiv is_trunc trunc prod fiber function

namespace seq_colim

  definition seq_diagram [reducible] (A : ℕ → Type) : Type := Π⦃n⦄, A n → A (succ n)

  structure Seq_diagram : Type :=
    (carrier : ℕ → Type)
    (struct : seq_diagram carrier)

  definition is_equiseq [reducible] {A : ℕ → Type} (f : seq_diagram A) : Type :=
  forall (n : ℕ), is_equiv (@f n)

  structure Equi_seq : Type :=
    (carrier : ℕ → Type)
    (maps : seq_diagram carrier)
    (prop : is_equiseq maps)

  protected abbreviation Mk [constructor] := Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [coercion]

  variables {A A' : ℕ → Type} (f : seq_diagram A) (f' : seq_diagram A') {n m k : ℕ}
  include f

  definition lrep {n m : ℕ} (H : n ≤ m) : A n → A m :=
  begin
    induction H with m H fs,
    { exact id },
    { exact @f m ∘ fs }
  end

  definition lrep_irrel_pathover {n m m' : ℕ} (H₁ : n ≤ m) (H₂ : n ≤ m') (p : m = m') (a : A n) :
    lrep f H₁ a =[p] lrep f H₂ a :=
  apo (λm H, lrep f H a) !is_prop.elimo

  definition lrep_irrel {n m : ℕ} (H₁ H₂ : n ≤ m) (a : A n) : lrep f H₁ a = lrep f H₂ a :=
  ap (λH, lrep f H a) !is_prop.elim

  definition lrep_eq_transport {n m : ℕ} (H : n ≤ m) (p : n = m) (a : A n) : lrep f H a = transport A p a :=
  begin induction p, exact lrep_irrel f H (nat.le_refl n) a end

  definition lrep_irrel2 {n m : ℕ} (H₁ H₂ : n ≤ m) (a : A n) :
    lrep_irrel f (le.step H₁) (le.step H₂) a = ap (@f m) (lrep_irrel f H₁ H₂ a) :=
  begin
    have H₁ = H₂, from !is_prop.elim, induction this,
    refine ap02 _ !is_prop_elim_self ⬝ _ ⬝ ap02 _(ap02 _ !is_prop_elim_self⁻¹),
    reflexivity
  end

  definition lrep_eq_lrep_irrel {n m m' : ℕ} (H₁ : n ≤ m) (H₂ : n ≤ m') (a₁ a₂ : A n) (p : m = m') :
    (lrep f H₁ a₁ = lrep f H₁ a₂) ≃ (lrep f H₂ a₁ = lrep f H₂ a₂) :=
  equiv_apd011 (λm H, lrep f H a₁ = lrep f H a₂) (is_prop.elimo p H₁ H₂)

  definition lrep_eq_lrep_irrel_natural {n m m' : ℕ} {H₁ : n ≤ m} (H₂ : n ≤ m') {a₁ a₂ : A n}
    (p : m = m') (q : lrep f H₁ a₁ = lrep f H₁ a₂) :
    lrep_eq_lrep_irrel f (le.step H₁) (le.step H₂) a₁ a₂ (ap succ p) (ap (@f m) q) =
    ap (@f m') (lrep_eq_lrep_irrel f H₁ H₂ a₁ a₂ p q) :=
  begin
    esimp [lrep_eq_lrep_irrel],
    symmetry,
    refine fn_tro_eq_tro_fn2 _ (λa₁ a₂, ap (@f _)) q ⬝ _,
    refine ap (λx, x ▸o _) (@is_prop.elim _ _ _ _),
    apply is_trunc_pathover
  end

  definition is_equiv_lrep [constructor] [Hf : is_equiseq f] {n m : ℕ} (H : n ≤ m) :
    is_equiv (lrep f H) :=
  begin
    induction H with m H Hlrepf,
    { apply is_equiv_id },
    { exact is_equiv_compose (@f _) (lrep f H) },
  end

  local attribute is_equiv_lrep [instance]
  definition lrep_back [reducible] [Hf : is_equiseq f] {n m : ℕ} (H : n ≤ m) : A m → A n :=
  (lrep f H)⁻¹ᶠ

  section generalized_lrep

  -- definition lrep_pathover_lrep0 [reducible] (k : ℕ) (a : A 0) : lrep f k a =[nat.zero_add k] lrep0 f k a :=
  -- begin induction k with k p, constructor, exact pathover_ap A succ (apo f p) end

  /- lreplace le_of_succ_le with this -/

  definition lrep_f {n m : ℕ} (H : succ n ≤ m) (a : A n) :
    lrep f H (f a) = lrep f (le_step_left H) a :=
  begin
    induction H with m H p,
    { reflexivity },
    { exact ap (@f m) p }
  end

  definition lrep_lrep {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) (a : A n) :
    lrep f H2 (lrep f H1 a) = lrep f (nat.le_trans H1 H2) a :=
  begin
    induction H2 with k H2 p,
    { reflexivity },
    { exact ap (@f k) p }
  end

  -- -- this should be a squareover
  -- definition lrep_lrep_succ (k l : ℕ) (a : A n) :
  --   lrep_lrep f k (succ l) a = change_path (idontwanttoprovethis n l k)
  --   (lrep_f f k (lrep f l a) ⬝o
  --    lrep_lrep f (succ k) l a ⬝o
  --    pathover_ap _ (λz, n + z) (apd (λz, lrep f z a) (succ_add l k)⁻¹ᵖ)) :=
  -- begin
  --   induction k with k IH,
  --   { constructor},
  --   { exact sorry}
  -- end

  definition f_lrep {n m : ℕ} (H : n ≤ m) (a : A n) : f (lrep f H a) = lrep f (le.step H) a := idp

  definition rep (m : ℕ) (a : A n) : A (n + m) :=
  lrep f (le_add_right n m) a

  definition rep0 (m : ℕ) (a : A 0) : A m :=
  lrep f (zero_le m) a

  definition rep_pathover_rep0 {n : ℕ} (a : A 0) : rep f n a =[nat.zero_add n] rep0 f n a :=
  !lrep_irrel_pathover

  -- definition old_rep (m : ℕ) (a : A n) : A (n + m) :=
  -- by induction m with m y; exact a; exact f y

  -- definition rep_eq_old_rep (m : ℕ) (a : A n) : rep f m a = old_rep f m a :=
  -- by induction m with m p; reflexivity; exact ap (@f _) p

  definition rep_f (k : ℕ) (a : A n) :
    pathover A (rep f k (f a)) (succ_add n k) (rep f (succ k) a) :=
  begin
    induction k with k IH,
    { constructor },
    { unfold [succ_add], apply pathover_ap, exact apo f IH}
  end

  definition rep_rep (k l : ℕ) (a : A n) :
    pathover A (rep f k (rep f l a)) (nat.add_assoc n l k) (rep f (l + k) a) :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end

  variables {f f'}
  definition is_trunc_fun_lrep (k : ℕ₋₂) (H : n ≤ m) (H2 : Πn, is_trunc_fun k (@f n)) :
    is_trunc_fun k (lrep f H) :=
  begin induction H with m H IH, apply is_trunc_fun_id, exact is_trunc_fun_compose k (H2 m) IH end

  definition is_conn_fun_lrep (k : ℕ₋₂) (H : n ≤ m) (H2 : Πn, is_conn_fun k (@f n)) :
    is_conn_fun k (lrep f H) :=
  begin induction H with m H IH, apply is_conn_fun_id, exact is_conn_fun_compose k (H2 m) IH end

  definition lrep_natural (τ : Π⦃n⦄, A n → A' n) (p : Π⦃n⦄ (a : A n), τ (f a) = f' (τ a))
    {n m : ℕ} (H : n ≤ m) (a : A n) : τ (lrep f H a) = lrep f' H (τ a) :=
  begin
    induction H with m H IH, reflexivity, exact p (lrep f H a) ⬝ ap (@f' m) IH
  end

  definition rep_natural (τ : Π⦃n⦄, A n → A' n) (p : Π⦃n⦄ (a : A n), τ (f a) = f' (τ a))
    {n : ℕ} (k : ℕ) (a : A n) : τ (rep f k a) = rep f' k (τ a) :=
  lrep_natural τ p _ a

  definition rep0_natural (τ : Π⦃n⦄, A n → A' n) (p : Π⦃n⦄ (a : A n), τ (f a) = f' (τ a))
    (k : ℕ) (a : A 0) : τ (rep0 f k a) = rep0 f' k (τ a) :=
  lrep_natural τ p _ a

  variables (f f')

  end generalized_lrep

  section shift

  definition shift_diag [unfold_full] : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  definition kshift_diag [unfold_full] (k : ℕ) : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  definition kshift_diag' [unfold_full] (k : ℕ) : seq_diagram (λn, A (n + k)) :=
  λn a, transport A (succ_add n k)⁻¹ (f a)

  definition lrep_kshift_diag {n m k : ℕ} (H : m ≤ k) (a : A (n + m)) :
    lrep (kshift_diag f n) H a = lrep f (nat.add_le_add_left2 H n) a :=
  by induction H with k H p; reflexivity; exact ap (@f _) p

  end shift

  section constructions

    omit f

    definition constant_seq (X : Type) : seq_diagram (λ n, X) :=
    λ n x, x

    definition seq_diagram_arrow_left [unfold_full] (X : Type) : seq_diagram (λn, X → A n) :=
    λn g x, f (g x)

    definition seq_diagram_prod [unfold_full] : seq_diagram (λn, A n × A' n) :=
    λn, prod_functor (@f n) (@f' n)

    open fin
    definition seq_diagram_fin [unfold_full] : seq_diagram fin :=
    lift_succ2

    definition id0_seq [unfold_full] (a₁ a₂ : A 0) : ℕ → Type :=
    λ k, rep0 f k a₁ = rep0 f k a₂

    definition id0_seq_diagram [unfold_full] (a₁ a₂ : A 0) : seq_diagram (id0_seq f a₁ a₂) :=
    λ (k : ℕ) (p : rep0 f k a₁ = rep0 f k a₂), ap (@f k) p

    definition id_seq [unfold_full] (n : ℕ) (a₁ a₂ : A n) : ℕ → Type :=
    λ k, rep f k a₁ = rep f k a₂

    definition id_seq_diagram [unfold_full] (n : ℕ) (a₁ a₂ : A n) : seq_diagram (id_seq f n a₁ a₂) :=
    λ (k : ℕ) (p : rep f k a₁ = rep f k a₂), ap (@f (n + k)) p

    definition trunc_diagram [unfold_full] (k : ℕ₋₂) (f : seq_diagram A) :
      seq_diagram (λn, trunc k (A n)) :=
    λn, trunc_functor k (@f n)

  end constructions

  section over

  variable {A}
  variable (P : Π⦃n⦄, A n → Type)

  definition seq_diagram_over : Type := Π⦃n⦄ {a : A n}, P a → P (f a)

  definition weakened_sequence [unfold_full] : seq_diagram_over f (λn a, A' n) :=
  λn a a', f' a'

  definition id0_seq_diagram_over [unfold_full] (a₀ : A 0) :
    seq_diagram_over f (λn a, rep0 f n a₀ = a) :=
  λn a p, ap (@f n) p

  variable (g : seq_diagram_over f P)
  variables {f P}

  definition seq_diagram_of_over [unfold_full] {n : ℕ} (a : A n) :
    seq_diagram (λk, P (rep f k a)) :=
  λk p, g p

  definition seq_diagram_sigma [unfold 6] : seq_diagram (λn, Σ(x : A n), P x) :=
  λn v, ⟨f v.1, g v.2⟩

  variables (f P)

  theorem rep_f_equiv [constructor] (a : A n) (k : ℕ) :
    P (lrep f (le_add_right (succ n) k) (f a)) ≃ P (lrep f (le_add_right n (succ k)) a) :=
  equiv_apd011 P (rep_f f k a)

  theorem rep_rep_equiv [constructor] (a : A n) (k l : ℕ) :
    P (rep f (l + k) a) ≃ P (rep f k (rep f l a)) :=
  (equiv_apd011 P (rep_rep f k l a))⁻¹ᵉ

  end over

  omit f
  -- do we need to generalize this to the case where the bottom sequence consists of equivalences?
  definition seq_diagram_pi {X : Type} {A : X → ℕ → Type} (g : Π⦃x n⦄, A x n → A x (succ n)) :
    seq_diagram (λn, Πx, A x n) :=
  λn f x, g (f x)

  variables {f f'}
  definition seq_diagram_over_fiber (g : Π⦃n⦄, A' n → A n)
    (p : Π⦃n⦄ (a : A' n), g (f' a) = f (g a)) : seq_diagram_over f (λn, fiber (@g n)) :=
  λk a, fiber_functor (@f' k) (@f k) (@p k) idp

  definition seq_diagram_fiber (g : Π⦃n⦄, A' n → A n) (p : Π⦃n⦄ (a : A' n), g (f' a) = f (g a))
    {n : ℕ} (a : A n) : seq_diagram (λk, fiber (@g (n + k)) (rep f k a)) :=
  seq_diagram_of_over (seq_diagram_over_fiber g p) a

  definition seq_diagram_fiber0 (g : Π⦃n⦄, A' n → A n) (p : Π⦃n⦄ (a : A' n), g (f' a) = f (g a))
    (a : A 0) : seq_diagram (λk, fiber (@g k) (rep0 f k a)) :=
  λk, fiber_functor (@f' k) (@f k) (@p k) idp


end seq_colim
