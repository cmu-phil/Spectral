/-
Copyright (c) 2017 Floris van Doorn and Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Truncatedness and truncation of spectra
-/

import .basic
open int trunc eq is_trunc lift unit pointed equiv is_equiv algebra EM trunc_index

namespace spectrum

/- interactions of ptrunc / trunc with maxm2 -/
definition ptrunc_maxm2_change_int {k l : ℤ} (p : k = l) (X : Type*)
  : ptrunc (maxm2 k) X ≃* ptrunc (maxm2 l) X :=
ptrunc_change_index (ap maxm2 p) X

definition is_trunc_maxm2_change_int {k l : ℤ} (X : pType) (p : k = l)
  : is_trunc (maxm2 k) X → is_trunc (maxm2 l) X :=
by induction p; exact id

definition is_trunc_maxm2_loop {k : ℤ} {A : Type*} (H : is_trunc (maxm2 (k+1)) A) :
  is_trunc (maxm2 k) (Ω A) :=
begin
  induction k with k k,
    apply is_trunc_loop, exact H,
  apply is_contr_loop,
  cases k with k,
  { exact H },
  { apply is_trunc_succ, apply is_trunc_succ, exact H }
end

definition loop_ptrunc_maxm2_pequiv {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l) (X : Type*) :
  Ω (ptrunc l X) ≃* ptrunc (maxm2 k) (Ω X) :=
begin
  induction p,
  induction k with k k,
  { exact loop_ptrunc_pequiv k X },
  { refine pequiv_of_is_contr _ _ _ !is_trunc_trunc,
    apply is_contr_loop,
    cases k with k,
    { change is_set (trunc 0 X), apply _ },
    { change is_set (trunc -2 X), apply _ }}
end

definition loop_ptrunc_maxm2_pequiv_ptrunc_elim' {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l)
  {A B : Type*} (f : A →* B) {H : is_trunc l B} :
  Ω→ (ptrunc.elim l f) ∘* (loop_ptrunc_maxm2_pequiv p A)⁻¹ᵉ* ~*
  @ptrunc.elim (maxm2 k) _ _ (is_trunc_maxm2_loop (is_trunc_of_eq p⁻¹ H)) (Ω→ f) :=
begin
  induction p, induction k with k k,
  { refine pwhisker_right _ (ap1_phomotopy _) ⬝* @(ap1_ptrunc_elim k f) H,
    apply ptrunc_elim_phomotopy2, reflexivity },
  { apply phomotopy_of_is_contr_cod_pmap, exact is_trunc_maxm2_loop H }
end

definition loop_ptrunc_maxm2_pequiv_ptrunc_elim {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l)
  {A B : Type*} (f : A →* B) {H1 : is_trunc ((maxm2 k).+1) B } {H2 : is_trunc l B} :
  Ω→ (ptrunc.elim l f) ∘* (loop_ptrunc_maxm2_pequiv p A)⁻¹ᵉ* ~* ptrunc.elim (maxm2 k) (Ω→ f) :=
begin
  induction p, induction k with k k: esimp at H1,
  { refine pwhisker_right _ (ap1_phomotopy _) ⬝* ap1_ptrunc_elim k f,
    apply ptrunc_elim_phomotopy2, reflexivity },
  { apply phomotopy_of_is_contr_cod }
end

definition loop_ptrunc_maxm2_pequiv_ptr {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l) (A : Type*) :
  Ω→ (ptr l A) ~* (loop_ptrunc_maxm2_pequiv p A)⁻¹ᵉ* ∘* ptr (maxm2 k) (Ω A) :=
begin
  induction p, induction k with k k,
  { exact ap1_ptr k A },
  { apply phomotopy_pinv_left_of_phomotopy, apply phomotopy_of_is_contr_cod_pmap,
    apply is_trunc_trunc }
end

definition is_trunc_of_is_trunc_maxm2 (k : ℤ) (X : Type)
  : is_trunc (maxm2 k) X → is_trunc (max0 k) X :=
λ H, @is_trunc_of_le X _ _ (maxm2_le_maxm0 k) H

definition ptrunc_maxm2_pred {n m : ℤ} (A : Type*) (p : n - 1 = m) :
  ptrunc (maxm2 m) A ≃* ptrunc (trunc_index.pred (maxm2 n)) A :=
begin
  cases n with n, cases n with n, apply pequiv_of_is_contr,
        induction p, apply is_trunc_trunc,
      apply is_contr_ptrunc_minus_one,
    exact ptrunc_change_index (ap maxm2 (p⁻¹ ⬝ !add_sub_cancel)) A,
  exact ptrunc_change_index (ap maxm2 p⁻¹) A
end

definition ptrunc_maxm2_pred_nat {n : ℕ} {m l : ℤ} (A : Type*)
  (p : nat.succ n = l) (q : pred l = m) (r : maxm2 m = trunc_index.pred (maxm2 (nat.succ n))) :
  @ptrunc_maxm2_pred (nat.succ n) m A (ap pred p ⬝ q) ~* ptrunc_change_index r A :=
begin
  have ap maxm2 ((ap pred p ⬝ q)⁻¹ ⬝ add_sub_cancel n 1) = r, from !is_set.elim,
  induction this, reflexivity
end

/- truncatedness of spectra -/
definition is_strunc [reducible] (k : ℤ) (E : spectrum) : Type :=
Π (n : ℤ), is_trunc (maxm2 (k + n)) (E n)

definition is_strunc_change_int {k l : ℤ} (E : spectrum) (p : k = l)
  : is_strunc k E → is_strunc l E :=
begin induction p, exact id end

definition is_strunc_of_le {k l : ℤ} (E : spectrum) (H : k ≤ l)
  : is_strunc k E → is_strunc l E :=
begin
  intro T, intro n, exact is_trunc_of_le (E n) (maxm2_monotone (algebra.add_le_add_right H n)) _
end

definition is_strunc_pequiv_closed {k : ℤ} {E F : spectrum} (H : Πn, E n ≃* F n)
  (H2 : is_strunc k E) : is_strunc k F :=
λn, is_trunc_equiv_closed (maxm2 (k + n)) (H n) _

definition is_strunc_sunit (n : ℤ) : is_strunc n sunit :=
begin
  intro k, apply is_trunc_lift, apply is_trunc_unit
end

open option
definition is_strunc_add_point_spectrum {X : Type} {Y : X → spectrum} {s₀ : ℤ}
  (H : Πx, is_strunc s₀ (Y x)) : Π(x : X₊), is_strunc s₀ (add_point_spectrum Y x)
| (some x) := proof H x qed
| none     := begin intro k, apply is_trunc_lift, apply is_trunc_unit end

definition is_strunc_EM_spectrum (G : AbGroup)
  : is_strunc 0 (EM_spectrum G) :=
begin
  intro n, induction n with n n,
  { -- case ≥ 0
    apply is_trunc_maxm2_change_int (EM G n) (zero_add n)⁻¹,
    apply is_trunc_EM },
  { change is_contr (EM_spectrum G (-[1+n])),
    induction n with n IH,
    { -- case = -1
      apply is_contr_loop, exact is_trunc_EM G 0 },
    { -- case < -1
      apply is_trunc_loop, apply is_trunc_succ, exact IH }}
end

definition trivial_shomotopy_group_of_is_strunc (E : spectrum)
  {n k : ℤ} (K : is_strunc n E) (H : n < k)
  : is_contr (πₛ[k] E) :=
let m := n + (2 - k) in
have I : m < 2, from
  calc
    m = (2 - k) + n : int.add_comm n (2 - k)
  ... < (2 - k) + k : add_lt_add_left H (2 - k)
  ... = 2           : sub_add_cancel 2 k,
@trivial_homotopy_group_of_is_trunc (E (2 - k)) (max0 m) 2
  (is_trunc_of_is_trunc_maxm2 m (E (2 - k)) (K (2 - k)))
  (nat.succ_le_succ (max0_le_of_le (le_sub_one_of_lt I)))

/- truncation of spectra -/
definition strunc [constructor] (k : ℤ) (E : spectrum) : spectrum :=
spectrum.MK (λ(n : ℤ), ptrunc (maxm2 (k + n)) (E n))
            (λ(n : ℤ), ptrunc_pequiv_ptrunc (maxm2 (k + n)) (equiv_glue E n)
              ⬝e* (loop_ptrunc_maxm2_pequiv (ap maxm2 (add.assoc k n 1)) (E (n+1)))⁻¹ᵉ*)

definition strunc_change_int [constructor] {k l : ℤ} (E : spectrum) (p : k = l) :
  strunc k E →ₛ strunc l E :=
begin induction p, reflexivity end

definition is_strunc_strunc (k : ℤ) (E : spectrum)
  : is_strunc k (strunc k E) :=
λ n, is_trunc_trunc (maxm2 (k + n)) (E n)

definition is_strunc_strunc_pred (X : spectrum) (k : ℤ) : is_strunc k (strunc (k - 1) X) :=
λn, @(is_trunc_of_le _ (maxm2_monotone (add_le_add_right (sub_one_le k) n))) !is_strunc_strunc

definition is_strunc_strunc_of_is_strunc (k : ℤ) {l : ℤ} {E : spectrum} (H : is_strunc l E)
  : is_strunc l (strunc k E) :=
λ n, !is_trunc_trunc_of_is_trunc

definition str [constructor] (k : ℤ) (E : spectrum) : E →ₛ strunc k E :=
smap.mk (λ n, ptr (maxm2 (k + n)) (E n))
  abstract begin
    intro n,
    apply psquare_of_phomotopy,
    refine !passoc ⬝* pwhisker_left _ !ptr_natural ⬝* _,
    refine !passoc⁻¹* ⬝* pwhisker_right _ !loop_ptrunc_maxm2_pequiv_ptr⁻¹*,
  end end

definition strunc_elim [constructor] {k : ℤ} {E F : spectrum} (f : E →ₛ F)
  (H : is_strunc k F) : strunc k E →ₛ F :=
smap.mk (λn, ptrunc.elim (maxm2 (k + n)) (f n))
  abstract begin
    intro n,
    apply psquare_of_phomotopy,
    symmetry,
    refine !passoc⁻¹* ⬝* pwhisker_right _ !loop_ptrunc_maxm2_pequiv_ptrunc_elim' ⬝* _,
    refine @(ptrunc_elim_ptrunc_functor _ _ _) _ ⬝* _,
    refine _ ⬝* @(ptrunc_elim_pcompose _ _ _) _ _,
      apply is_trunc_maxm2_loop,
      refine is_trunc_of_eq _ (H (n+1)), exact ap maxm2 (add.assoc k n 1)⁻¹,
    apply ptrunc_elim_phomotopy2,
    apply phomotopy_of_psquare,
    apply ptranspose,
    apply smap.glue_square
  end end

definition strunc_functor [constructor] (k : ℤ) {E F : spectrum} (f : E →ₛ F) :
  strunc k E →ₛ strunc k F :=
strunc_elim (str k F ∘ₛ f) (is_strunc_strunc k F)

/- truncated spectra -/
structure truncspectrum (n : ℤ) :=
  (carrier : spectrum)
  (struct : is_strunc n carrier)

notation n `-spectrum` := truncspectrum n

attribute truncspectrum.carrier [coercion]

definition genspectrum_of_truncspectrum [coercion] (n : ℤ) : n-spectrum → gen_spectrum +ℤ :=
λ E, truncspectrum.carrier E

/- Comment (by Floris):

  I think we should really not bundle truncated spectra up,
  unless we are interested in the type of truncated spectra (e.g. when proving n-spectrum ≃ ...).
  Properties of truncated a spectrum should just be stated with two assumptions
  (X : spectrum) (H : is_strunc n X)
-/

/- truncatedness of spi and sp_cotensor assuming the domain has a level of connectedness -/
section

  open is_conn

  definition is_conn_maxm1_of_maxm2 (A : Type*) (n : ℤ)
    : is_conn (maxm2 n) A → is_conn (maxm1m1 n).+1 A :=
  begin
    intro H, induction n with n n,
    { exact H },
    { exact is_conn_minus_one A (tr pt) }
  end

  definition is_trunc_maxm2_of_maxm1 (A : Type*) (n : ℤ)
    : is_trunc (maxm1m1 n).+1 A → is_trunc (maxm2 n) A :=
  begin
    intro H, induction n with n n,
    { exact H},
    { apply is_contr_of_merely_prop,
      { exact H },
      { exact tr pt } }
  end

  variables (A : Type*) (n : ℤ) [H : is_conn (maxm2 n) A]
  include H

  definition is_trunc_maxm2_ppi (k l : ℤ) (H3 : l ≤ n+1+k) (P : A → Type*)
    (H2 : Πa, is_trunc (maxm2 l) (P a)) : is_trunc (maxm2 k) (Π*(a : A), P a) :=
  is_trunc_maxm2_of_maxm1 (Π*(a : A), P a) k
    (@is_trunc_ppi_of_is_conn A (maxm1m1 n) (is_conn_maxm1_of_maxm2 A n H) (maxm1m1 k) _
      (le.trans (maxm2_monotone H3) (maxm2_le n k)) P H2)

  definition is_strunc_spi_of_is_conn (k l : ℤ) (H3 : l ≤ n+1+k) (P : A → spectrum)
    (H2 : Πa, is_strunc l (P a)) : is_strunc k (spi A P) :=
  begin
    intro m, unfold spi,
    exact is_trunc_maxm2_ppi A n (k+m) _ (le.trans (add_le_add_right H3 _)
            (le_of_eq (add.assoc (n+1) k m))) (λ a, P a m) (λa, H2 a m)
  end

end

definition is_strunc_spi_of_le {A : Type*} (k n : ℤ) (H : n ≤ k) (P : A → spectrum)
  (H2 : Πa, is_strunc n (P a)) : is_strunc k (spi A P) :=
begin
  assert K : n ≤ -[1+ 0] + 1 + k,
  { krewrite (int.zero_add k), exact H },
  { exact @is_strunc_spi_of_is_conn A (-[1+ 0]) (is_conn.is_conn_minus_two A) k _ K P H2 }
end

definition is_strunc_spi {A : Type*} (n : ℤ) (P : A → spectrum) (H : Πa, is_strunc n (P a))
  : is_strunc n (spi A P) :=
is_strunc_spi_of_le n n !le.refl P H

definition is_strunc_sp_cotensor (n : ℤ) (A : Type*) {Y : spectrum} (H : is_strunc n Y)
  : is_strunc n (sp_cotensor A Y) :=
is_strunc_pequiv_closed (λn, !pppi_pequiv_ppmap) (is_strunc_spi n (λa, Y) (λa, H))

definition is_strunc_sp_ucotensor (n : ℤ) (A : Type) {Y : spectrum} (H : is_strunc n Y)
  : is_strunc n (sp_ucotensor A Y) :=
λk, !pi.is_trunc_arrow

end spectrum
