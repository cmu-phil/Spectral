import .spectrum .EM

namespace int

  -- TODO move this
  open trunc_index nat algebra
  section
  private definition maxm2_le.lemma₁ {n k : ℕ} : n+(1:int) + -[1+ k] ≤ n :=
  le.intro (
    calc n + 1 + -[1+ k] + k = n + 1 - (k + 1) + k : by reflexivity
                         ... = n                   : sorry)

  private definition maxm2_le.lemma₂ {n : ℕ} {k : ℤ} : -[1+ n] + 1 + k ≤ k :=
  le.intro (
    calc -[1+ n] + 1 + k + n = - (n + 1) + 1 + k + n : by reflexivity
                         ... = k                     : sorry)

  definition maxm2_le (n k : ℤ) : maxm2 (n+1+k) ≤ (maxm1m1 n).+1+2+(maxm1m1 k) :=
  begin
    rewrite [-(maxm1_eq_succ n)],
    induction n with n n,
    { induction k with k k,
      { induction k with k IH,
        { apply le.tr_refl },
        { exact succ_le_succ IH } },
      { exact trunc_index.le_trans (maxm2_monotone maxm2_le.lemma₁)
                                   (maxm2_le_maxm1 n) } },
    { krewrite (add_plus_two_comm -1 (maxm1m1 k)),
      rewrite [-(maxm1_eq_succ k)],
      exact trunc_index.le_trans (maxm2_monotone maxm2_le.lemma₂)
                                 (maxm2_le_maxm1 k) }
  end
  end

end int

open int trunc eq is_trunc lift unit pointed equiv is_equiv algebra EM

namespace spectrum

definition ptrunc_maxm2_change_int {k l : ℤ} (p : k = l) (X : Type*)
  : ptrunc (maxm2 k) X ≃* ptrunc (maxm2 l) X :=
pequiv_ap (λ n, ptrunc (maxm2 n) X) p

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

definition ptrunc_elim_phomotopy2 [constructor] (k : ℕ₋₂) {A B : Type*} {f g : A →* B} (H₁ : is_trunc k B)
  (H₂ : is_trunc k B) (p : f ~* g) : @ptrunc.elim k A B H₁ f ~* @ptrunc.elim k A B H₂ g :=
begin
  fapply phomotopy.mk,
  { intro x, induction x with a, exact p a },
  { exact to_homotopy_pt p }
end

definition loop_ptrunc_maxm2_pequiv_ptrunc_elim' {k : ℤ} {l : ℕ₋₂} (p : maxm2 (k+1) = l)
  {A B : Type*} (f : A →* B) {H : is_trunc l B} :
  Ω→ (ptrunc.elim l f) ∘* (loop_ptrunc_maxm2_pequiv p A)⁻¹ᵉ* ~*
  @ptrunc.elim (maxm2 k) _ _ (is_trunc_maxm2_loop (is_trunc_of_eq p⁻¹ H)) (Ω→ f) :=
begin
  induction p, induction k with k k,
  { refine pwhisker_right _ (ap1_phomotopy _) ⬝* @(ap1_ptrunc_elim k f) H,
    apply ptrunc_elim_phomotopy2, reflexivity },
  { apply phomotopy_of_is_contr_cod, exact is_trunc_maxm2_loop H }
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
  { apply phomotopy_pinv_left_of_phomotopy, apply phomotopy_of_is_contr_cod, apply is_trunc_trunc }
end

definition is_trunc_of_is_trunc_maxm2 (k : ℤ) (X : Type)
  : is_trunc (maxm2 k) X → is_trunc (max0 k) X :=
λ H, @is_trunc_of_le X _ _ (maxm2_le_maxm0 k) H

definition strunc [constructor] (k : ℤ) (E : spectrum) : spectrum :=
spectrum.MK (λ(n : ℤ), ptrunc (maxm2 (k + n)) (E n))
            (λ(n : ℤ), ptrunc_pequiv_ptrunc (maxm2 (k + n)) (equiv_glue E n)
              ⬝e* (loop_ptrunc_maxm2_pequiv (ap maxm2 (add.assoc k n 1)) (E (n+1)))⁻¹ᵉ*)

definition strunc_change_int [constructor] {k l : ℤ} (E : spectrum) (p : k = l) :
  strunc k E →ₛ strunc l E :=
begin induction p, reflexivity end

definition is_strunc [reducible] (k : ℤ) (E : spectrum) : Type :=
Π (n : ℤ), is_trunc (maxm2 (k + n)) (E n)

definition is_strunc_change_int {k l : ℤ} (E : spectrum) (p : k = l)
  : is_strunc k E → is_strunc l E :=
begin induction p, exact id end

definition is_strunc_of_le {k l : ℤ} (E : spectrum) (H : k ≤ l)
  : is_strunc k E → is_strunc l E :=
begin
  intro T, intro n, exact is_trunc_of_le (E n)
    (maxm2_monotone (algebra.add_le_add_right H n))
end

definition is_strunc_strunc (k : ℤ) (E : spectrum)
  : is_strunc k (strunc k E) :=
λ n, is_trunc_trunc (maxm2 (k + n)) (E n)

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

structure truncspectrum (n : ℤ) :=
  (carrier : spectrum)
  (struct : is_strunc n carrier)

notation n `-spectrum` := truncspectrum n

attribute truncspectrum.carrier [coercion]

definition genspectrum_of_truncspectrum (n : ℤ)
  : n-spectrum → gen_spectrum +ℤ :=
λ E, truncspectrum.carrier E

attribute genspectrum_of_truncspectrum [coercion]

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

  definition is_trunc_maxm2_ppi (k : ℤ) (P : A → (maxm2 (n+1+k))-Type*)
    : is_trunc (maxm2 k) (Π*(a : A), P a) :=
  is_trunc_maxm2_of_maxm1 (Π*(a : A), P a) k
    (@is_trunc_ppi_of_is_conn A (maxm1m1 n)
      (is_conn_maxm1_of_maxm2 A n H) (maxm1m1 k)
      (λ a, ptrunctype.mk (P a) (is_trunc_of_le (P a) (maxm2_le n k)) pt))

  definition is_strunc_spi_of_is_conn (k : ℤ) (P : A → (n+1+k)-spectrum)
    : is_strunc k (spi A P) :=
  begin
    intro m, unfold spi,
    exact is_trunc_maxm2_ppi A n (k+m)
      (λ a, ptrunctype.mk (P a m)
       (is_trunc_maxm2_change_int (P a m) (add.assoc (n+1) k m)
         (truncspectrum.struct (P a) m)) pt)
  end

end

definition is_strunc_spi (A : Type*) (k n : ℤ) (H : n ≤ k) (P : A → n-spectrum)
  : is_strunc k (spi A P) :=
begin
  assert K : n ≤ -[1+ 0] + 1 + k,
  { krewrite (int.zero_add k), exact H },
  { exact @is_strunc_spi_of_is_conn A (-[1+ 0])
    (is_conn.is_conn_minus_two A) k
    (λ a, truncspectrum.mk (P a) (is_strunc_of_le (P a) K
          (truncspectrum.struct (P a)))) }
end

end spectrum
