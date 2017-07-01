import ..algebra.module_exact_couple .strunc

open eq spectrum trunc is_trunc pointed int EM algebra left_module fiber lift equiv is_equiv

/- Eilenberg MacLane spaces are the fibers of the Postnikov system of a type -/

definition postnikov_map [constructor] (A : Type*) (n : ℕ₋₂) : ptrunc (n.+1) A →* ptrunc n A :=
ptrunc.elim (n.+1) !ptr

definition ptrunc_functor_postnikov_map {A B : Type*} (n : ℕ₋₂) (f : A →* B) :
  ptrunc_functor n f ∘* postnikov_map A n ~* ptrunc.elim (n.+1) (!ptr ∘* f) :=
begin
  fapply phomotopy.mk,
  { intro x, induction x with a, reflexivity },
  { reflexivity }
end

section
open nat is_conn group
definition pfiber_postnikov_map (A : Type*) (n : ℕ) :
  pfiber (postnikov_map A n) ≃* EM_type A (n+1) :=
begin
  symmetry, apply EM_type_pequiv,
  { symmetry, refine _ ⬝g ghomotopy_group_ptrunc (n+1) A,
    exact chain_complex.LES_isomorphism_of_trivial_cod _ _
      (trivial_homotopy_group_of_is_trunc _ (self_lt_succ n))
      (trivial_homotopy_group_of_is_trunc _ (le_succ _)) },
  { apply is_conn_fun_trunc_elim,  apply is_conn_fun_tr },
  { have is_trunc (n+1) (ptrunc n.+1 A), from !is_trunc_trunc,
    have is_trunc ((n+1).+1) (ptrunc n A), by do 2 apply is_trunc_succ, apply is_trunc_trunc,
    apply is_trunc_pfiber }
end
end

definition postnikov_map_natural {A B : Type*} (f : A →* B) (n : ℕ₋₂) :
  psquare (postnikov_map A n) (postnikov_map B n)
          (ptrunc_functor (n.+1) f) (ptrunc_functor n f) :=
!ptrunc_functor_postnikov_map ⬝* !ptrunc_elim_ptrunc_functor⁻¹*

definition is_equiv_postnikov_map (A : Type*) {n k : ℕ₋₂} [HA : is_trunc k A] (H : k ≤ n) :
  is_equiv (postnikov_map A n) :=
begin
  apply is_equiv_of_equiv_of_homotopy
    (ptrunc_pequiv_ptrunc_of_is_trunc (trunc_index.le.step H) H HA),
  intro x, induction x, reflexivity
end

definition encode_ap1_gen_tr (n : ℕ₋₂) {A : Type*} {a a' : A} (p : a = a') :
  trunc.encode (ap1_gen tr idp idp p) = tr p :> trunc n (a = a') :=
by induction p; reflexivity

definition ap1_postnikov_map (A : Type*) (n : ℕ₋₂) :
  psquare (Ω→ (postnikov_map A (n.+1))) (postnikov_map (Ω A) n)
          (loop_ptrunc_pequiv (n.+1) A) (loop_ptrunc_pequiv n A) :=
have psquare (postnikov_map (Ω A) n) (Ω→ (postnikov_map A (n.+1)))
             (loop_ptrunc_pequiv (n.+1) A)⁻¹ᵉ* (loop_ptrunc_pequiv n A)⁻¹ᵉ*,
begin
  refine _ ⬝* !ap1_ptrunc_elim⁻¹*, apply pinv_left_phomotopy_of_phomotopy,
  fapply phomotopy.mk,
  { intro x, induction x with p, exact !encode_ap1_gen_tr⁻¹ },
  { reflexivity }
end,
this⁻¹ᵛ*

definition is_strunc_strunc_pred (X : spectrum) (k : ℤ) : is_strunc k (strunc (k - 1) X) :=
λn, @(is_trunc_of_le _ (maxm2_monotone (add_le_add_right (sub_one_le k) n))) !is_strunc_strunc

definition postnikov_smap [constructor] (X : spectrum) (k : ℤ) :
  strunc k X →ₛ strunc (k - 1) X :=
strunc_elim (str (k - 1) X) (is_strunc_strunc_pred X k)

definition postnikov_smap_phomotopy [constructor] (X : spectrum) (k : ℤ) (n : ℤ) :
  postnikov_smap X k n ~* postnikov_map (X n) (maxm2 (k - 1 + n)) ∘*
  sorry :=
sorry

section atiyah_hirzebruch
  parameters {X : Type*} (Y : X → spectrum) (s₀ : ℤ) (H : Πx, is_strunc s₀ (Y x))

  definition atiyah_hirzebruch_exact_couple : exact_couple rℤ Z2 :=
  @exact_couple_sequence (λs, strunc s (spi X Y)) (postnikov_smap (spi X Y))

  definition is_bounded_atiyah_hirzebruch : is_bounded atiyah_hirzebruch_exact_couple :=
  is_bounded_sequence _ s₀ (λn, n - 1)
    begin
      intro s n H,
      exact sorry
    end
    begin
      intro s n H, apply trivial_shomotopy_group_of_is_strunc,
        apply is_strunc_strunc,
      exact lt_of_le_sub_one H,
    end

end atiyah_hirzebruch
