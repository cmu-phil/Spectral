import ..algebra.module_exact_couple .strunc

open eq spectrum trunc is_trunc pointed int EM algebra left_module fiber lift

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


-- definition postnikov_map_int (X : Type*) (k : ℤ) :
--   ptrunc (maxm2 (k + 1)) X →* ptrunc (maxm2 k) X :=
-- begin
--   induction k with k k,
--     exact postnikov_map X k,
--   exact !pconst
-- end

-- definition postnikov_map_int_natural {A B : Type*} (f : A →* B) (k : ℤ) :
--   psquare (postnikov_map_int A k) (postnikov_map_int B k)
--           (ptrunc_int_functor (k+1) f) (ptrunc_int_functor k f) :=
-- begin
--   induction k with k k,
--     exact postnikov_map_natural f k,
--   apply psquare_of_phomotopy, exact !pcompose_pconst ⬝* !pconst_pcompose⁻¹*
-- end

-- definition postnikov_map_int_natural_pequiv {A B : Type*} (f : A ≃* B) (k : ℤ) :
--   psquare (postnikov_map_int A k) (postnikov_map_int B k)
--           (ptrunc_int_pequiv_ptrunc_int (k+1) f) (ptrunc_int_pequiv_ptrunc_int k f) :=
-- begin
--   induction k with k k,
--     exact postnikov_map_natural f k,
--   apply psquare_of_phomotopy, exact !pcompose_pconst ⬝* !pconst_pcompose⁻¹*
-- end

-- definition pequiv_ap_natural2 {X A : Type} (B C : X → A → Type*) {a a' : X → A}
--   (p : a ~ a')
--   (s : X → X) (f : Πx a, B x a →* C (s x) a) (x : X) :
--   psquare (pequiv_ap (B x) (p x)) (pequiv_ap (C (s x)) (p x)) (f x (a x)) (f x (a' x)) :=
-- begin induction p using homotopy.rec_on_idp, exact phrfl end

-- definition pequiv_ap_natural3 {X A : Type} (B C : X → A → Type*) {a a' : A}
--   (p : a = a')
--   (s : X → X) (x : X) (f : Πx a, B x a →* C (s x) a) :
--   psquare (pequiv_ap (B x) p) (pequiv_ap (C (s x)) p) (f x a) (f x a') :=
-- begin induction p, exact phrfl end

-- definition postnikov_smap (X : spectrum) (k : ℤ) :
--   strunc (k+1) X →ₛ strunc k X :=
-- smap.mk (λn, postnikov_map_int (X n) (k + n) ∘* ptrunc_int_change_int _ !norm_num.add_comm_middle)
--         (λn, begin
--                exact sorry
-- --             exact (_ ⬝vp* !ap1_pequiv_ap) ⬝h* (!postnikov_map_int_natural_pequiv ⬝v* _ ⬝v* _) ⬝vp* !ap1_pcompose,
--              end)


-- section atiyah_hirzebruch
--   parameters {X : Type*} (Y : X → spectrum)

--   definition atiyah_hirzebruch_exact_couple : exact_couple rℤ spectrum.I :=
--   @exact_couple_sequence (λs, strunc s (spi X (λx, Y x)))
--                          (λs, !postnikov_smap ∘ₛ strunc_change_int _ !succ_pred⁻¹)

-- --  parameters (k : ℕ) (H : Π(x : X) (n : ℕ), is_trunc (k + n) (Y x n))



-- end atiyah_hirzebruch
