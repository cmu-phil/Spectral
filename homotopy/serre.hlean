import ..algebra.spectral_sequence .strunc .cohomology

open eq spectrum trunc is_trunc pointed int EM algebra left_module fiber lift equiv is_equiv
     cohomology group sigma unit is_conn
set_option pp.binder_types true

/- Eilenberg MacLane spaces are the fibers of the Postnikov system of a type -/

namespace pointed
definition postnikov_map [constructor] (A : Type*) (n : ℕ₋₂) : ptrunc (n.+1) A →* ptrunc n A :=
ptrunc.elim (n.+1) (ptr n A)

definition ptrunc_functor_postnikov_map {A B : Type*} (n : ℕ₋₂) (f : A →* B) :
  ptrunc_functor n f ∘* postnikov_map A n ~* ptrunc.elim (n.+1) (!ptr ∘* f) :=
begin
  fapply phomotopy.mk,
  { intro x, induction x with a, reflexivity },
  { reflexivity }
end

section
open nat group
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

end pointed open pointed

namespace spectrum
/- begin move -/
definition is_strunc_strunc_pred (X : spectrum) (k : ℤ) : is_strunc k (strunc (k - 1) X) :=
λn, @(is_trunc_of_le _ (maxm2_monotone (add_le_add_right (sub_one_le k) n))) !is_strunc_strunc

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

definition EM_type_pequiv_EM (A : spectrum) (n k : ℤ) (l : ℕ) (p : n + k = l) :
  EM_type (A k) l ≃* EM (πₛ[n] A) l :=
begin
  symmetry,
  cases l with l,
  { exact shomotopy_group_pequiv_homotopy_group A p },
  { cases l with l,
    { apply EM1_pequiv_EM1, exact shomotopy_group_isomorphism_homotopy_group A p },
    { apply EMadd1_pequiv_EMadd1 (l+1), exact shomotopy_group_isomorphism_homotopy_group A p }}
end
/- end move -/

definition postnikov_smap [constructor] (X : spectrum) (k : ℤ) :
  strunc k X →ₛ strunc (k - 1) X :=
strunc_elim (str (k - 1) X) (is_strunc_strunc_pred X k)

definition postnikov_map_pred (A : Type*) (n : ℕ₋₂) :
  ptrunc n A →* ptrunc (trunc_index.pred n) A :=
begin cases n with n, exact !pid, exact postnikov_map A n end

definition pfiber_postnikov_map_pred (A : Type*) (n : ℕ) :
  pfiber (postnikov_map_pred A n) ≃* EM_type A n :=
begin
  cases n with n,
    apply pfiber_pequiv_of_is_contr, apply is_contr_ptrunc_minus_one,
  exact pfiber_postnikov_map A n
end

definition pfiber_postnikov_map_pred' (A : spectrum) (n k l : ℤ) (p : n + k = l) :
  pfiber (postnikov_map_pred (A k) (maxm2 l)) ≃* EM_spectrum (πₛ[n] A) l :=
begin
  cases l with l l,
  { refine pfiber_postnikov_map_pred (A k) l ⬝e* _,
    exact EM_type_pequiv_EM A n k l p },
  { apply pequiv_of_is_contr, apply is_contr_pfiber_pid,
    apply is_contr_EM_spectrum_neg }
end

definition psquare_postnikov_map_ptrunc_elim (A : Type*) {n k l : ℕ₋₂} (H : is_trunc n (ptrunc k A))
  (p : n = l.+1) (q : k = l) :
  psquare (ptrunc.elim n (ptr k A)) (postnikov_map A l)
          (ptrunc_change_index p A) (ptrunc_change_index q A) :=
begin
  induction q, cases p,
  refine _ ⬝pv* pvrfl,
  apply ptrunc_elim_phomotopy2,
  reflexivity
end

definition postnikov_smap_postnikov_map (A : spectrum) (n k l : ℤ) (p : n + k = l) :
  psquare (postnikov_smap A n k) (postnikov_map_pred (A k) (maxm2 l))
    (ptrunc_maxm2_change_int p (A k)) (ptrunc_maxm2_pred (A k) (ap pred p⁻¹ ⬝ add.right_comm n k (- 1))) :=
begin
  cases l with l,
  { cases l with l, apply phomotopy_of_is_contr_cod, apply is_contr_ptrunc_minus_one,
    refine psquare_postnikov_map_ptrunc_elim (A k) _ _ _ ⬝hp* _,
    exact ap maxm2 (add.right_comm n (- 1) k ⬝ ap pred p ⬝ !pred_succ),
    apply ptrunc_maxm2_pred_nat },
  { apply phomotopy_of_is_contr_cod, apply is_trunc_trunc }
end

definition sfiber_postnikov_smap_pequiv (A : spectrum) (n : ℤ) (k : ℤ) :
  sfiber (postnikov_smap A n) k ≃* ssuspn n (EM_spectrum (πₛ[n] A)) k :=
proof
pfiber_pequiv_of_square _ _ (postnikov_smap_postnikov_map A n k (n + k) idp) ⬝e*
pfiber_postnikov_map_pred' A n k _ idp ⬝e*
pequiv_ap (EM_spectrum (πₛ[n] A)) (add.comm n k)
qed

section atiyah_hirzebruch
  parameters {X : Type*} (Y : X → spectrum) (s₀ : ℤ) (H : Πx, is_strunc s₀ (Y x))

  definition atiyah_hirzebruch_exact_couple : exact_couple rℤ Z2 :=
  @exact_couple_sequence (λs, spi X (λx, strunc s (Y x)))
                         (λs, spi_compose_left (λx, postnikov_smap (Y x) s))

  include H
  definition atiyah_hirzebruch_ub ⦃s n : ℤ⦄ (Hs : s ≤ n - 1) :
    is_contr (πₛ[n] (spi X (λx, strunc s (Y x)))) :=
  begin
    refine trivial_shomotopy_group_of_is_strunc _ _ (lt_of_le_sub_one Hs),
    apply is_strunc_spi, intro x, exact is_strunc_strunc _ _
  end

  definition atiyah_hirzebruch_lb ⦃s n : ℤ⦄ (Hs : s ≥ s₀ + 1) :
    is_equiv (spi_compose_left (λx, postnikov_smap (Y x) s) n) :=
  begin
    refine is_equiv_of_equiv_of_homotopy
      (ppi_pequiv_right (λx, ptrunc_pequiv_ptrunc_of_is_trunc _ _ (H x n))) _,
    { intro x, apply maxm2_monotone, apply add_le_add_right, exact le.trans !le_add_one Hs },
    { intro x, apply maxm2_monotone, apply add_le_add_right, exact le_sub_one_of_lt Hs },
    intro f, apply eq_of_ppi_homotopy,
    apply pmap_compose_ppi_phomotopy_left, intro x,
    fapply phomotopy.mk,
    { refine @trunc.rec _ _ _ _ _,
      { intro x, apply is_trunc_eq,
        assert H3 : maxm2 (s - 1 + n) ≤ (maxm2 (s + n)).+1,
        { refine trunc_index.le_succ (maxm2_monotone (le.trans (le_of_eq !add.right_comm)
                                                               !sub_one_le)) },
        exact @is_trunc_of_le _ _ _ H3 !is_trunc_trunc },
      intro a, reflexivity },
    reflexivity
  end

  definition is_bounded_atiyah_hirzebruch : is_bounded atiyah_hirzebruch_exact_couple :=
  is_bounded_sequence _ s₀ (λn, n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

  definition atiyah_hirzebruch_convergence' :
    (λn s, πₛ[n] (sfiber (spi_compose_left (λx, postnikov_smap (Y x) s)))) ⟹ᵍ
    (λn, πₛ[n] (spi X (λx, strunc s₀ (Y x)))) :=
  converges_to_sequence _ s₀ (λn, n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

  definition atiyah_hirzebruch_convergence :
    (λn s, opH^-(n-s)[(x : X), πₛ[s] (Y x)]) ⟹ᵍ (λn, pH^-n[(x : X), Y x]) :=
  converges_to_g_isomorphism atiyah_hirzebruch_convergence'
    begin
      intro n s,
      refine _ ⬝g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ idp)⁻¹ᵍ,
      refine _ ⬝g !shomotopy_group_ssuspn,
      apply shomotopy_group_isomorphism_of_pequiv n, intro k,
      refine !pfiber_ppi_compose_left ⬝e* _,
      exact ppi_pequiv_right (λx, sfiber_postnikov_smap_pequiv (Y x) s k)
    end
    begin
      intro n,
      refine _ ⬝g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ idp)⁻¹ᵍ,
      apply shomotopy_group_isomorphism_of_pequiv, intro k,
      exact ppi_pequiv_right (λx, ptrunc_pequiv (maxm2 (s₀ + k)) (Y x k)),
    end

end atiyah_hirzebruch

section unreduced_atiyah_hirzebruch

definition unreduced_atiyah_hirzebruch_convergence {X : Type} (Y : X → spectrum) (s₀ : ℤ)
  (H : Πx, is_strunc s₀ (Y x)) :
  (λn s, uopH^-(n-s)[(x : X), πₛ[s] (Y x)]) ⟹ᵍ (λn, upH^-n[(x : X), Y x]) :=
converges_to_g_isomorphism
  (@atiyah_hirzebruch_convergence X₊ (add_point_spectrum Y) s₀ (is_strunc_add_point_spectrum H))
  begin
    intro n s, refine _ ⬝g !uopH_isomorphism_opH⁻¹ᵍ,
    apply ordinary_parametrized_cohomology_isomorphism_right,
    intro x,
    apply shomotopy_group_add_point_spectrum
  end
  begin
    intro n, reflexivity
  end
end unreduced_atiyah_hirzebruch

section serre
  variables {X : Type} (F : X → Type) (Y : spectrum) (s₀ : ℤ) (H : is_strunc s₀ Y)

  include H
  definition serre_convergence :
    (λn s, uopH^-(n-s)[(x : X), uH^-s[F x, Y]]) ⟹ᵍ (λn, uH^-n[Σ(x : X), F x, Y]) :=
  proof
  converges_to_g_isomorphism
    (unreduced_atiyah_hirzebruch_convergence
      (λx, sp_ucotensor (F x) Y) s₀
      (λx, is_strunc_sp_ucotensor s₀ (F x) H))
    begin
      intro n s,
      refine unreduced_ordinary_parametrized_cohomology_isomorphism_right _ (-(n-s)),
      intro x,
      exact (unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor _ _ idp)⁻¹ᵍ
    end
    begin
     intro n,
     refine unreduced_parametrized_cohomology_isomorphism_shomotopy_group_supi _ idp ⬝g _,
     refine _ ⬝g (unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor _ _ idp)⁻¹ᵍ,
     apply shomotopy_group_isomorphism_of_pequiv, intro k,
     exact (sigma_pumap F (Y k))⁻¹ᵉ*
    end
 qed
end serre


end spectrum
