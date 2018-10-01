import ..algebra.spectral_sequence ..spectrum.trunc .basic

open eq spectrum trunc is_trunc pointed int EM algebra left_module fiber lift equiv is_equiv
     cohomology group sigma unit is_conn prod
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
    exact is_trunc_pfiber _ _ _ _ }
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
    exact EM_type_pequiv_EM A p },
  { refine pequiv_of_is_contr _ _ _ _, apply is_contr_pfiber_pid,
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
  { cases l with l, apply phomotopy_of_is_contr_cod_pmap, apply is_contr_ptrunc_minus_one,
    refine psquare_postnikov_map_ptrunc_elim (A k) _ _ _ ⬝hp* _,
    exact ap maxm2 (add.right_comm n (- 1) k ⬝ ap pred p ⬝ !pred_succ),
    apply ptrunc_maxm2_pred_nat },
  { apply phomotopy_of_is_contr_cod_pmap, apply is_trunc_trunc }
end

definition sfiber_postnikov_smap_pequiv (A : spectrum) (n : ℤ) (k : ℤ) :
  sfiber (postnikov_smap A n) k ≃* ssuspn n (EM_spectrum (πₛ[n] A)) k :=
proof
pfiber_pequiv_of_square _ _ (postnikov_smap_postnikov_map A n k (n + k) idp) ⬝e*
pfiber_postnikov_map_pred' A n k _ idp ⬝e*
pequiv_ap (EM_spectrum (πₛ[n] A)) (add.comm n k)
qed

open exact_couple

section atiyah_hirzebruch
  parameters {X : Type*} (Y : X → spectrum) (s₀ : ℤ) (H : Πx, is_strunc s₀ (Y x))
  include H

  definition atiyah_hirzebruch_exact_couple : exact_couple rℤ Z2 :=
  @exact_couple_sequence (λs, spi X (λx, strunc s (Y x)))
                         (λs, spi_compose_left (λx, postnikov_smap (Y x) s))

--  include H
  definition atiyah_hirzebruch_ub ⦃s n : ℤ⦄ (Hs : s ≤ n - 1) :
    is_contr (πₛ[n] (spi X (λx, strunc s (Y x)))) :=
  begin
    refine trivial_shomotopy_group_of_is_strunc _ _ (lt_of_le_sub_one Hs),
    apply is_strunc_spi, intro x, exact is_strunc_strunc _ _
  end

  definition atiyah_hirzebruch_lb' ⦃s n : ℤ⦄ (Hs : s ≥ s₀ + 1) :
    is_equiv (spi_compose_left (λx, postnikov_smap (Y x) s) n) :=
  begin
    refine is_equiv_of_equiv_of_homotopy
      (ppi_pequiv_right (λx, ptrunc_pequiv_ptrunc_of_is_trunc _ _ (H x n))) _,
    { intro x, apply maxm2_monotone, apply add_le_add_right, exact le.trans !le_add_one Hs },
    { intro x, apply maxm2_monotone, apply add_le_add_right, exact le_sub_one_of_lt Hs },
    intro f, apply eq_of_phomotopy,
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

  definition atiyah_hirzebruch_lb ⦃s n : ℤ⦄ (Hs : s ≥ s₀ + 1) :
    is_equiv (πₛ→[n] (spi_compose_left (λx, postnikov_smap (Y x) s))) :=
  begin
    apply is_equiv_homotopy_group_functor, apply atiyah_hirzebruch_lb', exact Hs
  end

  definition is_bounded_atiyah_hirzebruch : is_bounded atiyah_hirzebruch_exact_couple :=
  is_bounded_sequence _ (λn, s₀) (λn, n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

  definition atiyah_hirzebruch_convergence1 :
    (λn s, πₛ[n] (sfiber (spi_compose_left (λx, postnikov_smap (Y x) s)))) ⟹ᵍ
    (λn, πₛ[n] (spi X (λx, strunc s₀ (Y x)))) :=
  convergent_exact_couple_sequence _ (λn, s₀) (λn, n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

  definition atiyah_hirzebruch_convergence2 :
    (λn s, opH^-(n-s)[(x : X), πₛ[s] (Y x)]) ⟹ᵍ (λn, pH^n[(x : X), Y x]) :=
  convergent_exact_couple_g_isomorphism
    (convergent_exact_couple_negate_abutment atiyah_hirzebruch_convergence1)
    begin
      intro n s,
      refine _ ⬝g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ idp)⁻¹ᵍ,
      refine _ ⬝g !shomotopy_group_ssuspn,
      apply shomotopy_group_isomorphism_of_pequiv n, intro k,
      refine !pfiber_pppi_compose_left ⬝e* _,
      exact ppi_pequiv_right (λx, sfiber_postnikov_smap_pequiv (Y x) s k)
    end
    begin
      intro n,
      refine _ ⬝g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ !neg_neg)⁻¹ᵍ,
      apply shomotopy_group_isomorphism_of_pequiv, intro k,
      exact ppi_pequiv_right (λx, ptrunc_pequiv (maxm2 (s₀ + k)) (Y x k)),
    end

  open prod.ops
  definition atiyah_hirzebruch_base_change [constructor] : agℤ ×ag agℤ ≃g agℤ ×ag agℤ :=
  begin
    fapply group.isomorphism.mk,
    { fapply group.homomorphism.mk, exact (λpq, (-(pq.1 + pq.2), -pq.2)),
      intro pq pq',
      induction pq with p q, induction pq' with p' q', esimp,
      exact prod_eq (ap neg !add.comm4 ⬝ !neg_add) !neg_add },
    { fapply adjointify,
      { exact (λns, (ns.2 - ns.1, -ns.2)) },
      { intro ns, esimp,
        exact prod_eq (ap neg (!add.comm ⬝ !neg_add_cancel_left) ⬝ !neg_neg) !neg_neg },
      { intro pq, esimp,
        exact prod_eq (ap (λx, _ + x) !neg_neg ⬝ !add.comm ⬝ !add_neg_cancel_right) !neg_neg }}
  end

  definition atiyah_hirzebruch_convergence :
    (λp q, opH^p[(x : X), πₛ[-q] (Y x)]) ⟹ᵍ (λn, pH^n[(x : X), Y x]) :=
  begin
    note z := convergent_exact_couple_reindex atiyah_hirzebruch_convergence2 atiyah_hirzebruch_base_change,
    refine convergent_exact_couple_g_isomorphism z _ (by intro n; reflexivity),
    intro p q,
    apply parametrized_cohomology_change_int,
    esimp,
    refine !neg_neg_sub_neg ⬝ !add_neg_cancel_right
  end

  definition atiyah_hirzebruch_spectral_sequence :
    convergent_spectral_sequence_g (λp q, opH^p[(x : X), πₛ[-q] (Y x)]) (λn, pH^n[(x : X), Y x]) :=
  begin
    apply convergent_spectral_sequence_of_exact_couple atiyah_hirzebruch_convergence,
    { intro n, exact add.comm (s₀ - -n) (-s₀) ⬝ !neg_add_cancel_left ⬝ !neg_neg },
    { reflexivity }
  end

end atiyah_hirzebruch

section unreduced_atiyah_hirzebruch

definition unreduced_atiyah_hirzebruch_convergence {X : Type} (Y : X → spectrum) (s₀ : ℤ)
  (H : Πx, is_strunc s₀ (Y x)) :
  (λp q, uopH^p[(x : X), πₛ[-q] (Y x)]) ⟹ᵍ (λn, upH^n[(x : X), Y x]) :=
convergent_exact_couple_g_isomorphism
  (@atiyah_hirzebruch_convergence X₊ (add_point_spectrum Y) s₀ (is_strunc_add_point_spectrum H))
  begin
    intro p q, refine _ ⬝g !uopH_isomorphism_opH⁻¹ᵍ,
    apply ordinary_parametrized_cohomology_isomorphism_right,
    intro x,
    apply shomotopy_group_add_point_spectrum
  end
  begin
    intro n, reflexivity
  end

definition unreduced_atiyah_hirzebruch_spectral_sequence {X : Type} (Y : X → spectrum) (s₀ : ℤ)
  (H : Πx, is_strunc s₀ (Y x)) :
  convergent_spectral_sequence_g (λp q, uopH^p[(x : X), πₛ[-q] (Y x)]) (λn, upH^n[(x : X), Y x]) :=
begin
  apply convergent_spectral_sequence_of_exact_couple (unreduced_atiyah_hirzebruch_convergence Y s₀ H),
  { intro n, exact add.comm (s₀ - -n) (-s₀) ⬝ !neg_add_cancel_left ⬝ !neg_neg },
  { reflexivity }
end

end unreduced_atiyah_hirzebruch

section serre
  universe variable u
  variables {X B : Type.{u}} (b₀ : B) (F : B → Type) (f : X → B)
            (Y : spectrum) (s₀ : ℤ) (H : is_strunc s₀ Y)

  include H
  definition serre_convergence :
    (λp q, uopH^p[(b : B), uH^q[F b, Y]]) ⟹ᵍ (λn, uH^n[Σ(b : B), F b, Y]) :=
  proof
  convergent_exact_couple_g_isomorphism
    (unreduced_atiyah_hirzebruch_convergence
      (λx, sp_ucotensor (F x) Y) s₀
      (λx, is_strunc_sp_ucotensor s₀ (F x) H))
    begin
      intro p q,
      refine unreduced_ordinary_parametrized_cohomology_isomorphism_right _ p,
      intro x,
      exact (unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor _ _ !neg_neg)⁻¹ᵍ
    end
    begin
     intro n,
     refine unreduced_parametrized_cohomology_isomorphism_shomotopy_group_supi _ !neg_neg ⬝g _,
     refine _ ⬝g (unreduced_cohomology_isomorphism_shomotopy_group_sp_ucotensor _ _ !neg_neg)⁻¹ᵍ,
     apply shomotopy_group_isomorphism_of_pequiv, intro k,
     exact (sigma_pumap F (Y k))⁻¹ᵉ*
    end
  qed

  definition serre_spectral_sequence :
    convergent_spectral_sequence_g (λp q, uopH^p[(b : B), uH^q[F b, Y]]) (λn, uH^n[Σ(b : B), F b, Y]) :=
  begin
    apply convergent_spectral_sequence_of_exact_couple (serre_convergence F Y s₀ H),
    { intro n, exact add.comm (s₀ - -n) (-s₀) ⬝ !neg_add_cancel_left ⬝ !neg_neg },
    { reflexivity }
  end

  definition serre_convergence_map :
    (λp q, uopH^p[(b : B), uH^q[fiber f b, Y]]) ⟹ᵍ (λn, uH^n[X, Y]) :=
  proof
  convergent_exact_couple_g_isomorphism
    (serre_convergence (fiber f) Y s₀ H)
    begin intro p q, reflexivity end
    begin intro n, apply unreduced_cohomology_isomorphism, exact !sigma_fiber_equiv⁻¹ᵉ end
  qed

  definition serre_spectral_sequence_map :
    convergent_spectral_sequence_g (λp q, uopH^p[(b : B), uH^q[fiber f b, Y]]) (λn, uH^n[X, Y]) :=
  begin
    apply convergent_spectral_sequence_of_exact_couple (serre_convergence_map f Y s₀ H),
    { intro n, exact add.comm (s₀ - -n) (-s₀) ⬝ !neg_add_cancel_left ⬝ !neg_neg },
    { reflexivity }
  end

  definition serre_convergence_of_is_conn (H2 : is_conn 1 B) :
    (λp q, uoH^p[B, uH^q[F b₀, Y]]) ⟹ᵍ (λn, uH^n[Σ(b : B), F b, Y]) :=
  proof
  convergent_exact_couple_g_isomorphism
    (serre_convergence F Y s₀ H)
    begin intro p q, exact @uopH_isomorphism_uoH_of_is_conn (pointed.MK B b₀) _ _ H2  end
    begin intro n, reflexivity end
  qed

  definition serre_spectral_sequence_of_is_conn (H2 : is_conn 1 B) :
    convergent_spectral_sequence_g (λp q, uoH^p[B, uH^q[F b₀, Y]]) (λn, uH^n[Σ(b : B), F b, Y]) :=
  begin
    apply convergent_spectral_sequence_of_exact_couple (serre_convergence_of_is_conn b₀ F Y s₀ H H2),
    { intro n, exact add.comm (s₀ - -n) (-s₀) ⬝ !neg_add_cancel_left ⬝ !neg_neg },
    { reflexivity }
  end

  definition serre_convergence_map_of_is_conn (H2 : is_conn 1 B) :
    (λp q, uoH^p[B, uH^q[fiber f b₀, Y]]) ⟹ᵍ (λn, uH^n[X, Y]) :=
  proof
  convergent_exact_couple_g_isomorphism
    (serre_convergence_of_is_conn b₀ (fiber f) Y s₀ H H2)
    begin intro p q, reflexivity end
    begin intro n, apply unreduced_cohomology_isomorphism, exact !sigma_fiber_equiv⁻¹ᵉ end
  qed

  definition serre_spectral_sequence_map_of_is_conn (H2 : is_conn 1 B) :
    convergent_spectral_sequence_g (λp q, uoH^p[B, uH^q[fiber f b₀, Y]]) (λn, uH^n[X, Y]) :=
  begin
    apply convergent_spectral_sequence_of_exact_couple (serre_convergence_map_of_is_conn b₀ f Y s₀ H H2),
    { intro n, exact add.comm (s₀ - -n) (-s₀) ⬝ !neg_add_cancel_left ⬝ !neg_neg },
    { reflexivity }
  end

end serre

end spectrum
