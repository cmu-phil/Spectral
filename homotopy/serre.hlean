import ..algebra.spectral_sequence .strunc .cohomology

open eq spectrum trunc is_trunc pointed int EM algebra left_module fiber lift equiv is_equiv
     cohomology group sigma unit is_conn
set_option pp.binder_types true

/- Eilenberg MacLane spaces are the fibers of the Postnikov system of a type -/

namespace pointed
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

definition is_strunc_strunc_pred (X : spectrum) (k : ℤ) : is_strunc k (strunc (k - 1) X) :=
λn, @(is_trunc_of_le _ (maxm2_monotone (add_le_add_right (sub_one_le k) n))) !is_strunc_strunc

definition postnikov_smap [constructor] (X : spectrum) (k : ℤ) :
  strunc k X →ₛ strunc (k - 1) X :=
strunc_elim (str (k - 1) X) (is_strunc_strunc_pred X k)

/-
  we could try to prove that postnikov_smap is homotopic to postnikov_map, although the types
  are different enough, that even stating it will be quite annoying
-/

definition pfiber_postnikov_smap (A : spectrum) (n : ℤ) (k : ℤ) :
  sfiber (postnikov_smap A n) k ≃* EM_spectrum (πₛ[n] A) k :=
begin
  exact sorry
/-  symmetry, apply spectrum_pequiv_of_nat_succ_succ, clear k, intro k,
  apply EMadd1_pequiv k,
  { exact sorry
    -- refine _ ⬝g shomotopy_group_strunc n A,
    -- exact chain_complex.LES_isomorphism_of_trivial_cod _ _
    --   (trivial_homotopy_group_of_is_trunc _ (self_lt_succ n))
    --   (trivial_homotopy_group_of_is_trunc _ (le_succ _))
},
  { exact sorry --apply is_conn_fun_trunc_elim,  apply is_conn_fun_tr
    },
  { -- have is_trunc (n+1) (ptrunc n.+1 A), from !is_trunc_trunc,
    -- have is_trunc ((n+1).+1) (ptrunc n A), by do 2 apply is_trunc_succ, apply is_trunc_trunc,
    -- apply is_trunc_pfiber
    exact sorry
    }-/
end

section atiyah_hirzebruch
  parameters {X : Type*} (Y : X → spectrum) (s₀ : ℤ) (H : Πx, is_strunc s₀ (Y x))

  definition atiyah_hirzebruch_exact_couple : exact_couple rℤ Z2 :=
  @exact_couple_sequence (λs, strunc s (spi X Y)) (postnikov_smap (spi X Y))

  definition atiyah_hirzebruch_ub ⦃s n : ℤ⦄ (Hs : s ≤ n - 1) :
    is_contr (πₛ[n] (strunc s (spi X Y))) :=
  begin
    apply trivial_shomotopy_group_of_is_strunc,
      apply is_strunc_strunc,
    exact lt_of_le_sub_one Hs
  end

  include H
  definition atiyah_hirzebruch_lb ⦃s n : ℤ⦄ (Hs : s ≥ s₀ + 1) :
    is_equiv (postnikov_smap (spi X Y) s n) :=
  begin
    have H2 : is_strunc s₀ (spi X Y), from is_strunc_spi _ _ H,
    refine is_equiv_of_equiv_of_homotopy
      (ptrunc_pequiv_ptrunc_of_is_trunc _ _ (H2 n)) _,
    { apply maxm2_monotone, apply add_le_add_right, exact le.trans !le_add_one Hs },
    { apply maxm2_monotone, apply add_le_add_right, exact le_sub_one_of_lt Hs },
    refine @trunc.rec _ _ _ _ _,
    { intro x, apply is_trunc_eq,
      assert H3 : maxm2 (s - 1 + n) ≤ (maxm2 (s + n)).+1,
      { refine trunc_index.le_succ (maxm2_monotone (le.trans (le_of_eq !add.right_comm)
                                                             !sub_one_le)) },
      exact @is_trunc_of_le _ _ _ H3 !is_trunc_trunc },
    intro a, reflexivity
  end

  definition is_bounded_atiyah_hirzebruch : is_bounded atiyah_hirzebruch_exact_couple :=
  is_bounded_sequence _ s₀ (λn, n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

  definition atiyah_hirzebruch_convergence' :
    (λn s, πₛ[n] (sfiber (postnikov_smap (spi X Y) s))) ⟹ᵍ (λn, πₛ[n] (strunc s₀ (spi X Y))) :=
  converges_to_sequence _ s₀ (λn, n - 1) atiyah_hirzebruch_lb atiyah_hirzebruch_ub

  lemma spi_EM_spectrum (k n : ℤ) :
    EM_spectrum (πₛ[n] (spi X Y)) k ≃* spi X (λx, EM_spectrum (πₛ[n] (Y x))) k :=
  sorry

  definition atiyah_hirzebruch_convergence :
    (λn s, opH^-n[(x : X), πₛ[s] (Y x)]) ⟹ᵍ (λn, pH^-n[(x : X), Y x]) :=
  converges_to_g_isomorphism atiyah_hirzebruch_convergence'
    begin
      intro n s,
      refine _ ⬝g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ idp)⁻¹ᵍ,
      apply shomotopy_group_isomorphism_of_pequiv, intro k,
      refine pfiber_postnikov_smap (spi X Y) s k ⬝e* _,
      apply spi_EM_spectrum
    end
    begin
      intro n,
      refine _ ⬝g (parametrized_cohomology_isomorphism_shomotopy_group_spi _ idp)⁻¹ᵍ,
      apply shomotopy_group_isomorphism_of_pequiv, intro k,
      apply ptrunc_pequiv, exact is_strunc_spi s₀ Y H k,
    end

end atiyah_hirzebruch

section unreduced_atiyah_hirzebruch

definition unreduced_atiyah_hirzebruch_convergence {X : Type} (Y : X → spectrum) (s₀ : ℤ)
  (H : Πx, is_strunc s₀ (Y x)) :
  (λn s, uopH^-n[(x : X), πₛ[s] (Y x)]) ⟹ᵍ (λn, upH^-n[(x : X), Y x]) :=
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

  open option
  definition add_point_over {X : Type} (F : X → Type) (x : option X) : Type* :=
  (option.cases_on x (lift empty) F)₊

  postfix `₊ₒ`:(max+1) := add_point_over

  include H
 --  definition serre_convergence :
 --    (λn s, uopH^-n[(x : X), uH^-s[F x, Y]]) ⟹ᵍ (λn, uH^-n[Σ(x : X), F x, Y]) :=
 --  proof
 --  converges_to_g_isomorphism
 --    (unreduced_atiyah_hirzebruch_convergence
 --      (λx, sp_cotensor (F x) Y) s₀
 --      (λx, is_strunc_sp_cotensor s₀ (F x) H))
 --      begin
 --        exact sorry
 --        -- intro n s,
 --        -- apply ordinary_parametrized_cohomology_isomorphism_right,
 --        -- intro x,
 --        -- exact (cohomology_isomorphism_shomotopy_group_sp_cotensor _ _ idp)⁻¹ᵍ,
 --      end
 --      begin
 --        intro n, exact sorry
 --  --      refine parametrized_cohomology_isomorphism_shomotopy_group_spi _ idp ⬝g _,
 --  --      refine _ ⬝g (cohomology_isomorphism_shomotopy_group_sp_cotensor _ _ idp)⁻¹ᵍ,
 --  --      apply shomotopy_group_isomorphism_of_pequiv, intro k,
 --      end
 -- qed
end serre

/- TODO: πₛ[n] (strunc 0 (spi X Y)) ≃g H^n[X, λx, Y x] -/

end spectrum
