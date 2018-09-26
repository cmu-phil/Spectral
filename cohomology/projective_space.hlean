/- A computation of the cohomology groups of K(ℤ,2) using the Serre spectral sequence

Author: Floris van Doorn-/

import .serre

open eq spectrum EM EM.ops int pointed cohomology left_module algebra group fiber is_equiv equiv
     prod is_trunc function

namespace temp

  definition uH0_circle : uH^0[circle] ≃g gℤ :=
  sorry

  definition uH1_circle : uH^1[circle] ≃g gℤ :=
  sorry

  definition uH_circle_of_ge (n : ℤ) (h : n ≥ 2) : uH^n[circle] ≃g trivial_ab_group :=
  sorry

  definition f : unit → K agℤ 2 :=
  λx, pt

  definition fserre :
    (λp q, uoH^p[K agℤ 2, H^q[circle₊]]) ⟹ᵍ (λn, H^-n[unit₊]) :=
  proof
  converges_to_g_isomorphism
    (serre_convergence_map_of_is_conn pt f (EM_spectrum agℤ) 0
      (is_strunc_EM_spectrum agℤ) (is_conn_EM agℤ 2))
    begin
      intro n s, apply unreduced_ordinary_cohomology_isomorphism_right,
      apply unreduced_cohomology_isomorphism, symmetry,
      refine !fiber_const_equiv ⬝e _,
      refine loop_EM _ 1 ⬝e _,
      exact EM_pequiv_circle
    end
    begin intro n, reflexivity end
  qed
exit -- this file needs to be updated after reindexing of spectral sequences
  section
  local notation `X`   := converges_to.X fserre
  local notation `E∞`  := convergence_theorem.Einf (converges_to.HH fserre)
  local notation `E∞d` := convergence_theorem.Einfdiag (converges_to.HH fserre)
  local notation `E`   := exact_couple.E X

  definition fbuilt (n : ℤ) :
    is_built_from (LeftModule_int_of_AbGroup (H^-n[unit₊])) (E∞d (n, 0)) :=
  is_built_from_of_converges_to fserre n

  definition fEinf0 : E∞ (0, 0) ≃lm LeftModule_int_of_AbGroup agℤ :=
  isomorphism_zero_of_is_built_from (fbuilt 0) (by reflexivity) ⬝lm
  lm_iso_int.mk (cohomology_change_int _ _ neg_zero ⬝g
    cohomology_isomorphism pbool_pequiv_add_point_unit _ _ ⬝g ordinary_cohomology_pbool _)

  definition fEinfd (n : ℤ) (m : ℕ) (p : n ≠ 0) : is_contr (E∞d (n, 0) m) :=
  have p' : -n ≠ 0, from λH, p (eq_zero_of_neg_eq_zero H),
  is_contr_quotients (fbuilt n) (@(is_trunc_equiv_closed_rev -2
    (group.equiv_of_isomorphism (cohomology_isomorphism pbool_pequiv_add_point_unit _ _)))
    (EM_dimension' _ _ p')) _

  definition fEinf (n : ℤ) (m : ℕ) (p : n ≠ 0) : is_contr (E∞ (n, -m)) :=
  transport (is_contr ∘ E∞)
    begin
      induction m with m q, reflexivity, refine ap (deg (exact_couple.i X)) q ⬝ _,
      exact prod_eq idp (neg_add m (1 : ℤ))⁻¹ᵖ
    end
    (fEinfd n m p)

  definition is_contr_fD (n s : ℤ) (p : s > 0) : is_contr (E (n, s)) :=
  have is_contr H^-s[circle₊], from
  is_contr_ordinary_cohomology_of_neg _ _ (neg_neg_of_pos p),
  have is_contr (uoH^-(n-s)[K agℤ 2, H^-s[circle₊]]), from
  is_contr_unreduced_ordinary_cohomology _ _ _ _,
  @(is_contr_equiv_closed (left_module.equiv_of_isomorphism (converges_to.e fserre (n, s))⁻¹ˡᵐ))
    this

  definition is_contr_fD2 (n s : ℤ) (p : n > s) : is_contr (E (n, s)) :=
  have -(n-s) < 0, from neg_neg_of_pos (sub_pos_of_lt p),
  @(is_contr_equiv_closed (left_module.equiv_of_isomorphism (converges_to.e fserre (n, s))⁻¹ˡᵐ))
    (is_contr_ordinary_cohomology_of_neg _ _ this)

  definition is_contr_fD3 (n s : ℤ) (p : s ≤ - 2) : is_contr (E (n, s)) :=
  have -s ≥ 2, from sorry, --from neg_neg_of_pos (sub_pos_of_lt p),
  @(is_contr_equiv_closed (group.equiv_of_isomorphism (unreduced_ordinary_cohomology_isomorphism_right _ (uH_circle_of_ge _ this)⁻¹ᵍ _) ⬝e
    left_module.equiv_of_isomorphism (converges_to.e fserre (n, s))⁻¹ˡᵐ))
    (is_contr_ordinary_cohomology _ _ _ !is_contr_unit)
--(unreduced_ordinary_cohomology_isomorphism_right _ _ _)
--(is_contr_ordinary_cohomology_of_neg _ _ this)
--(is_contr_ordinary_cohomology_of_neg _ _ this)
  definition fE00 : E (0,0) ≃lm LeftModule_int_of_AbGroup agℤ :=
  begin
    refine (Einf_isomorphism fserre 0 _ _)⁻¹ˡᵐ ⬝lm fEinf0,
    intro r H, apply is_contr_fD2, exact sub_nat_lt 0 (r+1),
    intro r H, apply is_contr_fD, change 0 + (r + 1) >[ℤ] 0,
    apply of_nat_lt_of_nat_of_lt,
    apply nat.zero_lt_succ,
  end

  definition Ex0 (n : ℕ) : AddGroup_of_AddAbGroup (E (-n,0)) ≃g uH^n[K agℤ 2] :=
  begin
    refine group_isomorphism_of_lm_isomorphism_int (converges_to.e fserre (-n,0)) ⬝g _,
    refine cohomology_change_int _ _ (ap neg !sub_zero ⬝ !neg_neg) ⬝g
      unreduced_ordinary_cohomology_isomorphism_right _ uH0_circle _,
  end

  definition Ex1 (n : ℕ) : AddGroup_of_AddAbGroup (E (-(n+(1 : ℤ)),- (1 : ℤ))) ≃g uH^n[K agℤ 2] :=
  begin
    refine group_isomorphism_of_lm_isomorphism_int (converges_to.e fserre (-(n+(1 : ℤ)),- (1 : ℤ))) ⬝g _,
    refine cohomology_change_int _ _ (ap neg _ ⬝ !neg_neg) ⬝g
      unreduced_ordinary_cohomology_isomorphism_right _ !uH1_circle _,
    exact ap (λx, x - - (1 : ℤ)) !neg_add ⬝ !add_sub_cancel
  end

  definition uH0 : uH^0[K agℤ 2] ≃g gℤ :=
  (Ex0 0)⁻¹ᵍ ⬝g group_isomorphism_of_lm_isomorphism_int fE00

  definition fE10 : is_contr (E (- (1 : ℤ),0)) :=
  begin
    refine @(is_trunc_equiv_closed _ _) (fEinf (- (1 : ℤ)) 0 dec_star),
    apply equiv_of_isomorphism,
    refine Einf_isomorphism fserre 0 _ _,
    intro r H, exact sorry, exact sorry --apply is_contr_fD2, change (- 1) - (- 1) >[ℤ] (- 0) - (r + 1),
--    apply is_contr_fD, change (-0) - (r + 1) >[ℤ] 0,
--exact sub_nat_lt 0 r,
    -- intro r H, apply is_contr_fD, change 0 + (r + 1) >[ℤ] 0,
    -- apply of_nat_lt_of_nat_of_lt,
    -- apply nat.zero_lt_succ,
  end

  definition uH1 : is_contr (uH^1[K agℤ 2]) :=
  begin
    refine @(is_trunc_equiv_closed -2 (group.equiv_of_isomorphism !Ex0)) fE10,
  end

  end

end temp
