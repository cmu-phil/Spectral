/- the construction of the Gysin sequence using the Serre spectral sequence -/
-- author: Floris van Doorn

import .serre

open eq pointed is_trunc is_conn is_equiv equiv sphere fiber chain_complex left_module spectrum nat
     prod nat int algebra function spectral_sequence

namespace cohomology
-- set_option pp.universes true
-- print unreduced_ordinary_cohomology_sphere_of_neq_nat
-- --set_option formatter.hide_full_terms false
-- exit
definition gysin_sequence' {E B : Type*} (n : ℕ) (HB : is_conn 1 B) (f : E →* B)
  (e : pfiber f ≃* sphere (n+1)) (A : AbGroup) : chain_complex +3ℤ :=
let c := serre_spectral_sequence_map_of_is_conn pt f (EM_spectrum A) 0 (is_strunc_EM_spectrum A) HB in
let cn : is_normal c := !is_normal_serre_spectral_sequence_map_of_is_conn in
let deg_d_x : Π(m : ℤ), deg (convergent_spectral_sequence.d c n) ((m+1) - 3, n + 1) = (n + m - 0, 0) :=
begin
  intro m, refine deg_d_normal_eq cn _ _ ⬝ _,
  refine prod_eq _ !add.right_inv,
  refine add.comm4 (m+1) (-3) n 2 ⬝ _,
  exact ap (λx, x - 1) (add.comm (m + 1) n ⬝ (add.assoc n m 1)⁻¹) ⬝ !add.assoc
end in
left_module.LES_of_SESs _ _ _ (λm, convergent_spectral_sequence.d c n (m - 3, n + 1))
  begin
    intro m,
    fapply short_exact_mod_isomorphism,
    rotate 3,
    { fapply short_exact_mod_of_is_contr_submodules
        (convergence_0 c (n + m) (λm, neg_zero)),
      { exact zero_lt_succ n },
      { intro k Hk0 Hkn, apply is_contr_E,
        apply is_contr_ordinary_cohomology,
        refine is_contr_equiv_closed_rev _
                (unreduced_ordinary_cohomology_sphere_of_neq_nat A Hkn Hk0),
        apply group.equiv_of_isomorphism, apply unreduced_ordinary_cohomology_isomorphism,
        exact e⁻¹ᵉ* }},
    { symmetry, refine Einf_isomorphism c (n+1) _ _ ⬝lm
            convergent_spectral_sequence.α c n (n + m - 0, 0) ⬝lm
            isomorphism_of_eq (ap (graded_homology _ _) _) ⬝lm
            !graded_homology_isomorphism ⬝lm
            cokernel_module_isomorphism_homology _ _ _,
      { exact sorry },
      { exact sorry },
      { exact (deg_d_x m)⁻¹ },
      { intro x, apply @eq_of_is_contr, apply is_contr_E,
        apply is_normal.normal2 cn,
        refine lt_of_le_of_lt (@le_of_eq ℤ _ _ _ (ap (pr2 ∘ deg (convergent_spectral_sequence.d c n))
          (deg_d_x m) ⬝ ap pr2 (deg_d_normal_eq cn _ _))) _,
        refine lt_of_le_of_lt (le_of_eq (zero_add (-(n+1)))) _,
        apply neg_neg_of_pos, apply of_nat_succ_pos }},
    { reflexivity },
    { exact sorry }
  end

--   (λm, short_exact_mod_isomorphism
--     _
--     isomorphism.rfl
--     _
--     (short_exact_mod_of_is_contr_submodules
--       (convergent_HDinf X _)
--       (zero_lt_succ n)
--       _))


end cohomology
