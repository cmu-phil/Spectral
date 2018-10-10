/- the construction of the Gysin sequence using the Serre spectral sequence -/
-- author: Floris van Doorn

import .serre

open eq pointed is_trunc is_conn is_equiv equiv sphere fiber chain_complex left_module spectrum nat
     prod nat int algebra

namespace cohomology

definition gysin_sequence' {E B : Type*} (n : ℕ) (HB : is_conn 1 B) (f : E →* B)
  (e : pfiber f ≃* sphere (n+1)) (A : AbGroup) : chain_complex +3ℤ :=
let c := serre_spectral_sequence_map_of_is_conn pt f (EM_spectrum A) 0 (is_strunc_EM_spectrum A) HB
in
left_module.LES_of_SESs _ _ _ (λm, convergent_spectral_sequence.d c n (m, n))
  begin
    intro m,
    fapply short_exact_mod_isomorphism,
    rotate 3,
    { fapply short_exact_mod_of_is_contr_submodules
        (spectral_sequence.convergence_0 c (n + m) (λm, neg_zero)),
      { exact zero_lt_succ n },
      { intro k Hk0 Hkn, apply spectral_sequence.is_contr_E,
        apply is_contr_ordinary_cohomology,
        refine is_contr_equiv_closed_rev _
                (unreduced_ordinary_cohomology_sphere_of_neq_nat A Hkn Hk0),
        apply group.equiv_of_isomorphism, apply unreduced_ordinary_cohomology_isomorphism,
        exact e⁻¹ᵉ* }},
  end
--   (λm, short_exact_mod_isomorphism
--     _
--     isomorphism.rfl
--     _
--     (short_exact_mod_of_is_contr_submodules
--       (convergent_spectral_sequence.HDinf X _)
--       (zero_lt_succ n)
--       _))

end cohomology
