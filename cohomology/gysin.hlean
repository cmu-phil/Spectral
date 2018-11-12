/- the construction of the Gysin sequence using the Serre spectral sequence -/
-- author: Floris van Doorn

import .serre

open eq pointed is_trunc is_conn is_equiv equiv sphere fiber chain_complex left_module spectrum nat
     prod nat int algebra function spectral_sequence

namespace cohomology
/-
  We have maps:
  d_m = d_(m-1,n+1)^n : E_(m-1,n+1)^n → E_(m+n+1,0)^n
  Note that ker d_m = E_(m-1,n+1)^∞ and coker d_m = E_(m+n+1,0)^∞.
  We have short exact sequences
  coker d_{m-1} → D_{m+n}^∞  → ker d_m
  where D^∞ is the abutment of the spectral sequence.
  This comes from the spectral sequence, using the fact that coker d_{m-1} and ker d_m are the only
  two nontrivial groups building up D_{m+n}^∞ (in the filtration of D_{m+n}^∞).
  We can splice these SESs together to get a LES
  ... E_(m+n,0)^n → D_{m+n}^∞ → E_(m-1,n+1)^n → E_(m+n+1,0)^n → D_{m+n+1}^∞ ...
-/

definition gysin_sequence' {E B : Type*} {n : ℕ} (HB : is_conn 1 B) (f : E →* B)
  (e : pfiber f ≃* sphere (n+1)) (A : AbGroup) : chain_complex -3ℤ :=
let c := serre_spectral_sequence_map_of_is_conn pt f (EM_spectrum A) 0
  (is_strunc_EM_spectrum A) HB in
let cn : is_normal c := !is_normal_serre_spectral_sequence_map_of_is_conn in
have deg_d_x : Π(m : ℤ), deg (convergent_spectral_sequence.d c n) ((m - 1) - 1, n + 1) =
  (n + m - 0, 0),
begin
  intro m, refine deg_d_normal_eq cn _ _ ⬝ _,
  refine prod_eq _ !add.right_inv,
  refine ap (λx, x + (n+2)) !sub_sub ⬝ _,
  refine add.comm4 m (- 2) n 2 ⬝ _,
  refine ap (λx, x + 0) !add.comm
end,
have trivial_E : Π(r : ℕ) (p q : ℤ) (hq : q ≠ 0) (hq' : q ≠ of_nat (n+1)),
  is_contr (convergent_spectral_sequence.E c r (p, q)),
begin
  intros, apply is_contr_E, apply is_contr_ordinary_cohomology, esimp,
  refine is_contr_equiv_closed_rev _ (unreduced_ordinary_cohomology_sphere_of_neq A hq' hq),
  apply group.equiv_of_isomorphism, apply unreduced_ordinary_cohomology_isomorphism, exact e⁻¹ᵉ*
end,
have trivial_E' : Π(r : ℕ) (p q : ℤ) (hq : q > n+1),
  is_contr (convergent_spectral_sequence.E c r (p, q)),
begin
  intros, apply trivial_E r p q,
  { intro h, subst h, apply not_lt_zero (n+1), exact lt_of_of_nat_lt_of_nat hq },
  { intro h, subst h, exact lt.irrefl _ hq }
end,
left_module.LES_of_SESs _ _ _ (λm, convergent_spectral_sequence.d c n (m - 1, n + 1))
  begin
    intro m,
    fapply short_exact_mod_isomorphism,
    rotate 3,
    { fapply short_exact_mod_of_is_contr_submodules
        (convergence_0 c (n + m) (λm, neg_zero)),
      { exact zero_lt_succ n },
      { intro k Hk0 Hkn, apply trivial_E, exact λh, Hk0 (of_nat.inj h),
        exact λh, Hkn (of_nat.inj h), }},
    { symmetry, refine Einf_isomorphism c (n+1) _ _ ⬝lm
        convergent_spectral_sequence.α c n (n + m - 0, 0) ⬝lm
        isomorphism_of_eq (ap (graded_homology _ _) _) ⬝lm
        !graded_homology_isomorphism ⬝lm
        homology_isomorphism_cokernel_module _ _ _,
      { intros r Hr, apply trivial_E', apply of_nat_lt_of_nat_of_lt,
        rewrite [zero_add], exact lt_succ_of_le Hr },
      { intros r Hr, apply is_contr_E, apply is_normal.normal2 cn,
        refine lt_of_le_of_lt (le_of_eq (ap (λx : ℤ × ℤ, 0 + pr2 x) (is_normal.normal3 cn r))) _,
        esimp, rewrite [-sub_eq_add_neg], apply sub_lt_of_pos, apply of_nat_lt_of_nat_of_lt,
        apply succ_pos },
      { exact (deg_d_x m)⁻¹ },
      { intro x, apply @eq_of_is_contr, apply is_contr_E,
        apply is_normal.normal2 cn,
        refine lt_of_le_of_lt (@le_of_eq ℤ _ _ _ (ap (pr2 ∘ deg (convergent_spectral_sequence.d c n))
          (deg_d_x m) ⬝ ap pr2 (deg_d_normal_eq cn _ _))) _,
        refine lt_of_le_of_lt (le_of_eq (zero_add (-(n+1)))) _,
        apply neg_neg_of_pos, apply of_nat_succ_pos }},
    { reflexivity },
    { symmetry,
      refine Einf_isomorphism c (n+1) _ _ ⬝lm
        convergent_spectral_sequence.α c n (n + m - (n+1), n+1) ⬝lm
        graded_homology_isomorphism_kernel_module _ _ _ _ ⬝lm
        isomorphism_of_eq (ap (graded_kernel _) _),
      { intros r Hr, apply trivial_E', apply of_nat_lt_of_nat_of_lt,
        apply lt_add_of_pos_right, apply zero_lt_succ },
      { intros r Hr, apply is_contr_E, apply is_normal.normal2 cn,
        refine lt_of_le_of_lt (le_of_eq (ap (λx : ℤ × ℤ, (n+1)+pr2 x) (is_normal.normal3 cn r))) _,
        esimp, rewrite [-sub_eq_add_neg], apply sub_lt_right_of_lt_add,
        apply of_nat_lt_of_nat_of_lt, rewrite [zero_add], exact lt_succ_of_le Hr },
      { apply trivial_image_of_is_contr, rewrite [deg_d_inv_eq],
        apply trivial_E', apply of_nat_lt_of_nat_of_lt,
        apply lt_add_of_pos_right, apply zero_lt_succ },
      { refine prod_eq _ rfl, refine ap (add _) !neg_add ⬝ _,
        refine add.comm4 n m (-n) (- 1) ⬝ _,
        refine ap (λx, x + _) !add.right_inv ⬝ !zero_add }}
  end

-- open fin
-- definition gysin_sequence'_zero_equiv {E B : Type*} {n : ℕ} (HB : is_conn 1 B) (f : E →* B)
--   (e : pfiber f ≃* sphere (n+1)) (A : AbGroup) (m : ℤ) :
--   gysin_sequence' HB f e A (m, 0) ≃ _ :=
-- _




end cohomology
