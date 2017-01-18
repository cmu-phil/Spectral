import homotopy.sphere2 ..move_to_lib

open fin eq equiv group algebra sphere.ops pointed nat int trunc is_equiv function circle

  definition eq_one_or_eq_neg_one_of_mul_eq_one {n : ℤ} (m : ℤ) (p : n * m = 1) : n = 1 ⊎ n = -1 :=
  sorry

  definition endomorphism_int_unbundled (f : ℤ → ℤ) [is_add_hom f] (n : ℤ) :
    f n = f 1 * n :=
  begin
    induction n using rec_nat_on with n IH n IH,
    { refine respect_zero f ⬝ _, exact !mul_zero⁻¹ },
    { refine respect_add f n 1 ⬝ _, rewrite IH,
      rewrite [↑int.succ, left_distrib], apply ap (λx, _ + x), exact !mul_one⁻¹},
    { rewrite [neg_nat_succ], refine respect_add f (-n) (- 1) ⬝ _,
      rewrite [IH, ↑int.pred, mul_sub_left_distrib], apply ap (λx, _ + x),
      refine _ ⬝ ap neg !mul_one⁻¹, exact respect_neg f 1 }
  end

namespace sphere

  attribute fundamental_group_of_circle fg_carrier_equiv_int [constructor]
  attribute untrunc_of_is_trunc [unfold 4]

  definition surf_eq_loop : @surf 1 = circle.loop := sorry

  -- definition π2S2_surf : π2S2 (tr surf) = 1 :> ℤ :=
  -- begin
  --   unfold [π2S2, chain_complex.LES_of_homotopy_groups],
  -- end

-- check (pmap.to_fun
--              (chain_complex.cc_to_fn
--                 (chain_complex.LES_of_homotopy_groups
--                    hopf.complex_phopf)
--                 (pair 1 2))
--              (tr surf))

-- eval (pmap.to_fun
--              (chain_complex.cc_to_fn
--                 (chain_complex.LES_of_homotopy_groups
--                    hopf.complex_phopf)
--                 (pair 1 2))
--              (tr surf))

  definition πnSn_surf (n : ℕ) : πnSn n (tr surf) = 1 :> ℤ :=
  begin
    cases n with n IH,
    { refine ap (πnSn _ ∘ tr) surf_eq_loop ⬝ _, apply transport_code_loop },
    { unfold [πnSn], exact sorry}
  end

  definition deg {n : ℕ} [H : is_succ n] (f : S* n →* S* n) : ℤ :=
  by induction H with n; exact πnSn n (π→g[n+1] f (tr surf))

  definition deg_id (n : ℕ) [H : is_succ n] : deg (pid (S* n)) = (1 : ℤ) :=
  by induction H with n;
     exact ap (πnSn n) (homotopy_group_functor_pid (succ n) (S* (succ n)) (tr surf)) ⬝ πnSn_surf n

  definition deg_phomotopy {n : ℕ} [H : is_succ n] {f g : S* n →* S* n} (p : f ~* g) :
    deg f = deg g :=
  begin
    induction H with n,
    exact ap (πnSn n) (homotopy_group_functor_phomotopy (succ n) p (tr surf)),
  end

  definition endomorphism_int (f : gℤ →g gℤ) (n : ℤ) : f n = f (1 : ℤ) *[ℤ] n :=
  @endomorphism_int_unbundled f (homomorphism.addstruct f) n

  definition endomorphism_equiv_Z {X : Group} (e : X ≃g gℤ) {one : X}
    (p : e one = 1 :> ℤ) (φ : X →g X) (x : X) : e (φ x) = e (φ one) *[ℤ] e x :=
  begin
    revert x, refine equiv_rect' (equiv_of_isomorphism e) _ _,
    intro n,
    refine endomorphism_int (e ∘g φ ∘g e⁻¹ᵍ) n ⬝ _,
    refine ap011 (@mul ℤ _) _ _,
    { esimp, apply ap (e ∘ φ), refine ap e⁻¹ᵍ p⁻¹ ⬝ _,
      exact to_left_inv (equiv_of_isomorphism e) one },
    { symmetry, exact to_right_inv (equiv_of_isomorphism e) n}
  end

  definition deg_compose {n : ℕ} [H : is_succ n] (f g : S* n →* S* n) :
    deg (g ∘* f) = deg g *[ℤ] deg f :=
  begin
    induction H with n,
    refine ap (πnSn n) (homotopy_group_functor_compose (succ n) g f (tr surf)) ⬝ _,
    apply endomorphism_equiv_Z !πnSn !πnSn_surf (π→g[n+1] g)
  end

  definition deg_equiv {n : ℕ} [H : is_succ n] (f : S* n ≃* S* n) :
    deg f = 1 ⊎ deg f = -1 :=
  begin
    induction H with n,
    apply eq_one_or_eq_neg_one_of_mul_eq_one (deg f⁻¹ᵉ*),
    refine !deg_compose⁻¹ ⬝ _,
    refine deg_phomotopy (pright_inv f) ⬝ _,
    apply deg_id
  end

end sphere
