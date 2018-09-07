import homotopy.sphere2 ..move_to_lib

open fin eq equiv group algebra sphere.ops pointed nat int trunc is_equiv function circle

  protected definition nat.eq_one_of_mul_eq_one {n : ℕ} (m : ℕ) (q : n * m = 1) : n = 1 :=
  begin
    cases n with n,
    { exact empty.elim (succ_ne_zero 0 ((nat.zero_mul m)⁻¹ ⬝ q)⁻¹) },
    { cases n with n,
      { reflexivity },
      { apply empty.elim, cases m with m,
        { exact succ_ne_zero 0 q⁻¹ },
        { apply nat.lt_irrefl 1,
          exact (calc
            1 ≤ (m + 1)
              : succ_le_succ (nat.zero_le m)
          ... = 1 * (m + 1)
              : (nat.one_mul (m + 1))⁻¹
          ... < (n + 2) * (m + 1)
              : nat.mul_lt_mul_of_pos_right
                  (succ_le_succ (succ_le_succ (nat.zero_le n))) (zero_lt_succ m)
          ... = 1 : q) } } }
  end

  definition cases_of_nat_abs_eq {z : ℤ} (n : ℕ) (p : nat_abs z = n)
    : (z = of_nat n) ⊎ (z = - of_nat n) :=
  begin
    cases p, apply by_cases_of_nat z,
    { intro n, apply sum.inl, reflexivity },
    { intro n, apply sum.inr, exact ap int.neg (ap of_nat (nat_abs_neg n))⁻¹ }
  end

  definition eq_one_or_eq_neg_one_of_mul_eq_one {n : ℤ} (m : ℤ) (p : n * m = 1) : n = 1 ⊎ n = -1 :=
  cases_of_nat_abs_eq 1
    (nat.eq_one_of_mul_eq_one (nat_abs m)
      ((int.nat_abs_mul n m)⁻¹ ⬝ ap int.nat_abs p))

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

  /-
    TODO: define for unbased maps, define for S 0,
    clear sorry s
    prove stable under suspension
  -/

  attribute fundamental_group_of_circle fg_carrier_equiv_int [constructor]
  attribute untrunc_of_is_trunc [unfold 4]

  definition surf_eq_loop : @surf 1 = circle.loop := sorry
/-
  Favonia had a good idea, which he got from Ulrik: use the cogroup structure on the suspension to construct a group structure on ΣX →* Y, from which you can easily show that deg(id) = 1. See in the Agda library the files cogroup, cohspace and Group/LoopSuspAdjoint (or something)
-/


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

  definition πnSn_surf (n : ℕ) : πnSn (n+1) (tr surf) = 1 :> ℤ :=
  begin
    cases n with n IH,
    { refine ap (πnSn _ ∘ tr) surf_eq_loop ⬝ _, apply transport_code_loop },
    { unfold [πnSn], exact sorry}
  end

  definition deg {n : ℕ} [H : is_succ n] (f : S n →* S n) : ℤ :=
  by induction H with n; exact πnSn (n+1) (π→g[n+1] f (tr surf))

  definition deg_id (n : ℕ) [H : is_succ n] : deg (pid (S n)) = (1 : ℤ) :=
  by induction H with n;
     exact ap (πnSn (n+1)) (homotopy_group_functor_pid (succ n) (S (succ n)) (tr surf)) ⬝ πnSn_surf n

  definition deg_phomotopy {n : ℕ} [H : is_succ n] {f g : S n →* S n} (p : f ~* g) :
    deg f = deg g :=
  begin
    induction H with n,
    exact ap (πnSn (n+1)) (homotopy_group_functor_phomotopy (succ n) p (tr surf)),
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

  definition deg_compose {n : ℕ} [H : is_succ n] (f g : S n →* S n) :
    deg (g ∘* f) = deg g *[ℤ] deg f :=
  begin
    induction H with n,
    refine ap (πnSn (n+1)) (homotopy_group_functor_pcompose (succ n) g f (tr surf)) ⬝ _,
    apply endomorphism_equiv_Z !πnSn !πnSn_surf (π→g[n+1] g)
  end

  definition deg_equiv {n : ℕ} [H : is_succ n] (f : S n ≃* S n) :
    deg f = 1 ⊎ deg f = -1 :=
  begin
    induction H with n,
    apply eq_one_or_eq_neg_one_of_mul_eq_one (deg f⁻¹ᵉ*),
    refine !deg_compose⁻¹ ⬝ _,
    refine deg_phomotopy (pright_inv f) ⬝ _,
    apply deg_id
  end

end sphere
