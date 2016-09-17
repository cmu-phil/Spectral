import homotopy.sphere2 ..move_to_lib

open fin eq equiv group algebra sphere.ops pointed nat int trunc is_equiv function

definition eq_one_or_eq_neg_one_of_mul_eq_one {n : ℤ} (m : ℤ) (p : n * m = 1) : n = 1 ⊎ n = -1 :=
sorry

namespace sphere

  definition πnSn_surf (n : ℕ) : πnSn n (tr surf) = 1 :> ℤ :=
  sorry

  definition deg {n : ℕ} [H : is_succ n] (f : S. n →* S. n) : ℤ :=
  by induction H with n; exact πnSn n ((π→g[n+1] f) (tr surf))

  definition deg_id (n : ℕ) [H : is_succ n] : deg (pid (S. n)) = (1 : ℤ) :=
  by induction H with n;
     exact ap (πnSn n) (phomotopy_group_functor_pid (succ n) (S. (succ n)) (tr surf)) ⬝ πnSn_surf n

  definition deg_phomotopy {n : ℕ} [H : is_succ n] {f g : S. n →* S. n} (p : f ~* g) :
    deg f = deg g :=
  begin
    induction H with n,
    exact ap (πnSn n) (phomotopy_group_functor_phomotopy (succ n) p (tr surf)),
  end

  -- this is super ugly and should be changed
  definition endomorphism_int (f : gℤ →g gℤ) (n : ℤ) : f n = f (1 : ℤ) *[ℤ] n :=
  begin
    induction n using rec_nat_on with n IH n IH,
    { refine respect_one f ⬝ _, esimp, exact !mul_zero⁻¹ },
    { refine respect_mul f n (1 : ℤ) ⬝ _, rewrite IH,
      rewrite [↑int.succ, left_distrib], apply ap (λx, _ + x), exact !mul_one⁻¹},
    { rewrite [neg_nat_succ], refine respect_mul f (-n : ℤ) (- 1 : ℤ) ⬝ _,
      rewrite [IH, ↑int.pred, mul_sub_left_distrib], apply ap (λx, _ + x),
      refine _ ⬝ ap neg !mul_one⁻¹, exact to_respect_inv f (1 : ℤ) }
  end

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

  definition deg_compose {n : ℕ} [H : is_succ n] (f g : S. n →* S. n) :
    deg (g ∘* f) = deg g *[ℤ] deg f :=
  begin
    induction H with n,
    refine ap (πnSn n) (phomotopy_group_functor_compose (succ n) g f (tr surf)) ⬝ _,
    apply endomorphism_equiv_Z !πnSn !πnSn_surf (π→g[n+1] g)
  end

  definition deg_equiv {n : ℕ} [H : is_succ n] (f : S. n ≃* S. n) :
    deg f = 1 ⊎ deg f = -1 :=
  begin
    induction H with n,
    apply eq_one_or_eq_neg_one_of_mul_eq_one (deg f⁻¹ᵉ*),
    refine !deg_compose⁻¹ ⬝ _,
    refine deg_phomotopy (pright_inv f) ⬝ _,
    apply deg_id,
  end

end sphere
