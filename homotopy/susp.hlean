import ..pointed

open susp eq pointed function is_equiv
  variables {X X' Y Y' Z : Type*}

-- move
  definition pap1 [constructor] (X Y : Type*) : ppmap X Y →* ppmap (Ω X) (Ω Y) :=
  pmap.mk ap1 (eq_of_phomotopy !ap1_pconst)

  definition ap1_gen_const {A B : Type} {a₁ a₂ : A} (b : B) (p : a₁ = a₂) :
    ap1_gen (const A b) idp idp p = idp :=
  ap1_gen_idp_left (const A b) p ⬝ ap_constant p b

  definition ap1_gen_compose_const_left
    {A B C : Type} (c : C) (f : A → B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose (const B c) f idp idp idp idp p ⬝
    ap1_gen_const c (ap1_gen f idp idp p) =
    ap1_gen_const c p :=
  begin induction p, reflexivity end

  definition ap1_gen_compose_const_right
    {A B C : Type} (g : B → C) (b : B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose g (const A b) idp idp idp idp p ⬝
    ap (ap1_gen g idp idp) (ap1_gen_const b p) =
    ap1_gen_const (g b) p :=
  begin induction p, reflexivity end

  definition ap1_pcompose_pconst_left {A B C : Type*} (f : A →* B) :
    phsquare (ap1_pcompose (pconst B C) f)
             (ap1_pconst A C)
             (ap1_phomotopy (pconst_pcompose f))
             (pwhisker_right (Ω→ f) (ap1_pconst B C) ⬝* pconst_pcompose (Ω→ f)) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction f with f f₀,
    esimp at *, induction f₀,
    refine idp ◾** !trans_refl ⬝ _ ⬝ !refl_trans⁻¹ ⬝ !ap1_phomotopy_refl⁻¹ ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_left c₀ f },
    { reflexivity }
  end

  definition ap1_pcompose_pconst_right {A B C : Type*} (g : B →* C) :
    phsquare (ap1_pcompose g (pconst A B))
             (ap1_pconst A C)
             (ap1_phomotopy (pcompose_pconst g))
             (pwhisker_left (Ω→ g) (ap1_pconst A B) ⬝* pcompose_pconst (Ω→ g)) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction g with g g₀,
    esimp at *, induction g₀,
    refine idp ◾** !trans_refl ⬝ _ ⬝ !refl_trans⁻¹ ⬝ !ap1_phomotopy_refl⁻¹ ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_right g b₀ },
    { reflexivity }
  end

  definition pap1_natural_left [constructor] (f : X' →* X) :
    psquare (pap1 X Y) (pap1 X' Y) (ppcompose_right f) (ppcompose_right (Ω→ f)) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro g, exact !ap1_pcompose⁻¹* },
    { refine idp ◾** (ap phomotopy_of_eq (!ap1_eq_of_phomotopy  ◾ idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝
      !phomotopy_of_eq_of_phomotopy)  ⬝ _ ⬝ (ap phomotopy_of_eq (!pcompose_right_eq_of_phomotopy ◾
      idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝ !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_left f)⁻¹ }
  end

  definition pap1_natural_right [constructor] (f : Y →* Y') :
    psquare (pap1 X Y) (pap1 X Y') (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro g, exact !ap1_pcompose⁻¹* },
    { refine idp ◾** (ap phomotopy_of_eq (!ap1_eq_of_phomotopy  ◾ idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝
      !phomotopy_of_eq_of_phomotopy)  ⬝ _ ⬝ (ap phomotopy_of_eq (!pcompose_left_eq_of_phomotopy ◾
      idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝ !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_right f)⁻¹ }
  end

namespace susp

  definition susp_functor_pconst_homotopy [unfold 3] {X Y : Type*} (x : psusp X) :
    psusp_functor (pconst X Y) x = pt :=
  begin
    induction x,
    { reflexivity },
    { exact (merid pt)⁻¹ },
    { apply eq_pathover, refine !elim_merid ⬝ph _ ⬝hp !ap_constant⁻¹, exact square_of_eq !con.right_inv⁻¹ }
  end

  definition susp_functor_pconst [constructor] (X Y : Type*) : psusp_functor (pconst X Y) ~* pconst (psusp X) (psusp Y) :=
  begin
    fapply phomotopy.mk,
    { exact susp_functor_pconst_homotopy },
    { reflexivity }
  end

  definition psusp_pfunctor [constructor] (X Y : Type*) : ppmap X Y →* ppmap (psusp X) (psusp Y) :=
  pmap.mk psusp_functor (eq_of_phomotopy !susp_functor_pconst)

  definition psusp_pelim [constructor] (X Y : Type*) : ppmap X (Ω Y) →* ppmap (psusp X) Y :=
  ppcompose_left (loop_psusp_counit Y) ∘* psusp_pfunctor X (Ω Y)

  definition loop_psusp_pintro [constructor] (X Y : Type*) : ppmap (psusp X) Y →* ppmap X (Ω Y) :=
  ppcompose_right (loop_psusp_unit X) ∘* pap1 (psusp X) Y

  definition loop_psusp_pintro_natural_left (f : X' →* X) :
    psquare (loop_psusp_pintro X Y) (loop_psusp_pintro X' Y)
            (ppcompose_right (psusp_functor f)) (ppcompose_right f) :=
  !pap1_natural_left ⬝h* ppcompose_right_psquare (loop_psusp_unit_natural f)⁻¹*

  definition loop_psusp_pintro_natural_right (f : Y →* Y') :
    psquare (loop_psusp_pintro X Y) (loop_psusp_pintro X Y')
            (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  !pap1_natural_right ⬝h* !ppcompose_left_ppcompose_right⁻¹*

  definition is_equiv_loop_psusp_pintro [constructor] (X Y : Type*) :
    is_equiv (loop_psusp_pintro X Y) :=
  begin
    fapply adjointify,
    { exact psusp_pelim X Y },
    { intro g, apply eq_of_phomotopy, exact psusp_adjoint_loop_right_inv g },
    { intro f, apply eq_of_phomotopy, exact psusp_adjoint_loop_left_inv f }
  end

  definition psusp_adjoint_loop' [constructor] (X Y : Type*) : ppmap (psusp X) Y ≃* ppmap X (Ω Y) :=
  pequiv_of_pmap (loop_psusp_pintro X Y) (is_equiv_loop_psusp_pintro X Y)

  definition psusp_adjoint_loop_natural_right (f : Y →* Y') :
    psquare (psusp_adjoint_loop' X Y) (psusp_adjoint_loop' X Y')
            (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  loop_psusp_pintro_natural_right f

  definition psusp_adjoint_loop_natural_left (f : X' →* X) :
    psquare (psusp_adjoint_loop' X Y) (psusp_adjoint_loop' X' Y)
            (ppcompose_right (psusp_functor f)) (ppcompose_right f) :=
  loop_psusp_pintro_natural_left f

  definition iterate_psusp_iterate_psusp_rev (n m : ℕ) (A : Type*) :
    iterate_psusp n (iterate_psusp m A) ≃* iterate_psusp (m + n) A :=
  begin
    induction n with n e,
    { reflexivity },
    { exact psusp_pequiv e }
  end

  definition iterate_psusp_pequiv [constructor] (n : ℕ) {X Y : Type*} (f : X ≃* Y) :
    iterate_psusp n X ≃* iterate_psusp n Y :=
  begin
    induction n with n e,
    { exact f },
    { exact psusp_pequiv e }
  end

  open algebra nat
  definition iterate_psusp_iterate_psusp (n m : ℕ) (A : Type*) :
    iterate_psusp n (iterate_psusp m A) ≃* iterate_psusp (n + m) A :=
  iterate_psusp_iterate_psusp_rev n m A ⬝e* pequiv_of_eq (ap (λk, iterate_psusp k A) (add.comm m n))

end susp
