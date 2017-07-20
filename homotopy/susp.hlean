import homotopy.susp types.pointed2 ..move_to_lib

open susp eq pointed function is_equiv lift equiv is_trunc nat

namespace susp
  variables {X X' Y Y' Z : Type*}

  definition susp_functor_pconst_homotopy [unfold 3] {X Y : Type*} (x : susp X) :
    susp_functor (pconst X Y) x = pt :=
  begin
    induction x,
    { reflexivity },
    { exact (merid pt)⁻¹ },
    { apply eq_pathover, refine !elim_merid ⬝ph _ ⬝hp !ap_constant⁻¹, exact square_of_eq !con.right_inv⁻¹ }
  end

  definition susp_functor_pconst [constructor] (X Y : Type*) : susp_functor (pconst X Y) ~* pconst (susp X) (susp Y) :=
  begin
    fapply phomotopy.mk,
    { exact susp_functor_pconst_homotopy },
    { reflexivity }
  end

  definition susp_pfunctor [constructor] (X Y : Type*) : ppmap X Y →* ppmap (susp X) (susp Y) :=
  pmap.mk susp_functor (eq_of_phomotopy !susp_functor_pconst)

  definition susp_pelim [constructor] (X Y : Type*) : ppmap X (Ω Y) →* ppmap (susp X) Y :=
  ppcompose_left (loop_susp_counit Y) ∘* susp_pfunctor X (Ω Y)

  definition loop_susp_pintro [constructor] (X Y : Type*) : ppmap (susp X) Y →* ppmap X (Ω Y) :=
  ppcompose_right (loop_susp_unit X) ∘* pap1 (susp X) Y

  definition loop_susp_pintro_natural_left (f : X' →* X) :
    psquare (loop_susp_pintro X Y) (loop_susp_pintro X' Y)
            (ppcompose_right (susp_functor f)) (ppcompose_right f) :=
  !pap1_natural_left ⬝h* ppcompose_right_psquare (loop_susp_unit_natural f)⁻¹*

  definition loop_susp_pintro_natural_right (f : Y →* Y') :
    psquare (loop_susp_pintro X Y) (loop_susp_pintro X Y')
            (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  !pap1_natural_right ⬝h* !ppcompose_left_ppcompose_right⁻¹*

  definition is_equiv_loop_susp_pintro [constructor] (X Y : Type*) :
    is_equiv (loop_susp_pintro X Y) :=
  begin
    fapply adjointify,
    { exact susp_pelim X Y },
    { intro g, apply eq_of_phomotopy, exact susp_adjoint_loop_right_inv g },
    { intro f, apply eq_of_phomotopy, exact susp_adjoint_loop_left_inv f }
  end

  definition susp_adjoint_loop' [constructor] (X Y : Type*) : ppmap (susp X) Y ≃* ppmap X (Ω Y) :=
  pequiv_of_pmap (loop_susp_pintro X Y) (is_equiv_loop_susp_pintro X Y)

  definition susp_adjoint_loop_natural_right (f : Y →* Y') :
    psquare (susp_adjoint_loop' X Y) (susp_adjoint_loop' X Y')
            (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  loop_susp_pintro_natural_right f

  definition susp_adjoint_loop_natural_left (f : X' →* X) :
    psquare (susp_adjoint_loop' X Y) (susp_adjoint_loop' X' Y)
            (ppcompose_right (susp_functor f)) (ppcompose_right f) :=
  loop_susp_pintro_natural_left f

  definition iterate_susp_iterate_susp_rev (n m : ℕ) (A : Type*) :
    iterate_susp n (iterate_susp m A) ≃* iterate_susp (m + n) A :=
  begin
    induction n with n e,
    { reflexivity },
    { exact susp_pequiv e }
  end

  definition iterate_susp_pequiv [constructor] (n : ℕ) {X Y : Type*} (f : X ≃* Y) :
    iterate_susp n X ≃* iterate_susp n Y :=
  begin
    induction n with n e,
    { exact f },
    { exact susp_pequiv e }
  end

  open algebra nat
  definition iterate_susp_iterate_susp (n m : ℕ) (A : Type*) :
    iterate_susp n (iterate_susp m A) ≃* iterate_susp (n + m) A :=
  iterate_susp_iterate_susp_rev n m A ⬝e* pequiv_of_eq (ap (λk, iterate_susp k A) (add.comm m n))

  definition plift_susp.{u v} : Π(A : Type*), plift.{u v} (susp A) ≃* susp (plift.{u v} A) :=
  begin
    intro A,
    calc
      plift.{u v} (susp A) ≃* susp A               : by exact (pequiv_plift (susp A))⁻¹ᵉ*
                        ... ≃* susp (plift.{u v} A) : by exact susp_pequiv (pequiv_plift.{u v} A)
  end

  definition is_contr_susp [instance] (A : Type) [H : is_contr A] : is_contr (susp A) :=
  begin
    apply is_contr.mk north,
    intro x, induction x,
    reflexivity,
    exact merid !center,
    apply eq_pathover_constant_left_id_right, apply square_of_eq,
    exact whisker_left idp (ap merid !eq_of_is_contr)
  end

  definition loop_susp_pintro_phomotopy {X Y : Type*} {f g : ⅀ X →* Y} (p : f ~* g) :
    loop_susp_pintro X Y f ~* loop_susp_pintro X Y g :=
  pwhisker_right (loop_susp_unit X) (Ω⇒ p)

  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type*}
            {f₁₀ : A₀₀ →* A₂₀} {f₁₂ : A₀₂ →* A₂₂}
            {f₀₁ : A₀₀ →* A₀₂} {f₂₁ : A₂₀ →* A₂₂}

  -- rename: susp_functor_psquare
  definition suspend_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : psquare (⅀→ f₁₀) (⅀→ f₁₂) (⅀→ f₀₁) (⅀→ f₂₁) :=
sorry

  definition susp_to_loop_psquare (f₁₀ : A₀₀ →* A₂₀) (f₁₂ : A₀₂ →* A₂₂) (f₀₁ : susp A₀₀ →* A₀₂) (f₂₁ : susp A₂₀ →* A₂₂) : (psquare (⅀→ f₁₀) f₁₂ f₀₁ f₂₁) → (psquare f₁₀ (Ω→ f₁₂) ((loop_susp_pintro A₀₀ A₀₂) f₀₁) ((loop_susp_pintro A₂₀ A₂₂) f₂₁)) :=
  begin
    intro p,
    refine pvconcat _ (ap1_psquare p),
    exact loop_susp_unit_natural f₁₀
  end

  definition loop_to_susp_square (f₁₀ : A₀₀ →* A₂₀) (f₁₂ : A₀₂ →* A₂₂) (f₀₁ : A₀₀ →* Ω A₀₂) (f₂₁ : A₂₀ →* Ω A₂₂) : (psquare f₁₀ (Ω→ f₁₂) f₀₁ f₂₁) → (psquare (⅀→ f₁₀) f₁₂ ((susp_pelim A₀₀ A₀₂) f₀₁) ((susp_pelim A₂₀ A₂₂) f₂₁)) :=
  begin
    intro p,
    refine pvconcat (suspend_psquare p) _,
    exact psquare_transpose (loop_susp_counit_natural f₁₂)
  end

end susp
