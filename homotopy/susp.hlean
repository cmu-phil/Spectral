import homotopy.susp types.pointed2

open susp eq pointed function is_equiv

namespace susp
  variables {X X' Y Y' Z : Type*}
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
