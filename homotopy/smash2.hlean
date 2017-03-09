import .smash_adjoint

-- Authors: Floris van Doorn

import homotopy.smash ..pointed .pushout homotopy.red_susp

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function red_susp unit

  /- To prove: Σ(X × Y) ≃ ΣX ∨ ΣY ∨ Σ(X ∧ Y) (?) (notation means suspension, wedge, smash) -/

  /- To prove: Σ(X ∧ Y) ≃ X ★ Y (?) (notation means suspension, smash, join) -/

  /- To prove: A ∧ S¹ ≃ ΣA -/

  /- associativity is proven in smash_adjoint -/
variables {A A' B B' C C' D E F : Type*}

namespace smash

  definition smash_pelim2 [constructor] (A B C : Type*) : ppmap A (ppmap B C) →* ppmap (B ∧ A) C :=
  ppcompose_left (smash_pmap_counit B C) ∘* smash_functor_right B A (ppmap B C)

  definition smash_pelim2_natural (f : C →* C') :
    psquare (smash_pelim2 A B C) (smash_pelim2 A B C')
            (ppcompose_left (ppcompose_left f)) (ppcompose_left f) :=
  smash_functor_right_natural_right (ppcompose_left f) ⬝h*
  ppcompose_left_psquare (smash_pmap_counit_natural f)

--ppmap B C →* ppmap (A ∧ B) (A ∧ C)
  definition smash_functor_right_natural_middle (f : B' →* B) :
    psquare (smash_functor_right A B C) (smash_functor_right A B' C)
            (ppcompose_right f) (ppcompose_right (pid A ∧→ f)) :=
  begin
    refine _⁻¹*,
    fapply phomotopy_mk_ppmap,
    { intro g, exact smash_functor_pid_pcompose A g f },
    { refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !smash_functor_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply smash_functor_pid_pconst_pcompose }
  end

  definition smash_functor_right_natural_left_lemma (f : A →* A')
    : phsquare (smash_functor_psquare (phomotopy.rfl : psquare f f !pid !pid)
                                      (phomotopy.rfl : psquare !pid !pid (pconst B C) (pconst B C)))
               (pconst_pcompose (f ∧→ pid B))
               (pwhisker_right (f ∧→ pid B) (smash_functor_pconst_right (pid A')))
               (pwhisker_right (f ∧→ pid B) (smash_functor_pconst_right (pid A')) ⬝*
                 pconst_pcompose (f ∧→ pid B)) :=
  begin
    -- refine !trans_assoc ⬝pv** _,
    -- apply phmove_top_of_left',
    -- refine _ ⬝ (!trans_assoc ⬝ !smash_functor_pconst_pcompose)⁻¹,
    -- refine !trans_assoc⁻¹ ⬝ trans_eq_of_eq_trans_symm _,
    -- refine _ ⬝hp** !pwhisker_left_trans⁻¹,
    -- refine (smash_functor_phomotopy_phsquare (phvrfl ⬝hp** !pcompose2_refl⁻¹)
    --   (!pcompose2_refl_left ⬝ph** !pid_pconst_pcompose)⁻¹ʰ** ⬝h**
    --   !smash_functor_pcompose_phomotopy ⬝hp**
    --   (!smash_functor_phomotopy_refl ◽* idp ⬝ !pcompose2_refl_left)) ⬝v** _,
    -- refine ((!smash_functor_phomotopy_trans⁻¹ ⬝
    --   ap011 smash_functor_phomotopy !trans_refl !refl_trans) ◾** idp) ⬝ph** idp ⬝ _,
    -- refine !trans_assoc ⬝ !trans_assoc ⬝ _,
    -- apply trans_eq_of_eq_symm_trans,
    -- refine _ ⬝ !trans_assoc ⬝ (ap (smash_functor_phomotopy _) !refl_symm⁻¹ ⬝
    --   !smash_functor_phomotopy_symm) ◾** idp,
    -- refine _ ⬝ !smash_functor_pconst_right_phomotopy⁻¹ ◾** idp,
    -- apply trans_eq_of_eq_symm_trans,
    -- refine _ ⬝ !trans_assoc ⬝ (ap011 smash_functor_phomotopy !refl_symm⁻¹ !refl_symm⁻¹ ⬝
    --   !smash_functor_phomotopy_symm) ◾** idp,
    -- apply eq_trans_symm_of_trans_eq, refine !trans_assoc ⬝ _,
    -- apply smash_functor_pcompose_pconst
  end

  definition smash_functor_right_natural_left (f : A →* A') :
    psquare (smash_functor_right A B C) (ppcompose_right (f ∧→ (pid B)))
            (smash_functor_right A' B C) (ppcompose_left (f ∧→ (pid C))) :=
  begin
    refine _⁻¹*,
    fapply phomotopy_mk_ppmap,
    { intro g, exact smash_functor_psquare proof phomotopy.rfl qed proof phomotopy.rfl qed },
    { esimp,
      refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      -- apply smash_functor_pid_pcompose_pconst

}
  end

  definition smash_pelim2_natural_left (B C : Type*) (f : A' →* A) :
    psquare (smash_pelim2 A B C) (smash_pelim2 A' B C)
            (ppcompose_right f) (ppcompose_right (pid B ∧→ f)) :=
  smash_functor_right_natural_middle f ⬝h* !ppcompose_left_ppcompose_right

  definition smash_pelim2_natural_middle (A C : Type*) (g : B' →* B) :
    psquare (smash_pelim2 A B C) (smash_pelim2 A B' C)
            (ppcompose_left (ppcompose_right g)) (ppcompose_right (g ∧→ pid A)) :=
  pwhisker_tl _ !ppcompose_left_ppcompose_right ⬝*
  (!smash_functor_right_natural_left⁻¹* ⬝pv*
  smash_functor_right_natural_right (ppcompose_right g) ⬝h*
  ppcompose_left_psquare !smash_pmap_counit_natural_left)

  definition smash_functor_split (f : A →* C) (g : B →* D) :
    f ∧→ g ~* (pid C) ∧→ g ∘* f ∧→ (pid B)  :=
  smash_functor_phomotopy !pid_pcompose⁻¹* !pcompose_pid⁻¹* ⬝* !smash_functor_pcompose

  definition smash_pelim2_natural_lm (C : Type*) (f : A' →* A) (g : B' →* B) :
    psquare (smash_pelim2 A B C) (smash_pelim2 A' B' C)
            (ppcompose_left (ppcompose_right g) ∘* ppcompose_right f) (ppcompose_right (g ∧→ f)) :=
  smash_pelim2_natural_left B C f ⬝v* smash_pelim2_natural_middle A' C g ⬝hp*
  ppcompose_right_phomotopy proof !smash_functor_split qed ⬝* !ppcompose_right_pcompose

end smash
