-- Authors: Floris van Doorn

import homotopy.wedge

open wedge pushout eq prod sum pointed equiv is_equiv unit lift

namespace wedge

  definition wedge_flip' [unfold 3] {A B : Type*} (x : A ∨ B) : B ∨ A :=
  begin
    induction x,
    { exact inr a },
    { exact inl a },
    { exact (glue ⋆)⁻¹ }
  end

  -- TODO: fix precedences
  definition wedge_flip [constructor] (A B : Type*) : A ∨ B →* B ∨ A :=
  pmap.mk wedge_flip' (glue ⋆)⁻¹

  definition wedge_flip'_wedge_flip' [unfold 3] {A B : Type*} (x : A ∨ B) : wedge_flip' (wedge_flip' x) = x :=
  begin
    induction x,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_id_right,
     apply hdeg_square,
     exact ap_compose wedge_flip' _ _ ⬝ ap02 _ !elim_glue ⬝ !ap_inv ⬝ !elim_glue⁻² ⬝ !inv_inv }
  end

  definition wedge_flip_wedge_flip (A B : Type*) :
    wedge_flip B A ∘* wedge_flip A B ~* pid (A ∨ B) :=
  phomotopy.mk wedge_flip'_wedge_flip'
    proof (whisker_right _ (!ap_inv ⬝ !wedge.elim_glue⁻²) ⬝ !con.left_inv)⁻¹ qed

  definition wedge_comm [constructor] (A B : Type*) : A ∨ B ≃* B ∨ A :=
  begin
    fapply pequiv.MK,
    { exact wedge_flip A B },
    { exact wedge_flip B A },
    { exact wedge_flip_wedge_flip A B },
    { exact wedge_flip_wedge_flip B A }
  end

  -- TODO: wedge is associative

  definition wedge_shift [unfold 3] {A B C : Type*} (x : (A ∨ B) ∨ C) : (A ∨ (B ∨ C)) :=
  begin
    induction x with l,
    induction l with a,
    exact inl a,
    exact inr (inl a),
    exact (glue ⋆),
    exact inr (inr a),
    -- exact elim_glue _ _ _,
    exact sorry

  end


  definition wedge_pequiv [constructor] {A A' B B' : Type*} (a : A ≃* A') (b : B ≃* B') : A ∨ B ≃* A' ∨ B' :=
  begin
    fapply pequiv_of_equiv,
    exact pushout.equiv !pconst !pconst !pconst !pconst !pequiv.refl a b (λdummy, respect_pt a) (λdummy, respect_pt b),
    exact ap pushout.inl (respect_pt a)
  end

  definition plift_wedge.{u v} (A B : Type*) : plift.{u v} (A ∨ B) ≃* plift.{u v} A ∨ plift.{u v} B :=
  calc plift.{u v} (A ∨ B) ≃* A ∨ B : by exact !pequiv_plift⁻¹ᵉ*
                       ... ≃* plift.{u v} A ∨ plift.{u v} B : by exact wedge_pequiv !pequiv_plift !pequiv_plift

end wedge
