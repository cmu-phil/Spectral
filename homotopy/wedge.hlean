-- Authors: Floris van Doorn

import homotopy.wedge

open wedge pushout eq prod sum pointed equiv is_equiv unit

namespace wedge

  definition wedge_flip [unfold 3] {A B : Type*} (x : A ∨ B) : B ∨ A :=
  begin
    induction x,
    { exact inr a },
    { exact inl a },
    { exact (glue ⋆)⁻¹ }
  end

  -- TODO: fix precedences
  definition pwedge_flip [constructor] (A B : Type*) : (A ∨ B) →* (B ∨ A) :=
  pmap.mk wedge_flip (glue ⋆)⁻¹

  definition wedge_flip_wedge_flip {A B : Type*} (x : A ∨ B) : wedge_flip (wedge_flip x) = x :=
  begin
    induction x,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_id_right, apply hdeg_square,
      exact ap_compose wedge_flip _ _ ⬝ ap02 _ !elim_glue ⬝ !ap_inv ⬝ !elim_glue⁻² ⬝ !inv_inv }
  end

  definition pwedge_comm [constructor] (A B : Type*) : A ∨ B ≃* B ∨ A :=
  begin
    fapply pequiv.MK,
    { exact pwedge_flip A B },
    { exact wedge_flip },
    { exact wedge_flip_wedge_flip },
    { exact wedge_flip_wedge_flip }
  end

  -- TODO: wedge is associative

end wedge
