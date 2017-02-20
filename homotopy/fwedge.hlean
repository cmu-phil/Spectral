/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Ulrik Buchholtz

The Wedge Sum of a family of Pointed Types
-/
import homotopy.wedge ..move_to_lib ..choice

open eq pushout pointed unit trunc_index sigma bool equiv trunc choice unit is_trunc

definition fwedge' {I : Type} (F : I → Type*) : Type := pushout (λi, ⟨i, Point (F i)⟩) (λi, ⋆)
definition pt' [constructor] {I : Type} {F : I → Type*} : fwedge' F := inr ⋆
definition fwedge [constructor] {I : Type} (F : I → Type*) : Type* := pointed.MK (fwedge' F) pt'

notation `⋁` := fwedge

namespace fwedge
  variables {I : Type} {F : I → Type*}

  definition il {i : I} (x : F i) : ⋁F := inl ⟨i, x⟩
  definition inl (i : I) (x : F i) : ⋁F := il x
  definition pinl [constructor] (i : I) : F i →* ⋁F := pmap.mk (inl i) (glue i)
  definition glue (i : I) : inl i pt = pt :> ⋁ F := glue i

  protected definition rec {P : ⋁F → Type} (Pinl : Π(i : I) (x : F i), P (il x))
    (Pinr : P pt) (Pglue : Πi, pathover P (Pinl i pt) (glue i) (Pinr)) (y : fwedge' F) : P y :=
  begin induction y, induction x, apply Pinl, induction x, apply Pinr, apply Pglue end

  protected definition elim {P : Type} (Pinl : Π(i : I) (x : F i), P)
    (Pinr : P) (Pglue : Πi, Pinl i pt = Pinr) (y : fwedge' F) : P :=
  begin induction y with x u, induction x with i x, exact Pinl i x, induction u, apply Pinr, apply Pglue end

  protected definition elim_glue {P : Type} {Pinl : Π(i : I) (x : F i), P}
    {Pinr : P} (Pglue : Πi, Pinl i pt = Pinr) (i : I)
    : ap (fwedge.elim Pinl Pinr Pglue) (fwedge.glue i) = Pglue i :=
  !pushout.elim_glue

  protected definition rec_glue {P : ⋁F → Type} {Pinl : Π(i : I) (x : F i), P (il x)}
    {Pinr : P pt} (Pglue : Πi, pathover P (Pinl i pt) (glue i) (Pinr)) (i : I)
    : apd (fwedge.rec Pinl Pinr Pglue) (fwedge.glue i) = Pglue i :=
  !pushout.rec_glue

end fwedge

attribute fwedge.rec fwedge.elim [recursor 7] [unfold 7]
attribute fwedge.il fwedge.inl [constructor]

namespace fwedge

  definition fwedge_of_pwedge [unfold 3] {A B : Type*} (x : A ∨ B) : ⋁(bool.rec A B) :=
  begin
    induction x with a b,
    { exact inl ff a },
    { exact inl tt b },
    { exact glue ff ⬝ (glue tt)⁻¹ }
  end

  definition pwedge_of_fwedge [unfold 3] {A B : Type*} (x : ⋁(bool.rec A B)) : A ∨ B :=
  begin
    induction x with b x b,
    { induction b, exact pushout.inl x, exact pushout.inr x },
    { exact pushout.inr pt },
    { induction b, exact pushout.glue ⋆, reflexivity }
  end

  definition pwedge_pequiv_fwedge [constructor] (A B : Type*) : A ∨ B ≃* ⋁(bool.rec A B) :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact fwedge_of_pwedge },
      { exact pwedge_of_fwedge },
      { exact abstract begin intro x, induction x with b x b,
        { induction b: reflexivity },
        { exact glue tt },
        { apply eq_pathover_id_right,
          refine ap_compose fwedge_of_pwedge _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
          induction b, exact !elim_glue ⬝ph whisker_bl _ hrfl, apply square_of_eq idp }
        end end },
      { exact abstract begin intro x, induction x with a b,
        { reflexivity },
        { reflexivity },
        { apply eq_pathover_id_right,
          refine ap_compose pwedge_of_fwedge _ _ ⬝ ap02 _ !elim_glue ⬝ !ap_con ⬝
                 !elim_glue ◾ (!ap_inv ⬝ !elim_glue⁻²) ⬝ph _, exact hrfl } end end}},
    { exact glue ff }
  end

  definition is_contr_fwedge_empty : is_contr (⋁(empty.rec _)) :=
  begin
    apply is_contr.mk pt, intro x, induction x, contradiction, reflexivity, contradiction
  end

  definition fwedge_pmap [constructor] {I : Type} {F : I → Type*} {X : Type*} (f : Πi, F i →* X) : ⋁F →* X :=
  begin
    fconstructor,
    { intro x, induction x,
        exact f i x,
        exact pt,
        exact respect_pt (f i) },
    { reflexivity }
  end

  definition fwedge_pmap_beta [constructor] {I : Type} {F : I → Type*} {X : Type*} (f : Πi, F i →* X) (i : I) :
    fwedge_pmap f ∘* pinl i ~* f i :=
  begin
    fconstructor,
    { reflexivity },
    { exact !idp_con ⬝ !fwedge.elim_glue⁻¹ }
  end

  definition fwedge_pmap_eta [constructor] {I : Type} {F : I → Type*} {X : Type*} (g : ⋁F →* X) :
    fwedge_pmap (λi, g ∘* pinl i) ~* g :=
  begin
    fconstructor,
    { intro x, induction x,
        reflexivity,
        exact (respect_pt g)⁻¹,
        apply eq_pathover, refine !elim_glue ⬝ph _, apply whisker_lb, exact hrfl },
    { exact con.left_inv (respect_pt g) }
  end

  definition fwedge_pmap_equiv [constructor] {I : Type} (F : I → Type*) (X : Type*) :
    ⋁F →* X ≃ Πi, F i →* X :=
  begin
    fapply equiv.MK,
    { intro g i, exact g ∘* pinl i },
    { exact fwedge_pmap },
    { intro f, apply eq_of_homotopy, intro i, apply eq_of_phomotopy, apply fwedge_pmap_beta f i },
    { intro g, apply eq_of_phomotopy, exact fwedge_pmap_eta g }
  end

  definition trunc_fwedge_pmap_equiv.{u} {n : ℕ₋₂} {I : Type.{u}} (H : has_choice n I)
    (F : I → pType.{u}) (X : pType.{u}) : trunc n (⋁F →* X) ≃ Πi, trunc n (F i →* X) :=
  trunc_equiv_trunc n (fwedge_pmap_equiv F X) ⬝e choice_equiv H (λi, F i →* X)

end fwedge
