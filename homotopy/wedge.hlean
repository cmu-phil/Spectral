-- Authors: Floris van Doorn

import homotopy.wedge homotopy.cofiber ..move_to_lib .pushout

open wedge pushout eq prod sum pointed equiv is_equiv unit lift bool option

namespace wedge

variable (A : Type*)
variables {A}


definition add_point_of_wedge_pbool [unfold 2]
  (x : A ∨ pbool) : A₊ :=
begin
  induction x with a b,
  { exact some a },
  { induction b, exact some pt, exact none },
  { reflexivity }
end

definition wedge_pbool_of_add_point [unfold 2]
  (x : A₊) : A ∨ pbool :=
begin
  induction x with a,
  { exact inr tt },
  { exact inl a }
end

variables (A)
definition wedge_pbool_equiv_add_point [constructor] :
  A ∨ pbool ≃ A₊ :=
equiv.MK add_point_of_wedge_pbool wedge_pbool_of_add_point
  abstract begin
    intro x, induction x,
    { reflexivity },
    { reflexivity }
  end end
  abstract begin
    intro x, induction x with a b,
    { reflexivity },
    { induction b, exact wedge.glue, reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose wedge_pbool_of_add_point _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
      exact square_of_eq idp }
  end end

  definition wedge_flip' [unfold 3] {A B : Type*} (x : A ∨ B) : B ∨ A :=
  begin
    induction x,
    { exact inr a },
    { exact inl a },
    { exact (glue ⋆)⁻¹ }
  end

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

  protected definition pelim [constructor] {X Y Z : Type*} (f : X →* Z) (g : Y →* Z) : X ∨ Y →* Z :=
  pmap.mk (wedge.elim f g (respect_pt f ⬝ (respect_pt g)⁻¹)) (respect_pt f)

  definition wedge_pr1 [constructor] (X Y : Type*) : X ∨ Y →* X := wedge.pelim (pid X) (pconst Y X)
  definition wedge_pr2 [constructor] (X Y : Type*) : X ∨ Y →* Y := wedge.pelim (pconst X Y) (pid Y)

  open fiber prod cofiber pi

variables {X Y : Type*}
definition pcofiber_pprod_incl1_of_pfiber_wedge_pr2' [unfold 3]
  (x : pfiber (wedge_pr2 X Y)) : pcofiber (pprod_incl1 (Ω Y) X) :=
begin
  induction x with x p, induction x with x y,
  { exact cod _ (p, x) },
  { exact pt },
  { apply arrow_pathover_constant_right, intro p, apply cofiber.glue }
end

--set_option pp.all true
/-
  X : Type* has a nondegenerate basepoint iff
  it has the homotopy extension property iff
  Π(f : X → Y) (y : Y) (p : f pt = y), ∃(g : X → Y) (h : f ~ g) (q : y = g pt), h pt = p ⬝ q
 (or Σ?)
-/

definition pfiber_wedge_pr2_of_pcofiber_pprod_incl1' [unfold 3]
  (x : pcofiber (pprod_incl1 (Ω Y) X)) : pfiber (wedge_pr2 X Y) :=
begin
  induction x with v p,
  { induction v with p x, exact fiber.mk (inl x) p },
  { exact fiber.mk (inr pt) idp },
  { esimp, apply fiber_eq (wedge.glue ⬝ ap inr p), symmetry,
      refine !ap_con ⬝ !wedge.elim_glue ◾ (!ap_compose'⁻¹ ⬝ !ap_id) ⬝ !idp_con }
end

variables (X Y)
definition pcofiber_pprod_incl1_of_pfiber_wedge_pr2 [constructor] :
  pfiber (wedge_pr2 X Y) →* pcofiber (pprod_incl1 (Ω Y) X) :=
pmap.mk pcofiber_pprod_incl1_of_pfiber_wedge_pr2' (cofiber.glue idp)

-- definition pfiber_wedge_pr2_of_pprod [constructor] :
--   Ω Y ×* X →* pfiber (wedge_pr2 X Y) :=
-- begin
--   fapply pmap.mk,
--   { intro v, induction v with p x, exact fiber.mk (inl x) p },
--   { reflexivity }
-- end

definition pfiber_wedge_pr2_of_pcofiber_pprod_incl1 [constructor] :
  pcofiber (pprod_incl1 (Ω Y) X) →* pfiber (wedge_pr2 X Y) :=
pmap.mk pfiber_wedge_pr2_of_pcofiber_pprod_incl1'
  begin refine (fiber_eq wedge.glue _)⁻¹, exact !wedge.elim_glue⁻¹ end
-- pcofiber.elim (pfiber_wedge_pr2_of_pprod X Y)
--   begin
--     fapply phomotopy.mk,
--     { intro p, apply fiber_eq (wedge.glue ⬝ ap inr p ⬝ wedge.glue⁻¹), symmetry,
--       refine !ap_con ⬝ (!ap_con ⬝ !wedge.elim_glue ◾ (!ap_compose'⁻¹ ⬝ !ap_id)) ◾
--         (!ap_inv ⬝ !wedge.elim_glue⁻²) ⬝ _, exact idp_con p },
--     { esimp, refine fiber_eq2 (con.right_inv wedge.glue) _ ⬝ !fiber_eq_eta⁻¹,
--       rewrite [idp_con, ↑fiber_eq_pr2, con2_idp, whisker_right_idp, whisker_right_idp],
--       -- refine _ ⬝ (eq_bot_of_square (transpose (ap_con_right_inv_sq
--       --              (wedge.elim (λx : X, Point Y) (@id Y) idp) wedge.glue)))⁻¹,
--       -- refine whisker_right _ !con_inv ⬝ _,
--       exact sorry
-- }
--   end

--set_option pp.notation false
set_option pp.binder_types true
open sigma.ops
definition pfiber_wedge_pr2_pequiv_pcofiber_pprod_incl1 [constructor] :
  pfiber (wedge_pr2 X Y) ≃* pcofiber (pprod_incl1 (Ω Y) X) :=
pequiv.MK (pcofiber_pprod_incl1_of_pfiber_wedge_pr2 _ _)
          (pfiber_wedge_pr2_of_pcofiber_pprod_incl1 _ _)
  abstract begin
    fapply phomotopy.mk,
    { intro x, esimp, induction x with x p,  induction x with x y,
      { reflexivity },
      { refine (fiber_eq (ap inr p) _)⁻¹, refine !ap_id⁻¹ ⬝ !ap_compose' },
      { apply @pi_pathover_right' _ _ _ _ (λ(xp : Σ(x : X ∨ Y), pppi.to_fun (wedge_pr2 X Y) x = pt),
          pfiber_wedge_pr2_of_pcofiber_pprod_incl1'
          (pcofiber_pprod_incl1_of_pfiber_wedge_pr2' (mk xp.1 xp.2)) = mk xp.1 xp.2),
        intro p, apply eq_pathover, exact sorry }},
    { symmetry, refine !cofiber.elim_glue ◾ idp ⬝ _, apply con_inv_eq_idp,
      apply ap (fiber_eq wedge.glue), esimp, rewrite [idp_con], refine !whisker_right_idp⁻² }
  end end
  abstract begin
    exact sorry
  end end
-- apply eq_pathover_id_right, refine ap_compose pcofiber_pprod_incl1_of_pfiber_wedge_pr2 _ _ ⬝ ap02 _ !elim_glue ⬝ph _
-- apply eq_pathover_id_right, refine ap_compose pfiber_wedge_pr2_of_pcofiber_pprod_incl1 _ _ ⬝ ap02 _ !elim_glue ⬝ph _

/- move -/
definition ap1_idp {A B : Type*} (f : A →* B) : Ω→ f idp = idp :=
respect_pt (Ω→ f)

definition ap1_phomotopy_idp {A B : Type*} {f g : A →* B} (h : f ~* g) :
  Ω⇒ h idp = !respect_pt ⬝ !respect_pt⁻¹ :=
sorry


variables {A} {B : Type*} {f : A →* B} {g : B →* A} (h : f ∘* g ~* pid B)
include h
definition nar_of_noo' (p : Ω A) : Ω (pfiber f) ×* Ω B :=
begin
  refine (_, Ω→ f p),
  have z : Ω A →* Ω A, from pmap.mk (λp, Ω→ (g ∘* f) p ⬝ p⁻¹) proof (respect_pt (Ω→ (g ∘* f))) qed,
  refine fiber_eq ((Ω→ g ∘* Ω→ f) p ⬝ p⁻¹) (!idp_con⁻¹ ⬝ whisker_right (respect_pt f) _⁻¹),
  induction B with B b₀, induction f with f f₀, esimp at * ⊢, induction f₀,
  refine !idp_con⁻¹ ⬝ ap1_con (pmap_of_map f pt) _ _ ⬝
    ((ap1_pcompose (pmap_of_map f pt) g _)⁻¹ ⬝ Ω⇒ h _ ⬝ ap1_pid _) ◾ ap1_inv _ _ ⬝ !con.right_inv
end

definition noo_of_nar' (x : Ω (pfiber f) ×* Ω B) : Ω A :=
begin
  induction x with p q, exact Ω→ (ppoint f) p ⬝ Ω→ g q
end

variables (f g)
definition nar_of_noo [constructor] :
  Ω A →* Ω (pfiber f) ×* Ω B :=
begin
  refine pmap.mk (nar_of_noo' h) (prod_eq _ (ap1_gen_idp f (respect_pt f))),
  esimp [nar_of_noo'],
  refine fiber_eq2 (ap (ap1_gen _ _ _) (ap1_gen_idp f _) ⬝ !ap1_gen_idp) _ ⬝ !fiber_eq_eta⁻¹,
  induction B with B b₀, induction f with f f₀, esimp at * ⊢, induction f₀, esimp,
  refine (!idp_con ⬝ !whisker_right_idp) ◾ !whisker_right_idp ⬝ _, esimp [fiber_eq_pr2],
  apply inv_con_eq_idp,
  refine ap (ap02 f) !idp_con ⬝ _,
  esimp [ap1_con, ap1_gen_con, ap1_inv, ap1_gen_inv],
  refine _ ⬝ whisker_left _ (!con2_idp ⬝ !whisker_right_idp ⬝ idp ◾ ap1_phomotopy_idp h)⁻¹ᵖ,
  esimp, exact sorry
end

definition noo_of_nar [constructor] :
  Ω (pfiber f) ×* Ω B →* Ω A :=
pmap.mk (noo_of_nar' h) (respect_pt (Ω→ (ppoint f)) ◾ respect_pt (Ω→ g))

definition noo_pequiv_nar [constructor] :
  Ω A ≃* Ω (pfiber f) ×* Ω B :=
pequiv.MK (nar_of_noo f g h) (noo_of_nar f g h)
  abstract begin
    exact sorry
  end end
  abstract begin
    exact sorry
  end end
-- apply eq_pathover_id_right, refine ap_compose nar_of_noo _ _ ⬝ ap02 _ !elim_glue ⬝ph _
-- apply eq_pathover_id_right, refine ap_compose noo_of_nar _ _ ⬝ ap02 _ !elim_glue ⬝ph _

  definition loop_pequiv_of_cross_section {A B : Type*} (f : A →* B) (g : B →* A)
    (h : f ∘* g ~* pid B) : Ω A ≃* Ω (pfiber f) ×* Ω B :=







end wedge
