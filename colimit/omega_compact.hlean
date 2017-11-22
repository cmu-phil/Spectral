/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import .seq_colim types.unit

open eq nat is_equiv equiv is_trunc pi unit function prod unit sigma sigma.ops sum prod trunc fin
     algebra

namespace seq_colim

  universe variable u
  variables {A : ℕ → Type.{u}} (f : seq_diagram A)
  variables {n : ℕ} (a : A n)

  definition arrow_colim_of_colim_arrow [unfold 4] {X : Type}
    (g : seq_colim (seq_diagram_arrow_left f X)) (x : X) : seq_colim f :=
  begin induction g with n g n g, exact ι f (g x), exact glue f (g x) end

  definition omega_compact [class] (X : Type) : Type :=
  Π⦃A : ℕ → Type⦄ (f : seq_diagram A),
  is_equiv (arrow_colim_of_colim_arrow f :
             seq_colim (seq_diagram_arrow_left f X) → (X → seq_colim f))

  definition equiv_of_omega_compact [unfold 4] (X : Type) [H : omega_compact X]
    {A : ℕ → Type} (f : seq_diagram A) :
    seq_colim (seq_diagram_arrow_left f X) ≃ (X → seq_colim f) :=
  equiv.mk _ (H f)

  definition omega_compact_of_equiv [unfold 4] (X : Type)
    (H : Π⦃A : ℕ → Type⦄ (f : seq_diagram A),
      seq_colim (seq_diagram_arrow_left f X) ≃ (X → seq_colim f))
    (p : Π⦃A : ℕ → Type⦄ (f : seq_diagram A) {n : ℕ} (g : X → A n) (x : X),
      H f (ι _ g) x = ι _ (g x))
    (q : Π⦃A : ℕ → Type⦄ (f : seq_diagram A) {n : ℕ} (g : X → A n) (x : X),
      square (p f (@f n ∘ g) x) (p f g x) (ap (λg, H f g x)
             (glue (seq_diagram_arrow_left f X) g)) (glue f (g x)))
    : omega_compact X :=
  λA f, is_equiv_of_equiv_of_homotopy (H f)
  begin
    intro g, apply eq_of_homotopy, intro x,
    induction g with n g n g,
    { exact p f g x },
    { apply eq_pathover, refine _ ⬝hp !elim_glue⁻¹, exact q f g x }
  end

  local attribute is_contr_seq_colim [instance]
  definition is_contr_empty_arrow [instance] (X : Type) : is_contr (empty → X) :=
  by apply is_trunc_pi; contradiction

  definition omega_compact_empty [instance] [constructor] : omega_compact empty :=
  begin
    intro A f,
    fapply adjointify,
    { intro g, exact ι' _ 0 empty.elim},
    { intro g, apply eq_of_homotopy, contradiction},
    { intro h, apply is_prop.elim}
  end

  definition omega_compact_unit' [instance] [constructor] : omega_compact unit :=
  begin
    intro A f,
    fapply adjointify,
    { intro g, induction g ⋆,
      { exact ι _ (λx, a)},
      { apply glue}},
    { intro g, apply eq_of_homotopy, intro u, induction u,
      induction g ⋆,
      { reflexivity},
      { esimp, apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose (λx, arrow_colim_of_colim_arrow f x ⋆) _ _ ⬝ _,
        refine ap02 _ !elim_glue ⬝ _, apply elim_glue}},
    { intro h, induction h with n h n h,
      { esimp, apply ap (ι' _ n), apply unit_arrow_eq},
      { esimp, apply eq_pathover_id_right,
        refine ap_compose' (seq_colim.elim _ _ _) _ _ ⬝ph _,
        refine ap02 _ !elim_glue ⬝ph _,
        refine !elim_glue ⬝ph _,
        refine _ ⬝pv natural_square_tr (@glue _ (seq_diagram_arrow_left f unit) n) (unit_arrow_eq h),
        refine _ ⬝ (ap_compose (ι' _ _) _ _)⁻¹,
        apply ap02, unfold [seq_diagram_arrow_left],
        apply unit_arrow_eq_compose}}
  end

  -- The following is a start of a different proof that unit is omega-compact,
  -- which proves first that the types are equivalent
  definition omega_compact_unit [instance] [constructor] : omega_compact unit :=
  begin
    fapply omega_compact_of_equiv,
    { intro A f, refine _ ⬝e !arrow_unit_left⁻¹ᵉ, fapply seq_colim_equiv,
      { intro n, apply arrow_unit_left },
      intro n f, reflexivity },
    { intros, induction x, reflexivity },
    { intros, induction x, esimp, apply hdeg_square, exact !elim_glue ⬝ !idp_con },
  end

  local attribute equiv_of_omega_compact [constructor]
  definition omega_compact_prod [instance] [constructor] {X Y : Type} [omega_compact.{_ u} X]
    [omega_compact.{u u} Y] : omega_compact.{_ u} (X × Y) :=
  begin
    fapply omega_compact_of_equiv,
    { intro A f,
      exact calc
        seq_colim (seq_diagram_arrow_left f (X × Y))
              ≃ seq_colim (seq_diagram_arrow_left (seq_diagram_arrow_left f Y) X) :
                  begin
                    apply seq_colim_equiv (λn, !imp_imp_equiv_prod_imp⁻¹ᵉ),
                    intro n f, reflexivity
                  end
          ... ≃ (X → seq_colim (seq_diagram_arrow_left f Y))  : !equiv_of_omega_compact
          ... ≃ (X → Y → seq_colim f) : arrow_equiv_arrow_right _ !equiv_of_omega_compact
          ... ≃ (X × Y → seq_colim f) : imp_imp_equiv_prod_imp },
    { intros, induction x with x y, reflexivity },
    { intros, induction x with x y, apply hdeg_square,
      refine ap_compose (λz, arrow_colim_of_colim_arrow f z y) _ _ ⬝ _,
      refine ap02 _ (ap_compose (λz, arrow_colim_of_colim_arrow _ z x) _ _) ⬝ _,
      refine ap02 _ (ap02 _ !elim_glue) ⬝ _, refine ap02 _ (ap02 _ !idp_con) ⬝ _, esimp,
      refine ap02 _ !elim_glue ⬝ _, apply elim_glue }
  end

definition not_omega_compact_nat : ¬(omega_compact.{0 0} ℕ) :=
assume H,
let e := equiv_of_omega_compact ℕ seq_diagram_fin ⬝e
         arrow_equiv_arrow_right _ seq_colim_fin_equiv in
begin
--  check_expr e,
  have Πx, ∥ Σn, Πm, e x m < n ∥,
  begin
    intro f, induction f using seq_colim.rec_prop with n f,
    refine tr ⟨n, _⟩, intro m, exact is_lt (f m)
  end,
  induction this (e⁻¹ᵉ id) with x, induction x with n H2,
  apply lt.irrefl n,
  refine lt_of_le_of_lt (le_of_eq _) (H2 n),
  exact ap10 (right_inv e id)⁻¹ n
end

exit
  print seq_diagram_over
  definition seq_colim_over_equiv {X : Type} {A : X → ℕ → Type} (g : Π⦃x n⦄, A x n → A x (succ n))
    (x : X)
    : @seq_colim_over _ (constant_seq X) _ _ ≃ seq_colim (@g x) :=
  begin

  end

  definition seq_colim_pi_equiv {X : Type} {A : X → ℕ → Type} (g : Π⦃x n⦄, A x n → A x (succ n))
    [omega_compact X] : (Πx, seq_colim (@g x)) ≃ seq_colim (seq_diagram_pi g) :=
  -- calc
--    (Πx, seq_colim (@g x)) ≃ Πx, seq_colim (@g x)
  begin
    refine !pi_equiv_arrow_sigma ⬝e _,
    refine sigma_equiv_sigma_left (arrow_equiv_arrow_right X (sigma_equiv_sigma_left (seq_colim_constant_seq X)⁻¹ᵉ)) ⬝e _,
    exact sigma_equiv_sigma_left (arrow_equiv_arrow_right X _) ⬝e _,
  end

  set_option pp.universes true
  print seq_diagram_arrow_left

end seq_colim
