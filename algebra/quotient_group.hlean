/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import hit.set_quotient .subgroup

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod trunc function equiv

namespace group

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : CommGroup}

  /- Quotient Group -/

  definition homotopy_of_homomorphism_eq {f g : G →g G'}(p : f = g) : f ~ g :=
  λx : G , ap010 group_fun p x

  definition quotient_rel (g h : G) : Prop := N (g * h⁻¹)

  variable {N}

    -- We prove that quotient_rel is an equivalence relation
  theorem quotient_rel_refl (g : G) : quotient_rel N g g :=
  transport (λx, N x) !mul.right_inv⁻¹ (subgroup_has_one N)

  theorem quotient_rel_symm (r : quotient_rel N g h) : quotient_rel N h g :=
  transport (λx, N x) (!mul_inv ⬝ ap (λx, x * _) !inv_inv) (subgroup_respect_inv N r)

  theorem quotient_rel_trans (r : quotient_rel N g h) (s : quotient_rel N h k)
    : quotient_rel N g k :=
  have H1 : N ((g * h⁻¹) * (h * k⁻¹)), from subgroup_respect_mul N r s,
  have H2 : (g * h⁻¹) * (h * k⁻¹) = g * k⁻¹, from calc
    (g * h⁻¹) * (h * k⁻¹) = ((g * h⁻¹) * h) * k⁻¹ : by rewrite [mul.assoc (g * h⁻¹)]
                      ... = g * k⁻¹               : by rewrite inv_mul_cancel_right,
  show N (g * k⁻¹), from H2 ▸ H1

  theorem is_equivalence_quotient_rel : is_equivalence (quotient_rel N) :=
  is_equivalence.mk quotient_rel_refl
                    (λg h, quotient_rel_symm)
                    (λg h k, quotient_rel_trans)

    -- We prove that quotient_rel respects inverses and multiplication, so
    -- it is a congruence relation
  theorem quotient_rel_resp_inv (r : quotient_rel N g h) : quotient_rel N g⁻¹ h⁻¹ :=
  have H1 : N (g⁻¹ * (h * g⁻¹) * g), from
    is_normal_subgroup' N g (quotient_rel_symm r),
  have H2 : g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h⁻¹⁻¹, from calc
    g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h * g⁻¹ * g : by rewrite -mul.assoc
                    ... = g⁻¹ * h           : inv_mul_cancel_right
                    ... = g⁻¹ * h⁻¹⁻¹       : by rewrite algebra.inv_inv,
  show N (g⁻¹ * h⁻¹⁻¹), from H2 ▸ H1

  theorem quotient_rel_resp_mul (r : quotient_rel N g h) (r' : quotient_rel N g' h')
    : quotient_rel N (g * g') (h * h') :=
  have H1 : N (g * ((g' * h'⁻¹) * h⁻¹)), from
    normal_subgroup_insert N r' r,
  have H2 : g * ((g' * h'⁻¹) * h⁻¹) = (g * g') * (h * h')⁻¹, from calc
    g * ((g' * h'⁻¹) * h⁻¹) = g * (g' * (h'⁻¹ * h⁻¹)) : by rewrite [mul.assoc]
                        ... = (g * g') * (h'⁻¹ * h⁻¹) : mul.assoc
                        ... = (g * g') * (h * h')⁻¹ : by rewrite [mul_inv],
  show N ((g * g') * (h * h')⁻¹), from transport (λx, N x) H2 H1

  local attribute is_equivalence_quotient_rel [instance]

  variable (N)

  definition qg : Type := set_quotient (quotient_rel N)

  variable {N}

  local attribute qg [reducible]

  definition quotient_one [constructor] : qg N := class_of one
  definition quotient_inv [unfold 3] : qg N → qg N :=
  quotient_unary_map has_inv.inv (λg g' r, quotient_rel_resp_inv r)
  definition quotient_mul [unfold 3 4] : qg N → qg N → qg N :=
  quotient_binary_map has_mul.mul (λg g' r h h' r', quotient_rel_resp_mul r r')

  section
  local notation 1 := quotient_one
  local postfix ⁻¹ := quotient_inv
  local infix * := quotient_mul

  theorem quotient_mul_assoc (g₁ g₂ g₃ : qg N) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    refine set_quotient.rec_prop _ g₁,
    refine set_quotient.rec_prop _ g₂,
    refine set_quotient.rec_prop _ g₃,
    clear g₁ g₂ g₃, intro g₁ g₂ g₃,
    exact ap class_of !mul.assoc
  end

  theorem quotient_one_mul (g : qg N) : 1 * g = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !one_mul
  end

  theorem quotient_mul_one (g : qg N) : g * 1 = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !mul_one
  end

  theorem quotient_mul_left_inv (g : qg N) : g⁻¹ * g = 1 :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !mul.left_inv
  end

  theorem quotient_mul_comm {G : CommGroup} {N : normal_subgroup_rel G} (g h : qg N)
    : g * h = h * g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    refine set_quotient.rec_prop _ h, clear h, intro h,
    apply ap class_of, esimp, apply mul.comm
  end

  end

  variable (N)
  definition group_qg [constructor] : group (qg N) :=
  group.mk quotient_mul _ quotient_mul_assoc quotient_one quotient_one_mul quotient_mul_one
           quotient_inv quotient_mul_left_inv

  definition quotient_group [constructor] : Group :=
  Group.mk _ (group_qg N)

  definition comm_group_qg [constructor] {G : CommGroup} (N : normal_subgroup_rel G)
    : comm_group (qg N) :=
  ⦃comm_group, group_qg N, mul_comm := quotient_mul_comm⦄

  definition quotient_comm_group [constructor] {G : CommGroup} (N : subgroup_rel G)
    : CommGroup :=
  CommGroup.mk _ (comm_group_qg (normal_subgroup_rel_comm N))

  definition gq_map : G →g quotient_group N :=
  homomorphism.mk class_of (λ g h, idp)

  definition comm_gq_map {G : CommGroup} (N : subgroup_rel G) : G →g quotient_comm_group N :=
  begin
    fapply homomorphism.mk,
    exact class_of,
    exact λ g h, idp
  end

  namespace quotient
    notation `⟦`:max a `⟧`:0 := gq_map a _
  end quotient

  open quotient
  variable {N}

  definition gq_map_eq_one (g : G) (H : N g) : gq_map N g = 1 :=
  begin
    apply eq_of_rel,
      have e : (g * 1⁻¹ = g),
      from calc
      g * 1⁻¹ = g * 1 : one_inv
        ...   = g : mul_one,
    unfold quotient_rel, rewrite e, exact H
  end

  definition rel_of_gq_map_eq_one (g : G) (H : gq_map N g = 1) : N g :=
  begin
    have e : (g * 1⁻¹ = g),
    from calc
      g * 1⁻¹ = g * 1 : one_inv
        ...   = g : mul_one,
    rewrite (inverse e),
    apply rel_of_eq _ H
  end

  definition quotient_group_elim (f : G →g G') (H : Π⦃g⦄, N g → f g = 1) : quotient_group N →g G' :=
  begin
    fapply homomorphism.mk,
      -- define function
    { apply set_quotient.elim f,
      intro g h K,
      apply eq_of_mul_inv_eq_one,
      have e : f (g * h⁻¹) = f g * (f h)⁻¹,
      from calc
        f (g * h⁻¹) = f g * (f h⁻¹) : to_respect_mul
               ...  = f g * (f h)⁻¹ : to_respect_inv,
      rewrite (inverse e),
      apply H, exact K},
    { intro g h, induction g using set_quotient.rec_prop with g,
      induction h using set_quotient.rec_prop with h,
      krewrite (inverse (to_respect_mul (gq_map N) g h)),
      unfold gq_map, esimp, exact to_respect_mul f g h }
  end

  definition quotient_group_compute (f : G →g G') (H : Π⦃g⦄, N g → f g = 1) : quotient_group_elim f H ∘g gq_map N ~ f :=
  begin
    intro g, reflexivity
  end

  definition gelim_unique (f : G →g G') (H : Π⦃g⦄, N g → f g = 1) (k : quotient_group N →g G')
    : ( k ∘g gq_map N ~ f ) → k ~ quotient_group_elim f H :=
  begin
    intro K cg, induction cg using set_quotient.rec_prop with g,
    krewrite (quotient_group_compute f),
    exact K g
  end

  definition gq_universal_property (f : G →g G') (H : Π⦃g⦄, N g → f g = 1)  :
    is_contr (Σ(g : quotient_group N →g G'), g ∘g gq_map N = f) :=
  begin
    fapply is_contr.mk,
      -- give center of contraction
    { fapply sigma.mk, exact quotient_group_elim f H, apply homomorphism_eq, exact quotient_group_compute f H },
      -- give contraction
    { intro pair, induction pair with g p, fapply sigma_eq, 
      {esimp, apply homomorphism_eq, symmetry, exact gelim_unique f H g (homotopy_of_homomorphism_eq p)},
      {fapply is_prop.elimo} }
  end

definition comm_group_quotient_homomorphism (A B : CommGroup)(K : subgroup_rel A)(L : subgroup_rel B) (f : A →g B)
     (p : Π(a:A), K(a) → L(f a)) : quotient_comm_group K →g quotient_comm_group L :=
    begin
    fapply quotient_group_elim,
    exact (comm_gq_map L) ∘g f,
    
-- homomorphism.mk,
  

    end

    /- set generating normal subgroup -/

  section

    parameters {GG : CommGroup} (S : GG → Prop)

    inductive generating_relation' : GG → Type :=
    | rincl : Π{g}, S g → generating_relation' g
    | rmul  : Π{g h}, generating_relation' g → generating_relation' h → generating_relation' (g * h)
    | rinv  : Π{g}, generating_relation' g → generating_relation' g⁻¹
    | rone  : generating_relation' 1
    open generating_relation'
    definition generating_relation (g : GG) : Prop := ∥ generating_relation' g ∥
    local abbreviation R := generating_relation
    definition gr_one : R 1 := tr (rone S)
    definition gr_inv (g : GG) : R g → R g⁻¹ :=
    trunc_functor -1 rinv
    definition gr_mul (g h : GG) : R g → R h → R (g * h) :=
    trunc_functor2 rmul

    definition normal_generating_relation : subgroup_rel GG :=
    ⦃ subgroup_rel,
      R := generating_relation,
      Rone := gr_one,
      Rinv := gr_inv,
      Rmul := gr_mul⦄

    parameter (GG)
    definition quotient_comm_group_gen : CommGroup := quotient_comm_group normal_generating_relation

  end

  end group
