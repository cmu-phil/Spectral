/-
Copyright (c) 2016 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

Exact couple, derived couples, and so on
-/

import algebra.group_theory hit.set_quotient types.sigma types.list types.sum .quotient_group .subgroup

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function group trunc
     equiv is_equiv

structure is_exact {A B C : AbGroup} (f : A →g B) (g : B →g C) :=
  ( im_in_ker : Π(a:A), g (f a) = 1)
  ( ker_in_im : Π(b:B), (g b = 1) → image_subgroup f b)

structure SES (A B C : AbGroup) :=
  ( f : A →g B)
  ( g : B →g C)
  ( Hf : is_embedding f)
  ( Hg : is_surjective g)
  ( ex : is_exact f g)

definition SES_of_inclusion {A B : AbGroup} (f : A →g B) (Hf : is_embedding f) : SES A B (quotient_ab_group (image_subgroup f)) := 
  begin
    have Hg : is_surjective (ab_qg_map (image_subgroup f)),
    from is_surjective_ab_qg_map (image_subgroup f),
    fapply SES.mk,
    exact f,
    exact ab_qg_map (image_subgroup f),
    exact Hf,
    exact Hg,
    fapply is_exact.mk,
    intro a,
    fapply qg_map_eq_one, fapply tr, fapply fiber.mk, exact a, reflexivity,
    intro b, intro p,
    fapply rel_of_ab_qg_map_eq_one, assumption
  end

definition SES_of_surjective_map {B C : AbGroup} (g : B →g C) (Hg : is_surjective g) : SES (ab_kernel g) B C :=
  begin
    fapply SES.mk,
    exact ab_kernel_incl g,
    exact g,
    exact is_embedding_ab_kernel_incl g,
    exact Hg,
    fapply is_exact.mk,
    intro a, induction a with a p, exact p,
    intro b p, fapply tr, fapply fiber.mk, fapply sigma.mk, exact b, exact p, reflexivity,
  end

structure hom_SES {A B C A' B' C' : AbGroup} (ses : SES A B C) (ses' : SES A' B' C') :=
  ( hA : A →g A')
  ( hB : B →g B')
  ( hC : C →g C')
  ( htpy1 : hB ∘g (SES.f ses) ~ (SES.f ses') ∘g hA)
  ( htpy2 : hC ∘g (SES.g ses) ~ (SES.g ses') ∘g hB)

--definition quotient_SES {A B C : AbGroup} (ses : SES A B C) : 
--  quotient_ab_group (image_subgroup (SES.f ses)) ≃g C :=
--  begin
--    fapply ab_group_first_iso_thm B C (SES.g ses), 
--  end

-- definition pre_right_extend_SES (to separate the following definition and replace C with B/A)

definition quotient_codomain_SES {A B C : AbGroup} (ses : SES A B C) : quotient_ab_group (kernel_subgroup (SES.g ses)) ≃g C :=
  begin
    exact (codomain_surjection_is_quotient (SES.g ses) (SES.Hg ses))
  end

definition quotient_triangle_SES {A B C : AbGroup} (ses : SES A B C) : (quotient_codomain_SES ses) ∘g (ab_qg_map (kernel_subgroup (SES.g ses))) ~ (SES.g ses) :=
  begin
    reflexivity
  end

section short_exact_sequences
  parameters {A B C A' B' C' : AbGroup} 
  (ses : SES A B C) (ses' : SES A' B' C')  
  (hA : A →g A') (hB : B →g B') (htpy1 : hB ∘g (SES.f ses) ~ (SES.f ses') ∘g hA)

  local abbreviation f := SES.f ses
  local abbreviation g := SES.g ses
  local abbreviation ex := SES.ex ses
  local abbreviation q := ab_qg_map (kernel_subgroup g)
  local abbreviation f' := SES.f ses'
  local abbreviation g' := SES.g ses'
  local abbreviation ex' := SES.ex ses'
  local abbreviation q' := ab_qg_map (kernel_subgroup g')
  local abbreviation α := quotient_codomain_SES ses
  local abbreviation α' := quotient_codomain_SES ses'
  
  include htpy1

  -- We define a group homomorphism B/ker(g) →g B'/ker(g'), keeping in mind that ker(g)=A and ker(g')=A'.
definition quotient_extend_SES : quotient_ab_group (kernel_subgroup g) →g quotient_ab_group (kernel_subgroup g') :=
  begin
    fapply ab_group_quotient_homomorphism B B' (kernel_subgroup g) (kernel_subgroup g') hB,
    intro b,
    intro K,
    have k : trunctype.carrier (image_subgroup f b), from is_exact.ker_in_im ex b K,
    induction k, induction a with a p,
    rewrite [p⁻¹],
    rewrite [htpy1 a],
    fapply is_exact.im_in_ker ex' (hA a)
  end

  local abbreviation k := quotient_extend_SES

definition quotient_extend_SES_square : k ∘g (ab_qg_map (kernel_subgroup g)) ~ (ab_qg_map (kernel_subgroup g')) ∘g hB :=
  begin
    fapply quotient_group_compute
  end

definition right_extend_SES  : C →g C' := 
  α' ∘g k ∘g α⁻¹ᵍ

local abbreviation hC := right_extend_SES

definition right_extend_hom_SES : hom_SES ses ses' :=
  begin
    fapply hom_SES.mk,
    exact hA,
    exact hB,
    exact hC,
    exact htpy1,
    exact calc
      hC ∘g g ~ hC ∘g α ∘g q              : by reflexivity
          ... ~ α' ∘g k ∘g α⁻¹ᵍ ∘g α ∘g q : by reflexivity
          ... ~ α' ∘g k ∘g q              : by exact hwhisker_left (α' ∘g k) (hwhisker_right q (left_inv α))
          ... ~ α' ∘g q' ∘g hB            : by exact hwhisker_left α' (quotient_extend_SES_square)
          ... ~ g' ∘g hB                  : by reflexivity
  end

end short_exact_sequences

definition is_differential {B : AbGroup} (d : B →g B) := Π(b:B), d (d b) = 1

definition image_subgroup_of_diff {B : AbGroup} (d : B →g B) (H : is_differential d) : subgroup_rel (ab_kernel d) :=
  subgroup_rel_of_subgroup (image_subgroup d) (kernel_subgroup d)
  begin
    intro g p,
    induction p with f, induction f with h p,
    rewrite [p⁻¹],
    esimp,
    exact H h
  end

definition homology {B : AbGroup} (d : B →g B) (H : is_differential d) : AbGroup :=
  @quotient_ab_group (ab_kernel d) (image_subgroup_of_diff d H)

structure exact_couple (A B : AbGroup) : Type :=
  ( i : A →g A) (j : A →g B) (k : B →g A)
  ( exact_ij : is_exact i j)
  ( exact_jk : is_exact j k)
  ( exact_ki : is_exact k i)

definition differential {A B : AbGroup} (EC : exact_couple A B) : B →g B :=
  (exact_couple.j EC) ∘g (exact_couple.k EC)

definition differential_is_differential {A B : AbGroup} (EC : exact_couple A B) : is_differential (differential EC) :=
  begin
    induction EC,
    induction exact_jk,
    intro b,
    exact (ap (group_fun j) (im_in_ker (group_fun k b))) ⬝ (respect_one j)
  end

section derived_couple

  variables {A B : AbGroup} (EC : exact_couple A B)

definition derived_couple_A : AbGroup :=
  ab_subgroup (image_subgroup (exact_couple.i EC))

definition derived_couple_B : AbGroup :=
  homology (differential EC) (differential_is_differential EC)

definition derived_couple_i : derived_couple_A EC →g derived_couple_A EC :=
  (image_lift (exact_couple.i EC)) ∘g (image_incl (exact_couple.i EC))

definition derived_couple_j : derived_couple_A EC →g derived_couple_B EC :=
  begin
  exact sorry,
--    refine (comm_gq_map (comm_kernel (boundary CC)) (image_subgroup_of_bd (boundary CC) (boundary_is_boundary CC))) ∘g _,
  end

end derived_couple
