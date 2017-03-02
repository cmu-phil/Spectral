/-
Copyright (c) 2017 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

Basic facts about short exact sequences. 

At the moment, it only covers short exact sequences of abelian groups, but this should be extended to short exact sequences in any abelian category.
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

definition SES_of_subgroup {B : AbGroup} (S : subgroup_rel B) : SES (ab_subgroup S) B (quotient_ab_group S) :=
  begin
    fapply SES.mk,
    exact incl_of_subgroup S,
    exact ab_qg_map S,
    exact is_embedding_incl_of_subgroup S,
    exact is_surjective_ab_qg_map S,
    fapply is_exact.mk,
    intro a, fapply ab_qg_map_eq_one, induction a with b p, exact p,
    intro b p, fapply tr, fapply fiber.mk, fapply sigma.mk b, fapply rel_of_ab_qg_map_eq_one, exact p, reflexivity,
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

section ses
parameters {A B C : AbGroup} (ses : SES A B C)

  local abbreviation f := SES.f ses
  local notation `g` := SES.g ses
  local abbreviation ex := SES.ex ses
  local abbreviation q := ab_qg_map (kernel_subgroup g)
  local abbreviation B_mod_A := quotient_ab_group (kernel_subgroup g)

--definition quotient_SES {A B C : AbGroup} (ses : SES A B C) : 
--  quotient_ab_group (image_subgroup (SES.f ses)) ≃g C :=
--  begin
--    fapply ab_group_first_iso_thm B C (SES.g ses), 
--  end

-- definition pre_right_extend_SES (to separate the following definition and replace C with B/A)

definition quotient_codomain_SES : B_mod_A ≃g C :=
  begin
    exact (codomain_surjection_is_quotient g (SES.Hg ses))
  end

  local abbreviation α := quotient_codomain_SES

definition quotient_triangle_SES : α ∘g q ~ g :=
  begin
    reflexivity
  end

definition quotient_triangle_extend_SES {C': AbGroup} (k : B →g C') :
  (Σ (h : C →g C'), h ∘g g ~ k) ≃ (Σ (h' : B_mod_A →g C'), h' ∘g q ~ k) :=
  begin
    fapply equiv.mk,
    intro pair, induction pair with h H, 
    fapply sigma.mk, exact h ∘g α, intro b,
    exact H b,
    fapply adjointify,
    intro pair, induction pair with h' H', fapply sigma.mk,
    exact h' ∘g α⁻¹ᵍ,
    intro b,
    exact calc
      h' (α⁻¹ᵍ (g b)) = h' (α⁻¹ᵍ (α (q b))) : by reflexivity
                  ... = h' (q b) : by exact hwhisker_left h' (left_inv α) (q b)
                  ... = k b : by exact H' b,
    intro pair, induction pair with h' H', fapply sigma_eq, esimp, fapply homomorphism_eq, fapply hwhisker_left h' (left_inv α),    esimp, fapply is_prop.elimo, fapply pi.is_trunc_pi, intro a, fapply is_trunc_eq,
    intro pair, induction pair with h H, fapply sigma_eq, esimp, fapply homomorphism_eq, fapply hwhisker_left h (right_inv α),
    esimp, fapply is_prop.elimo, fapply pi.is_trunc_pi, intro a, fapply is_trunc_eq,
  end

  parameters {A' B' C' : AbGroup} 
  (ses' : SES A' B' C')  
  (hA : A →g A') (hB : B →g B') (htpy1 : hB ∘g f ~ (SES.f ses') ∘g hA)

  local abbreviation f' := SES.f ses'
  local notation `g'` := SES.g ses'
  local abbreviation ex' := SES.ex ses'
  local abbreviation q' := ab_qg_map (kernel_subgroup g')
  local abbreviation α' := quotient_codomain_SES
  
  include htpy1

  definition quotient_extend_unique_SES : is_contr (Σ (hC : C →g C'), hC ∘g g ~ g' ∘g hB) := 
  begin
    fapply @(is_trunc_equiv_closed_rev _ (quotient_triangle_extend_SES (g' ∘g hB))), 
    fapply ab_qg_universal_property,
    intro b, intro K,
    have k : trunctype.carrier (image_subgroup f b), from is_exact.ker_in_im ex b K,
    induction k, induction a with a p,
    induction p,
    refine (ap g' (htpy1 a)) ⬝ _,
    fapply is_exact.im_in_ker ex' (hA a)
  end

/-
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

definition right_extend_SES_square : hC ∘g g ~ g' ∘ hB :=
  begin
    exact calc
      hC ∘g g ~ hC ∘g α ∘g q              : by reflexivity
          ... ~ α' ∘g k ∘g α⁻¹ᵍ ∘g α ∘g q : by reflexivity
          ... ~ α' ∘g k ∘g q              : by exact hwhisker_left (α' ∘g k) (hwhisker_right q (left_inv α))
          ... ~ α' ∘g q' ∘g hB            : by exact hwhisker_left α' (quotient_extend_SES_square)
          ... ~ g' ∘g hB                  : by reflexivity
  end

local abbreviation htpy2 := right_extend_SES_square

definition right_extend_SES_unique_map_aux (hC' : C →g C') (htpy2' : g' ∘g hB ~ hC' ∘g g) : k ∘g q ~  α'⁻¹ᵍ ∘g hC' ∘g α ∘g q :=
  begin
    exact calc
      k ∘g q ~ q' ∘g hB                : by reflexivity
      ... ~ α'⁻¹ᵍ ∘g α' ∘g q' ∘g hB    : by exact hwhisker_right (q' ∘g hB) (homotopy.symm (left_inv α'))
      ... ~ α'⁻¹ᵍ ∘g g' ∘g hB          : by reflexivity
      ... ~ α'⁻¹ᵍ ∘g hC' ∘g g          : by exact hwhisker_left (α'⁻¹ᵍ) htpy2'
      ... ~ α'⁻¹ᵍ ∘g hC' ∘g α ∘g q     : by reflexivity
  end

definition right_extend_SES_unique_map (hC' : C →g C') (htpy2' : hC' ∘g g ~ g' ∘g hB) : hC ~ hC' :=
  begin
    exact calc
      hC ~ α' ∘g k ∘g α⁻¹ᵍ : by reflexivity
     ... ~ α' ∘g α'⁻¹ᵍ ∘g hC' ∘g α ∘g α⁻¹ᵍ : 
     ... ~ hC' ∘g α ∘g α⁻¹ᵍ : _
     ... ~ hC' : _
  end

definition right_extend_hom_SES : hom_SES ses ses' :=
  begin
    fapply hom_SES.mk,
    exact hA,
    exact hB,
    exact hC,
    exact htpy1,
    exact htpy2
  end
-/

end ses
