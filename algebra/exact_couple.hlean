/-
Copyright (c) 2016 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke, Steve Awodey

Exact couple, derived couples, and so on
-/

import algebra.group_theory hit.set_quotient types.sigma types.list types.sum .quotient_group .subgroup .ses

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function group trunc
     equiv is_equiv

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

definition diff_im_in_ker {B : AbGroup} (d : B →g B) (H : is_differential d) : Π(b : B), image_subgroup d b → kernel_subgroup d b :=
  begin
    intro b p,
    induction p with q, induction q with b' p, induction p, exact H b'
  end

definition homology {B : AbGroup} (d : B →g B) (H : is_differential d) : AbGroup :=
  @quotient_ab_group (ab_kernel d) (image_subgroup_of_diff d H)

definition homology_ugly {B : AbGroup} (d : B →g B) (H : is_differential d) : AbGroup :=
  @quotient_ab_group (ab_kernel d) (image_subgroup (ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)))


definition homology_iso_ugly {B : AbGroup} (d : B →g B) (H : is_differential d) : (homology d H) ≃g (homology_ugly d H) :=
  begin
  fapply @iso_of_ab_qg_group (ab_kernel d),
  intro a,
  intro p, induction p with f, induction f with b p,
  fapply tr, fapply fiber.mk, fapply sigma.mk, exact d b, fapply tr, fapply fiber.mk, exact b, reflexivity,
  induction a with c q, fapply subtype_eq, refine p ⬝ _, reflexivity,
  intro b p, induction p with f, induction f with c p, induction p,
  induction c with a q, induction q with f, induction f with a' p, induction p,
  fapply tr, fapply fiber.mk, exact a', reflexivity
  end


definition SES_iso_C {A B C C' : AbGroup} (ses : SES A B C) (k : C ≃g C') : SES A B C' :=
  begin
  fapply SES.mk,
  exact SES.f ses,
  exact k ∘g SES.g ses,
  exact SES.Hf ses,
  fapply @is_surjective_compose _ _ _ k (SES.g ses),
  exact is_surjective_of_is_equiv k,
  exact SES.Hg ses,
  fapply is_exact.mk,
  intro a,
  esimp,
  note h := SES.ex ses,
  note h2 := is_exact.im_in_ker h a,
  refine ap k h2 ⬝ _ ,
  exact to_respect_one k,
  intro b,
  intro k3,
  note h := SES.ex ses,
  note h3 := is_exact.ker_in_im h b,
  fapply is_exact.ker_in_im h,
  refine  _ ⬝ ap k⁻¹ᵍ k3 ⬝ _ ,
  esimp,
  exact (to_left_inv (equiv_of_isomorphism k) ((SES.g ses) b))⁻¹,
  exact to_respect_one k⁻¹ᵍ
  end


definition SES_of_differential_ugly {B : AbGroup} (d : B →g B) (H : is_differential d) : SES (ab_image d) (ab_kernel d) (homology_ugly d H) :=
  begin
    exact SES_of_inclusion (ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)) (is_embedding_ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)),
   end

definition SES_of_differential {B : AbGroup} (d : B →g B) (H : is_differential d) : SES (ab_image d) (ab_kernel d) (homology d H) :=
  begin
    fapply SES_iso_C,
    fapply SES_of_inclusion (ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)) (is_embedding_ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)),
    exact (homology_iso_ugly d H)⁻¹ᵍ
   end

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

/-
   A - i -> A
 k ^        |
   |        v j
   B ====== B
-/

  parameters {A B : AbGroup} (EC : exact_couple A B)
  local abbreviation i := exact_couple.i EC
  local abbreviation j := exact_couple.j EC
  local abbreviation k := exact_couple.k EC
  local abbreviation d := differential EC
  local abbreviation H := differential_is_differential EC
 -- local abbreviation u := exact_couple.i (SES_of_differential d H)

definition derived_couple_A : AbGroup :=
  ab_subgroup (image_subgroup i)

definition derived_couple_B : AbGroup :=
  homology (differential EC) (differential_is_differential EC)

definition derived_couple_i : derived_couple_A →g derived_couple_A :=
  (image_lift (exact_couple.i EC)) ∘g (image_incl (exact_couple.i EC))

definition SES_of_exact_couple_at_i : SES (ab_kernel i) A (ab_image i) :=
  begin
  fapply SES_iso_C,
  fapply SES_of_subgroup (kernel_subgroup i),
  fapply ab_group_first_iso_thm i,
  end

definition kj_zero (a : A) : k (j a) = 1 :=
is_exact.im_in_ker (exact_couple.exact_jk EC) a

definition j_factor : A →g (ab_kernel d) :=
begin
  fapply ab_hom_lift j,
  intro a,
  unfold kernel_subgroup,
  exact calc
    d (j a) = j (k (j a)) : rfl
       ...  = j 1 : by exact ap j (kj_zero a)
       ...  = 1   : to_respect_one,
end

definition subgroup_iso_exact_at_A : ab_kernel i ≃g ab_image k :=
  begin
  fapply ab_subgroup_iso,
  intro a,
  induction EC,
  induction exact_ki,
  exact ker_in_im a,
  intro a b, induction b with f, induction f with b p, induction p,
  induction EC,
  induction exact_ki,
  exact im_in_ker b,
  end

definition subgroup_iso_exact_at_A_triangle : ab_kernel_incl i ~ ab_image_incl k ∘g subgroup_iso_exact_at_A :=
  begin
    fapply ab_subgroup_iso_triangle,
    intro a b, induction b with f, induction f with b p, induction p,
    induction EC, induction exact_ki, exact im_in_ker b,
  end

definition subgroup_homom_ker_to_im : ab_kernel i →g ab_image d :=
  (image_homomorphism k j) ∘g subgroup_iso_exact_at_A

open eq

definition left_square_derived_ses_aux : j_factor ∘g ab_image_incl k ~ (SES.f (SES_of_differential d H)) ∘g (image_homomorphism k j) :=
  begin
    intro x,
    induction x with a p, induction p with f, induction f with b p, induction p, 
    fapply subtype_eq, 
    reflexivity,
  end

definition left_square_derived_ses : j_factor ∘g (ab_kernel_incl i) ~ (SES.f (SES_of_differential d H)) ∘g subgroup_homom_ker_to_im :=
  begin
    intro x,
    exact (ap j_factor (subgroup_iso_exact_at_A_triangle x)) ⬝ (left_square_derived_ses_aux (subgroup_iso_exact_at_A x)),
  end

print quotient_extend_unique_SES
check quotient_extend_unique_SES (SES_of_exact_couple_at_i) (SES_of_differential d H) (subgroup_homom_ker_to_im) (j_factor) (left_square_derived_ses)

definition derived_couple_j_unique :   
    is_contr (Σ hC, group_fun (hC ∘g SES.g SES_of_exact_couple_at_i) ~ group_fun
       (SES.g (SES_of_differential d H) ∘g j_factor)) :=
quotient_extend_unique_SES (SES_of_exact_couple_at_i) (SES_of_differential d H) (subgroup_homom_ker_to_im) (j_factor) (left_square_derived_ses)

definition derived_couple_j : derived_couple_A →g derived_couple_B :=
   begin
     exact pr1 (center' (derived_couple_j_unique)),
   end

definition derived_couple_j_htpy : group_fun (derived_couple_j ∘g SES.g SES_of_exact_couple_at_i) ~ group_fun
       (SES.g (SES_of_differential d H) ∘g j_factor) :=
   begin
     exact pr2 (center' (derived_couple_j_unique)),
   end

/-definition derived_couple_j : derived_couple_A EC →g derived_couple_B EC :=
  begin
  exact sorry,
--    refine (comm_gq_map (comm_kernel (boundary CC)) (image_subgroup_of_bd (boundary CC) (boundary_is_boundary CC))) ∘g _,
  end-/

end derived_couple
