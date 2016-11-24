/-
Copyright (c) 2016 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

Exact couple, derived couples, and so on
-/

import algebra.group_theory hit.set_quotient types.sigma types.list types.sum .quotient_group .subgroup

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function group trunc
     equiv

structure is_exact {A B C : AbGroup} (f : A →g B) (g : B →g C) :=
  ( im_in_ker : Π(a:A), g (f a) = 1)
  ( ker_in_im : Π(b:B), (g b = 1) → ∃(a:A), f a = b)

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
