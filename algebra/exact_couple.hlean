/-
Copyright (c) 2016 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

Exact couple, derived couples, and so on
-/

import algebra.group_theory hit.set_quotient types.sigma types.list types.sum .quotient_group .subgroup

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function group trunc
     equiv

structure is_exact {A B C : CommGroup} (f : A →g B) (g : B →g C) :=
  ( im_in_ker : Π(a:A), g (f a) = 1)
  ( ker_in_im : Π(b:B), (g b = 1) → ∃(a:A), f a = b)  

definition is_boundary {B : CommGroup} (d : B →g B) := Π(b:B), d (d b) = 1

definition image_subgroup_of_bd {B : CommGroup} (d : B →g B) (H : is_boundary d) : subgroup_rel (comm_kernel d) :=
  subgroup_rel_of_subgroup (image_subgroup d) (kernel_subgroup d)
  begin
    intro g p, 
    induction p with f, induction f with h p,
    rewrite [p⁻¹], 
    esimp,
    exact H h 
  end

definition homology {B : CommGroup} (d : B →g B) (H : is_boundary d) : CommGroup := 
  @quotient_comm_group (comm_kernel d) (image_subgroup_of_bd d H)

structure exact_couple (A B : CommGroup) : Type :=
  ( i : A →g A) (j : A →g B) (k : B →g A)
  ( exact_ij : is_exact i j)
  ( exact_jk : is_exact j k)
  ( exact_ki : is_exact k i)

definition boundary {A B : CommGroup} (CC : exact_couple A B) : B →g B := 
  (exact_couple.j CC) ∘g (exact_couple.k CC)

definition boundary_is_boundary {A B : CommGroup} (CC : exact_couple A B) : is_boundary (boundary CC) :=
  begin
    induction CC, 
    induction exact_jk, 
    intro b,
    exact (ap (group_fun j) (im_in_ker (group_fun k b))) ⬝ (respect_one j)
  end

section derived_couple

  variables {A B : CommGroup} (CC : exact_couple A B) 

definition derived_couple_A : CommGroup :=
  comm_subgroup (image_subgroup (exact_couple.i CC))

definition derived_couple_B : CommGroup :=
  homology (boundary CC) (boundary_is_boundary CC)

definition derived_couple_i : derived_couple_A CC →g derived_couple_A CC :=
  (image_lift (exact_couple.i CC)) ∘g (image_incl (exact_couple.i CC))

definition derived_couple_j : derived_couple_A CC →g derived_couple_B CC :=
  begin
--    refine (comm_gq_map (comm_kernel (boundary CC)) (image_subgroup_of_bd (boundary CC) (boundary_is_boundary CC))) ∘g _,
  exact sorry
  end

end derived_couple
