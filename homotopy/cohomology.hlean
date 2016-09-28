/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Reduced cohomology
-/

import .EM algebra.arrow_group

open eq spectrum int trunc pointed EM group algebra circle sphere nat

definition cohomology (X : Type*) (Y : spectrum) (n : ℤ) : CommGroup :=
CommGroup_pmap X (πag[2] (Y (2+n)))

definition ordinary_cohomology [reducible] (X : Type*) (G : CommGroup) (n : ℤ) : CommGroup :=
cohomology X (EM_spectrum G) n

definition ordinary_cohomology_Z [reducible] (X : Type*) (n : ℤ) : CommGroup :=
ordinary_cohomology X agℤ n

notation `H^` n `[`:0 X:0 `, ` Y:0 `]`:0 := cohomology X Y n
notation `H^` n `[`:0 X:0 `]`:0 := ordinary_cohomology_Z X n

check H^3[S¹*,EM_spectrum agℤ]
check H^3[S¹*]

definition unpointed_cohomology (X : Type) (Y : spectrum) (n : ℤ) : CommGroup :=
cohomology X₊ Y n

definition cohomology_homomorphism [constructor] {X X' : Type*} (f : X' →* X) (Y : spectrum)
  (n : ℤ) : cohomology X Y n →g cohomology X' Y n :=
Group_pmap_homomorphism f (πag[2] (Y (2+n)))

definition cohomology_homomorphism_id (X : Type*) (Y : spectrum) (n : ℤ) (f : H^n[X, Y]) :
  cohomology_homomorphism (pid X) Y n f ~* f :=
!pcompose_pid

definition cohomology_homomorphism_compose {X X' X'' : Type*} (g : X'' →* X') (f : X' →* X)
  (Y : spectrum) (n : ℤ) (h : H^n[X, Y]) : cohomology_homomorphism (f ∘* g) Y n h ~*
  cohomology_homomorphism g Y n (cohomology_homomorphism f Y n h) :=
!passoc⁻¹*
