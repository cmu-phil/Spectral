/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Reduced cohomology
-/

import .EM

open spectrum int trunc pointed EM group algebra circle sphere

definition cohomology [reducible] (X : Type*) (Y : spectrum) (n : ℤ) : Set :=
ttrunc 0 (X →* Ω[2] (Y (n+2)))

definition ordinary_cohomology [reducible] (X : Type*) (G : CommGroup) (n : ℤ) : Set :=
cohomology X (EM_spectrum G) n

definition ordinary_cohomology_Z [reducible] (X : Type*) (n : ℤ) : Set :=
ordinary_cohomology X agℤ n

notation `H^` n `[`:0 X:0 `, ` Y:0 `]`:0 := cohomology X Y n
notation `H^` n `[`:0 X:0 `]`:0 := ordinary_cohomology_Z X n

check H^3[S¹*,EM_spectrum agℤ]
check H^3[S¹*]
