/-
Copyright (c) 2016 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

Exact couple, derived couples, and so on
-/

import algebra.group_theory hit.set_quotient types.sigma types.list types.sum

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function group
     equiv

definition kernel.{l1} {A B : CommGroup.{l1}} (f : A →g B) : CommGroup.{l1} :=
  begin
    fapply CommGroup.mk,
    { exact fiber f 1},
    fapply comm_group.mk,
    { intro x, induction x with a p, intro y, induction y with b q, fapply fiber.mk, exact a*b, rewrite respect_mul, rewrite p, rewrite q, apply mul_one},
    { exact sorry },
    { intros x y z, induction x with a p, induction y with b q, induction z with c r, esimp, exact sorry }, repeat exact sorry
  end

structure is_exact {A B C : CommGroup} (f : A →g B) (g : B →g C) :=
  ( im_in_ker : Π(a:A), g (f a) = 1)
  ( ker_in_im : Π(b:B), (g b = 1) → Σ(a:A), f a = b)  

definition isBoundary {B : CommGroup} (d : B →g B) := Π(b:B), d b = 1

-- definition homology {B : CommGroup} (d : B →g B) (H : isBoundary d) := 
--   quotient_group (kernel d) (image d)

structure exact_couple (A B : CommGroup) : Type :=
  ( i : A →g A) (j : A →g B) (k : B →g A)
  ( exact_ij : is_exact i j)
  ( exact_jk : is_exact j k)
  ( exact_ki : is_exact k i)

definition boundary {A B : CommGroup} (CC : exact_couple A B) : B →g B := (exact_couple.j CC) ∘g (exact_couple.k CC)



