/-
Copyright (c) 2017 Kuen-Bang Hou (Favonia).
Released under Apache 2.0 license as described in the file LICENSE.

Author: Kuen-Bang Hou (Favonia)
-/

import .basic .sphere ..homotopy.susp_product

open eq pointed group algebra circle sphere nat equiv susp
     function sphere homology int lift prod smash

namespace homology

section
  parameter (theory : ordinary_homology_theory)

  open ordinary_homology_theory

  theorem Hptorus : Π(n : ℤ)(m : ℕ), HH theory n (plift (sphere m ×* sphere m)) ≃g
    HH theory n (plift (sphere m)) ×g (HH theory n (plift (sphere m)) ×g HH theory n (plift (sphere (m + m)))) := λ n m,
    calc        HH theory n (plift (sphere m ×* sphere m))
             ≃g HH theory (n + 1) (plift (⅀ (sphere m ×* sphere m))) : by exact (Hplift_susp theory n (sphere m ×* sphere m))⁻¹ᵍ
         ... ≃g HH theory (n + 1) (plift (⅀ (sphere m) ∨ (⅀ (sphere m) ∨ ⅀ (sphere m ∧ sphere m))))
                   : by exact Hplift_isomorphism theory (n + 1) (susp_product (sphere m) (sphere m))
         ... ≃g HH theory (n + 1) (plift (⅀ (sphere m))) ×g HH theory (n + 1) (plift (⅀ (sphere m) ∨ (⅀ (sphere m ∧ sphere m))))
                   : by exact Hplift_wedge theory (n + 1) (⅀ (sphere m)) (⅀ (sphere m) ∨ (⅀ (sphere m ∧ sphere m)))
         ... ≃g HH theory n (plift (sphere m)) ×g (HH theory n (plift (sphere m)) ×g HH theory n (plift (sphere (m + m))))
                   : by exact product_isomorphism (Hplift_susp theory n (sphere m))
             (calc
                     HH theory (n + 1) (plift (⅀ (sphere m) ∨ (⅀ (sphere m ∧ sphere m))))
                  ≃g HH theory (n + 1) (plift (⅀ (sphere m))) ×g HH theory (n + 1) (plift (⅀ (sphere m ∧ sphere m)))
                     : by exact Hplift_wedge theory (n + 1) (⅀ (sphere m)) (⅀ (sphere m ∧ sphere m))
              ... ≃g HH theory n (plift (sphere m)) ×g HH theory n (plift (sphere (m + m)))
                     : by exact product_isomorphism (Hplift_susp theory n (sphere m))
                                  (Hplift_susp theory n (sphere m ∧ sphere m) ⬝g Hplift_isomorphism theory n (sphere_smash_sphere m m)))

end

end homology
