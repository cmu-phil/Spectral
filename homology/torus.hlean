/-
Copyright (c) 2017 Kuen-Bang Hou (Favonia).
Released under Apache 2.0 license as described in the file LICENSE.

Author: Kuen-Bang Hou (Favonia)
-/

import .homology .sphere ..susp_product

open eq pointed group algebra circle sphere nat equiv susp
     function sphere homology int lift prod smash

namespace homology

section
  parameter (theory : ordinary_homology_theory)

  open ordinary_homology_theory

  theorem Hptorus : Π(n : ℤ)(m : ℕ), HH theory n (plift (psphere m ×* psphere m)) ≃g
    HH theory n (plift (psphere m)) ×g (HH theory n (plift (psphere m)) ×g HH theory n (plift (psphere (m + m)))) := λ n m,
    calc        HH theory n (plift (psphere m ×* psphere m))
             ≃g HH theory (n + 1) (plift (⅀ (psphere m ×* psphere m))) : by exact (Hplift_psusp theory n (psphere m ×* psphere m))⁻¹ᵍ
         ... ≃g HH theory (n + 1) (plift (⅀ (psphere m) ∨ (⅀ (psphere m) ∨ ⅀ (psphere m ∧ psphere m))))
                   : by exact HH_isomorphism theory (n + 1) (!pequiv_plift⁻¹ᵉ* ⬝e* susp_product (psphere m) (psphere m) ⬝e* !pequiv_plift)
         ... ≃g HH theory (n + 1) (plift (⅀ (psphere m))) ×g HH theory (n + 1) (plift (⅀ (psphere m) ∨ (⅀ (psphere m ∧ psphere m))))
                   : by exact Hplift_pwedge theory (n + 1) (⅀ (psphere m)) (⅀ (psphere m) ∨ (⅀ (psphere m ∧ psphere m)))
         ... ≃g HH theory n (plift (psphere m)) ×g (HH theory n (plift (psphere m)) ×g HH theory n (plift (psphere (m + m))))
                   : by exact product_isomorphism (Hplift_psusp theory n (psphere m))
             (calc
                     HH theory (n + 1) (plift (⅀ (psphere m) ∨ (⅀ (psphere m ∧ psphere m))))
                  ≃g HH theory (n + 1) (plift (⅀ (psphere m))) ×g HH theory (n + 1) (plift (⅀ (psphere m ∧ psphere m)))
                     : by exact Hplift_pwedge theory (n + 1) (⅀ (psphere m)) (⅀ (psphere m ∧ psphere m))
              ... ≃g HH theory n (plift (psphere m)) ×g HH theory n (plift (psphere (m + m)))
                     : by exact product_isomorphism (Hplift_psusp theory n (psphere m))
                                  (Hplift_psusp theory n (psphere m ∧ psphere m) ⬝g HH_isomorphism theory n (!pequiv_plift⁻¹ᵉ* ⬝e* (sphere_smash_sphere m m) ⬝e* !pequiv_plift)))

end

end homology
