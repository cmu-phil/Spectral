/-
Copyright (c) 2017 Kuen-Bang Hou (Favonia).
Released under Apache 2.0 license as described in the file LICENSE.

Author: Kuen-Bang Hou (Favonia)
-/

import .basic

open eq pointed group algebra circle sphere nat equiv susp
     function sphere homology int lift

namespace homology

section
  parameter (theory : homology_theory)

  open homology_theory

  theorem Hpsphere : Π(n : ℤ)(m : ℕ), HH theory n (plift (psphere m)) ≃g HH theory (n - m) (plift (psphere 0)) :=
    begin
      intros n m, revert n, induction m with m,
      { exact λ n, isomorphism_ap (λ n, HH theory n (plift (psphere 0))) (sub_zero n)⁻¹ },
      { intro n, exact calc
                  HH theory n (plift (psusp (psphere m)))
               ≃g HH theory (succ (pred n)) (plift (psusp (psphere m)))
                  : by exact isomorphism_ap (λ n, HH theory n (plift (psusp (psphere m)))) (succ_pred n)⁻¹
           ... ≃g HH theory (pred n) (plift (psphere m)) : by exact Hplift_psusp theory (pred n) (psphere m)
           ... ≃g HH theory (pred n - m) (plift (psphere 0)) : by exact v_0 (pred n)
           ... ≃g HH theory (n - succ m) (plift (psphere 0))
                  : by exact isomorphism_ap (λ n, HH theory n (plift (psphere 0))) (sub_sub n 1 m ⬝ ap (λ m, n - m) (add.comm 1 m))
      }
    end
end

end homology
