-- Author: Kuen-Bang Hou (Favonia)

import core types.lift
import ..homotopy.homology

open eq pointed group algebra circle sphere nat equiv susp
     function sphere homology int lift

namespace homology

section
  parameter (theory : homology_theory)

  open homology_theory

  theorem Hsphere : Π(n : ℕ), HH theory n (plift (psphere n)) ≃g HH theory 0 (plift (psphere 0)) :=
    sorry

end

end homology
