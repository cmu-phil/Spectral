/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import .quotient_group .free_commutative_group

open eq algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv

namespace group

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : CommGroup}

  variables (X : Set) {l l' : list (X ⊎ X)}

  section

    parameters {I : Set} (Y : I → CommGroup)

    definition dirsum_carrier : CommGroup := free_comm_group (trunctype.mk (Σi, Y i) _)
    local abbreviation ι := @free_comm_group_inclusion
    inductive dirsum_rel : dirsum_carrier → Type :=
    | rmk : Πi y₁ y₂, dirsum_rel (ι ⟨i, y₁⟩ * ι ⟨i, y₂⟩ * (ι ⟨i, y₁ * y₂⟩)⁻¹)

    definition direct_sum : CommGroup := quotient_comm_group_gen dirsum_carrier (λg, ∥dirsum_rel g∥)

  end

end group
