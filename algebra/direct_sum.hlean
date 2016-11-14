/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import .quotient_group .free_commutative_group

open eq algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops

namespace group

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : CommGroup}

  variables (X : Set) {l l' : list (X ⊎ X)}

  section

    parameters {I : Set} (Y : I → CommGroup)
    variables {A' : CommGroup}

    definition dirsum_carrier : CommGroup := free_comm_group (trunctype.mk (Σi, Y i) _)
    local abbreviation ι := @free_comm_group_inclusion
    inductive dirsum_rel : dirsum_carrier → Type :=
    | rmk : Πi y₁ y₂, dirsum_rel (ι ⟨i, y₁⟩ * ι ⟨i, y₂⟩ * (ι ⟨i, y₁ * y₂⟩)⁻¹)

    definition dirsum : CommGroup := quotient_comm_group_gen dirsum_carrier (λg, ∥dirsum_rel g∥)

    -- definition dirsum_carrier_incl [constructor] (i : I) : Y i →g dirsum_carrier :=

    definition dirsum_incl [constructor] (i : I) : Y i →g dirsum :=
    homomorphism.mk (λy, class_of (ι ⟨i, y⟩))
      begin intro g h, symmetry, apply gqg_eq_of_rel, apply tr, apply dirsum_rel.rmk end

    definition dirsum_elim [constructor] (f : Πi, Y i →g A') : dirsum →g A' :=
    begin
      refine homomorphism.mk (gqg_elim _ (free_comm_group_elim (λv, f v.1 v.2)) _) _,
      { intro g r, induction r with r, induction r,
        rewrite [to_respect_mul, to_respect_inv], apply mul_inv_eq_of_eq_mul,
        rewrite [one_mul], apply ap (free_comm_group_elim (λ v, group_fun (f v.1) v.2)),
        exact sorry
        },
      { exact sorry }
    end

    definition dirsum_elim_compute (f : Πi, Y i →g A') (i : I) :
      dirsum_elim f ∘g dirsum_incl i ~ f i :=
    begin
      intro g, exact sorry
    end

    definition dirsum_elim_unique (f : Πi, Y i →g A') (k : dirsum →g A')
      (H : Πi, k ∘g dirsum_incl i ~ f i) : k ~ dirsum_elim f :=
    sorry


  end

end group
