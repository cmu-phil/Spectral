import .direct_sum .quotient_group

open eq algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops nat

namespace group

  section

    parameters (A : @trunctype.mk 0 ℕ _ → AbGroup) (f : Πi , A i → A (i + 1))
    variables {A' : AbGroup}

    definition seq_colim_carrier : AbGroup := dirsum A
    inductive seq_colim_rel : seq_colim_carrier → Type :=
    | rmk : Πi a, seq_colim_rel ((dirsum_incl A i a) * (dirsum_incl A (i + 1) (f i a))⁻¹)

    definition seq_colim : AbGroup := quotient_ab_group_gen seq_colim_carrier (λa, ∥seq_colim_rel a∥)

    definition seq_colim_incl [constructor] (i : ℕ) : A i →g seq_colim :=
      qg_map _ ∘g dirsum_incl A i

    definition seq_colim_quotient (h : Πi, A i →g A') (k : Πi a, h i a = h (i + 1) (f i a))
                                  (v : seq_colim_carrier) (r : ∥seq_colim_rel v∥) : dirsum_elim h v = 1 :=
      begin
        induction r with r, induction r, exact sorry
      end

    definition seq_colim_elim [constructor] (h : Πi, A i →g A')
                                            (k : Πi a, h i a = h (i + 1) (f i a)) : seq_colim →g A' :=
      gqg_elim _ (dirsum_elim h) (seq_colim_quotient h k)

  end

end group
