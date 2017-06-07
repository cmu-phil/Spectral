import .direct_sum .quotient_group

open eq algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops nat

namespace group

  section

    parameters (A : @trunctype.mk 0 ℕ _ → AddAbGroup) (f : Πi , A i → A (i + 1))
    variables {A' : AddAbGroup}

    definition seq_colim_carrier : AddAbGroup := dirsum A
    inductive seq_colim_rel : seq_colim_carrier → Type :=
    | rmk : Πi a, seq_colim_rel ((dirsum_incl A i a) - (dirsum_incl A (i + 1) (f i a)))
   
    definition seq_colim : AddAbGroup := quotient_ab_group_gen seq_colim_carrier (λa, ∥seq_colim_rel a∥)
 
    definition seq_colim_incl [constructor] (i : ℕ) : A i →a seq_colim :=
      qg_map _ ∘g dirsum_incl A i

    definition seq_colim_quotient (h : Πi, A i →a A') (k : Πi a, h i a = h (i + 1) (f i a))
                                  (v : seq_colim_carrier) (r : ∥seq_colim_rel v∥) : dirsum_elim h v = 0 :=
      begin
        induction r with r, induction r,
      end

    definition seq_colim_elim [constructor] (h : Πi, A i →a A') 
                                            (k : Πi a, h i a = h (i + 1) (f i a)) : seq_colim →a A' :=
      gqg_elim _ (dirsum_elim h) (seq_colim_quotient h k)

  end

end group

