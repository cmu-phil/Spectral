--Authors: Robert Rose, Liz Vidaurre

import .direct_sum .quotient_group ..move_to_lib

open eq algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops nat

namespace group

  section

    parameters (A : ℕ → AbGroup) (f : Πi , A i →g A (i + 1))
    variables {A' : AbGroup}

    definition seq_colim_carrier : AbGroup := dirsum A
    inductive seq_colim_rel : seq_colim_carrier → Type :=
    | rmk : Πi a, seq_colim_rel ((dirsum_incl A i a) * (dirsum_incl A (i + 1) (f i a))⁻¹)

    definition seq_colim : AbGroup := quotient_ab_group_gen seq_colim_carrier (λa, ∥seq_colim_rel a∥)

    parameters {A f}
    definition seq_colim_incl [constructor] (i : ℕ) : A i →g seq_colim :=
      gqg_map _ _ ∘g dirsum_incl A i

    definition seq_colim_quotient (h : Πi, A i →g A') (k : Πi a, h i a = h (succ i) (f i a))
                                  (v : seq_colim_carrier) (r : ∥seq_colim_rel v∥) : dirsum_elim h v = 1 :=
      begin
        induction r with r, induction r,
        refine !to_respect_mul ⬝ _,
        refine ap (λγ, group_fun (dirsum_elim h) (group_fun (dirsum_incl A i) a) * group_fun (dirsum_elim h) γ)
                  (!to_respect_inv)⁻¹ ⬝ _,
        refine ap (λγ, γ * group_fun (dirsum_elim h) (group_fun (dirsum_incl A (succ i)) (f i a)⁻¹))
                  !dirsum_elim_compute ⬝ _,
        refine ap (λγ, (h i a) * γ) !dirsum_elim_compute ⬝ _,
        refine ap (λγ, γ * group_fun (h (succ i)) (f i a)⁻¹) !k ⬝ _,
        refine ap (λγ, group_fun (h (succ i)) (f i a) * γ) (!to_respect_inv) ⬝ _,
        exact !mul.right_inv
      end

    definition seq_colim_elim [constructor] (h : Πi, A i →g A')
                                            (k : Πi a, h i a = h (succ i) (f i a)) : seq_colim →g A' :=
      gqg_elim _ (dirsum_elim h) (seq_colim_quotient h k)

    definition seq_colim_compute (h : Πi, A i →g A')
                                 (k : Πi a, h i a = h (succ i) (f i a)) (i : ℕ) (a : A i) :
               (seq_colim_elim h k) (seq_colim_incl i a) = h i a :=
      begin
        refine gqg_elim_compute (λa, ∥seq_colim_rel a∥) (dirsum_elim h) (seq_colim_quotient h k) (dirsum_incl A i a) ⬝ _,
        exact !dirsum_elim_compute
      end

    definition seq_colim_glue {i : @trunctype.mk 0 ℕ _} {a : A i} : seq_colim_incl i a = seq_colim_incl (succ i) (f i a) :=
    begin
      refine gqg_eq_of_rel _ _,
      exact tr (seq_colim_rel.rmk _ _)
    end

    section
      local abbreviation h (m : seq_colim →g A') : Πi, A i →g A' := λi, m ∘g (seq_colim_incl i)
      local abbreviation k (m : seq_colim →g A') : Πi a, h m i a = h m (succ i) (f i a) :=
      λ i a, ap m (@seq_colim_glue i a)

      definition seq_colim_unique (m : seq_colim →g A') :
        Πv, seq_colim_elim (h m) (k m) v = m v :=
      begin
        intro v, refine (gqg_elim_unique _ (dirsum_elim (h m)) _ m _ _)⁻¹ ⬝ _,
        apply dirsum_elim_unique, rotate 1, reflexivity,
        intro i a, reflexivity
      end

    end

  end

  definition seq_colim_functor [constructor] {A A' : ℕ → AbGroup}
    {f : Πi , A i →g A (i + 1)} {f' : Πi , A' i →g A' (i + 1)}
    (h : Πi, A i →g A' i) (p : Πi, hsquare (f i) (f' i) (h i) (h (i+1))) :
    seq_colim A f →g seq_colim A' f' :=
  seq_colim_elim (λi, seq_colim_incl i ∘g h i)
    begin
      intro i a,
      refine _ ⬝ ap (seq_colim_incl (succ i)) (p i a)⁻¹,
      apply seq_colim_glue
    end

  -- definition seq_colim_functor_compose [constructor] {A A' A'' : ℕ → AbGroup}
  --   {f : Πi , A i →g A (i + 1)} {f' : Πi , A' i →g A' (i + 1)} {f'' : Πi , A'' i →g A'' (i + 1)}
  --   (h : Πi, A i →g A' i) (p : Πi (a : A i), h (i+1) (f i a) = f' i (h i a))
  --   (h : Πi, A i →g A' i) (p : Πi (a : A i), h (i+1) (f i a) = f' i (h i a)) :
  --   seq_colim A f →g seq_colim A' f' :=
  -- sorry

end group
