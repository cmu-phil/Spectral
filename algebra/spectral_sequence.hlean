/- Spectral sequences
  - basic properties of spectral sequences
  - currently, we only construct an spectral sequence from an exact couple
 -/

-- Author: Floris van Doorn

import .exact_couple

open algebra is_trunc left_module is_equiv equiv eq function nat sigma set_quotient group
     left_module group int prod prod.ops
open exact_couple (Z2)

structure convergent_spectral_sequence.{u v w} {R : Ring} (E' : agℤ → agℤ → LeftModule.{u v} R)
                               (Dinf : agℤ → LeftModule.{u w} R) : Type.{max u (v+1) (w+1)} :=
  (E : ℕ → graded_module.{u 0 v} R Z2)
  (d : Π(r : ℕ), E r →gm E r)
  (deg_d : ℕ → Z2)
  (deg_d_eq0 : Π(r : ℕ), deg (d r) 0 = deg_d r)
  (α : Π(r : ℕ) (x : Z2), E (r+1) x ≃lm graded_homology (d r) (d r) x)
  (e : Π(x : Z2), E 0 x ≃lm E' x.1 x.2)
  (s₀ : Z2 → ℕ)
  (f : Π{r : ℕ} {x : Z2} (h : s₀ x ≤ r), E (s₀ x) x ≃lm E r x)
  (lb : ℤ → ℤ)
  (HDinf : Π(n : agℤ), is_built_from (Dinf n)
                                     (λ(k : ℕ), (λx, E (s₀ x) x) (n - (k + lb n), k + lb n)))

definition convergent_spectral_sequence_g [reducible] (E' : agℤ → agℤ → AbGroup)
  (Dinf : agℤ → AbGroup) : Type :=
convergent_spectral_sequence (λn s, LeftModule_int_of_AbGroup (E' n s))
                             (λn, LeftModule_int_of_AbGroup (Dinf n))

  section exact_couple
  open exact_couple exact_couple.exact_couple exact_couple.convergent_exact_couple
       exact_couple.convergence_theorem exact_couple.derived_couple

  definition convergent_spectral_sequence_of_exact_couple {R : Ring} {E' : agℤ → agℤ → LeftModule R}
    {Dinf : agℤ → LeftModule R} (c : convergent_exact_couple E' Dinf)
    (st_eq : Πn, (st c n).1 + (st c n).2 = n) (deg_i_eq : deg (i (X c)) 0 = (-(1 : ℤ), (1 : ℤ))) :
    convergent_spectral_sequence E' Dinf :=
  convergent_spectral_sequence.mk (λr, E (page (X c) r)) (λr, d (page (X c) r))
    (deg_d c) (deg_d_eq0 c)
    (λr ns, by reflexivity) (e c) (B3 (HH c)) (λr ns Hr, Einfstable (HH c) Hr idp)
    (λn, (st c n).2)
    begin
      intro n,
      refine is_built_from_isomorphism (f c n) _ (is_built_from_infpage (HH c) (st c n) (HB c n)),
      intro p, apply isomorphism_of_eq, apply ap (λx, E (page (X c) (B3 (HH c) x)) x),
      induction p with p IH,
      { exact !prod.eta⁻¹ ⬝ prod_eq (eq_sub_of_add_eq (ap (add _) !zero_add ⬝ st_eq n))
                                    (zero_add (st c n).2)⁻¹ },
      { assert H1 : Π(a : ℤ), n - (p + a) - (1 : ℤ) = n - (succ p + a),
        exact λa, !sub_add_eq_sub_sub⁻¹ ⬝ ap (sub n) (add_comm_middle p a (1 : ℤ) ⬝ proof idp qed),
        assert H2 : Π(a : ℤ), p + a + 1 = succ p + a,
        exact λa, add_comm_middle p a 1,
        refine ap (deg (i (X c))) IH ⬝ !deg_eq ⬝ ap (add _) deg_i_eq ⬝ prod_eq !H1 !H2 }
    end
    end exact_couple

namespace spectral_sequence
  open convergent_spectral_sequence

  variables {R : Ring} {E' : agℤ → agℤ → LeftModule R} {Dinf : agℤ → LeftModule R}
    (c : convergent_spectral_sequence E' Dinf)

    -- (E : ℕ → graded_module.{u 0 v} R Z2)
    -- (d : Π(r : ℕ), E r →gm E r)
    -- (deg_d : ℕ → Z2)
    -- (deg_d_eq0 : Π(r : ℕ), deg (d r) 0 = deg_d r)
    -- (α : Π(r : ℕ) (x : Z2), E (r+1) x ≃lm graded_homology (d r) (d r) x)
    -- (e : Π(x : Z2), E 0 x ≃lm E' x.1 x.2)
    -- (s₀ : Z2 → ℕ)
    -- (f : Π{r : ℕ} {x : Z2} (h : s₀ x ≤ r), E (s₀ x) x ≃lm E r x)
    -- (lb : ℤ → ℤ)
    -- (HDinf : Π(n : agℤ), is_built_from (Dinf n)
    --                                    (λ(k : ℕ), (λx, E (s₀ x) x) (n - (k + lb n), k + lb n)))

  definition Einf (x : Z2) : LeftModule R := E c (s₀ c x) x

  definition is_contr_E_succ (r : ℕ) (x : Z2) (h : is_contr (E c r x)) : is_contr (E c (r+1) x) :=
  is_contr_equiv_closed_rev (equiv_of_isomorphism (α c r x)) (is_contr_homology _ _ _)

  definition deg_d_eq (r : ℕ) (x : Z2) : deg (d c r) x = x + deg_d c r :=
  !deg_eq ⬝ ap (add _) !deg_d_eq0

  definition deg_d_inv_eq (r : ℕ) (x : Z2) : (deg (d c r))⁻¹ᵉ x = x - deg_d c r :=
  inv_eq_of_eq (!deg_d_eq ⬝ !neg_add_cancel_right)⁻¹

  definition is_contr_E_of_le {r₁ r₂ : ℕ} (H : r₁ ≤ r₂) (x : Z2) (h : is_contr (E c r₁ x)) :
    is_contr (E c r₂ x) :=
  begin
    induction H with r₂ H IH,
    { exact h },
    { apply is_contr_E_succ, exact IH }
  end

  definition is_contr_E (r : ℕ) (x : Z2) (h : is_contr (E' x.1 x.2)) : is_contr (E c r x) :=
  is_contr_E_of_le c !zero_le x (is_contr_equiv_closed_rev (equiv_of_isomorphism (e c x)) h)

  definition is_contr_Einf (x : Z2) (h : is_contr (E' x.1 x.2)) : is_contr (Einf c x) :=
  is_contr_E c (s₀ c x) x h

  definition E_isomorphism {r₁ r₂ : ℕ} {ns : Z2} (H : r₁ ≤ r₂)
    (H1 : Π⦃r⦄, r₁ ≤ r → r < r₂ → is_contr (E c r (ns - deg_d c r)))
    (H2 : Π⦃r⦄, r₁ ≤ r → r < r₂ → is_contr (E c r (ns + deg_d c r))) :
    E c r₂ ns ≃lm E c r₁ ns :=
  begin
    assert H3 : Π⦃r⦄, r₁ ≤ r → r ≤ r₂ → E c r ns ≃lm E c r₁ ns,
    { intro r Hr₁ Hr₂,
      induction Hr₁ with r Hr₁ IH, reflexivity,
      let Hr₂' := le_of_succ_le Hr₂,
      refine α c r ns  ⬝lm homology_isomorphism _ _ _ _ ⬝lm IH Hr₂',
      exact is_contr_equiv_closed (equiv_ap (E c r) !deg_d_inv_eq⁻¹) (H1 Hr₁ Hr₂),
      exact is_contr_equiv_closed (equiv_ap (E c r) !deg_d_eq⁻¹) (H2 Hr₁ Hr₂) },
    exact H3 H (le.refl _)
  end

  definition E_isomorphism0 {r : ℕ} {n s : agℤ}
    (H1 : Πr', r' < r → is_contr (E' (n - (deg_d c r').1) (s - (deg_d c r').2)))
    (H2 : Πr', r' < r → is_contr (E' (n + (deg_d c r').1) (s + (deg_d c r').2))) :
    E c r (n, s) ≃lm E' n s :=
  E_isomorphism c !zero_le (λr' Hr₁ Hr₂, is_contr_E c r' _ (H1 r' Hr₂))
   (λr' Hr₁ Hr₂, is_contr_E c r' _ (H2 r' Hr₂)) ⬝lm
  e c (n, s)

  definition Einf_isomorphism (r₁ : ℕ) {ns : Z2}
    (H1 : Π⦃r⦄, r₁ ≤ r → is_contr (E c r (ns - deg_d c r)))
    (H2 : Π⦃r⦄, r₁ ≤ r → is_contr (E c r (ns + deg_d c r))) :
    Einf c ns ≃lm E c r₁ ns :=
  begin
    cases le.total r₁ (s₀ c ns) with Hr Hr,
    exact E_isomorphism c Hr (λr Hr₁ Hr₂, H1 Hr₁) (λr Hr₁ Hr₂, H2 Hr₁),
    exact f c Hr
  end

  definition Einf_isomorphism0 {n s : agℤ}
    (H1 : Πr, is_contr (E' (n - (deg_d c r).1) (s - (deg_d c r).2)))
    (H2 : Πr, is_contr (E' (n + (deg_d c r).1) (s + (deg_d c r).2))) :
    Einf c (n, s) ≃lm E' n s :=
  E_isomorphism0 c (λr Hr, H1 r) (λr Hr, H2 r)


end spectral_sequence
