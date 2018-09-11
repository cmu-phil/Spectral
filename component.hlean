-- Author: Floris van Doorn

import homotopy.connectedness .move_to_lib

open eq equiv pointed is_conn is_trunc sigma prod trunc function group nat fiber

namespace is_conn

  open sigma.ops pointed trunc_index

  /- this is equivalent to pfiber (A → ∥A∥₀) ≡ connect 0 A -/
  definition component [constructor] (A : Type*) : Type* :=
  pType.mk (Σ(a : A), merely (pt = a)) ⟨pt, tr idp⟩

  lemma is_conn_component [instance] (A : Type*) : is_conn 0 (component A) :=
  is_conn_zero_pointed'
    begin intro x, induction x with a p, induction p with p, induction p, exact tidp end

  definition component_incl [constructor] (A : Type*) : component A →* A :=
  pmap.mk pr1 idp

  definition is_embedding_component_incl [instance] (A : Type*) : is_embedding (component_incl A) :=
  is_embedding_pr1 _

  definition component_intro [constructor] {A B : Type*} (f : A →* B) (H : merely_constant f) :
    A →* component B :=
  begin
    fapply pmap.mk,
    { intro a, refine ⟨f a, _⟩, exact tinverse (merely_constant_pmap H a) },
    exact subtype_eq !respect_pt
  end

  definition component_functor [constructor] {A B : Type*} (f : A →* B) :
    component A →* component B :=
  component_intro (f ∘* component_incl A) !merely_constant_of_is_conn

  -- definition component_elim [constructor] {A B : Type*} (f : A →* B) (H : merely_constant f) :
  --   A →* component B :=
  -- begin
  --   fapply pmap.mk,
  --   { intro a, refine ⟨f a, _⟩, exact tinverse (merely_constant_pmap H a) },
  --   exact subtype_eq !respect_pt
  -- end

  definition loop_component (A : Type*) : Ω (component A) ≃* Ω A :=
  loop_pequiv_loop_of_is_embedding (component_incl A)

  lemma loopn_component (n : ℕ) (A : Type*) : Ω[n+1] (component A) ≃* Ω[n+1] A :=
  !loopn_succ_in ⬝e* loopn_pequiv_loopn n (loop_component A) ⬝e* !loopn_succ_in⁻¹ᵉ*

  -- lemma fundamental_group_component (A : Type*) : π₁ (component A) ≃g π₁ A :=
  -- isomorphism_of_equiv (trunc_equiv_trunc 0 (loop_component A)) _

  lemma homotopy_group_component (n : ℕ) (A : Type*) : πg[n+1] (component A) ≃g πg[n+1] A :=
  homotopy_group_isomorphism_of_is_embedding (n+1) (component_incl A)

  definition is_trunc_component [instance] (n : ℕ₋₂) (A : Type*) [is_trunc n A] :
    is_trunc n (component A) :=
  begin
    apply @is_trunc_sigma, intro a, cases n with n,
    { refine is_contr_of_inhabited_prop _ _, exact tr !is_prop.elim },
    { exact is_trunc_succ_of_is_prop _ _ _ },
  end

  definition ptrunc_component' (n : ℕ₋₂) (A : Type*) :
    ptrunc (n.+2) (component A) ≃* component (ptrunc (n.+2) A) :=
  begin
    fapply pequiv.MK',
    { exact ptrunc.elim (n.+2) (component_functor !ptr) },
    { intro x, cases x with x p, induction x with a,
      refine tr ⟨a, _⟩,
      note q := trunc_functor -1 !tr_eq_tr_equiv p,
      exact trunc_trunc_equiv_left _ !minus_one_le_succ q },
    { exact sorry },
    { exact sorry }
  end

  definition ptrunc_component (n : ℕ₋₂) (A : Type*) :
    ptrunc n (component A) ≃* component (ptrunc n A) :=
  begin
    cases n with n, exact sorry,
    cases n with n, exact sorry,
    exact ptrunc_component' n A
  end

  definition break_into_components (A : Type) : A ≃ Σ(x : trunc 0 A), Σ(a : A), ∥ tr a = x ∥ :=
  calc
    A ≃ Σ(a : A) (x : trunc 0 A), tr a = x :
        by exact (@sigma_equiv_of_is_contr_right _ _ (λa, !is_contr_sigma_eq))⁻¹ᵉ
  ... ≃ Σ(x : trunc 0 A) (a : A), tr a = x :
        by apply sigma_comm_equiv
  ... ≃ Σ(x : trunc 0 A), Σ(a : A), ∥ tr a = x ∥ :
        by exact sigma_equiv_sigma_right (λx, sigma_equiv_sigma_right (λa, !trunc_equiv⁻¹ᵉ))

  definition pfiber_pequiv_component_of_is_contr [constructor] {A B : Type*} (f : A →* B)
    [is_contr B]
    /- extra condition, something like trunc_functor 0 f is an embedding -/ : pfiber f ≃* component A :=
  sorry

end is_conn
