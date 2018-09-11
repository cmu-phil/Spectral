-- Authors: Floris van Doorn

import .EM .smash_adjoint ..algebra.ring ..algebra.arrow_group

open algebra eq EM is_equiv equiv is_trunc is_conn pointed trunc susp smash group nat
namespace EM

definition EM1product_adj {R : Ring} :
  EM1 (AbGroup_of_Ring R) →* ppmap (EM1 (AbGroup_of_Ring R)) (EMadd1 (AbGroup_of_Ring R) 1) :=
begin
  have is_trunc 1 (ppmap (EM1 (AbGroup_of_Ring R)) (EMadd1 (AbGroup_of_Ring R) 1)),
    from is_trunc_pmap_of_is_conn _ _ _ _ _ _ (le.refl 2) !is_trunc_EMadd1,
  apply EM1_pmap, fapply inf_homomorphism.mk,
  { intro r, refine pfunext _ _, exact !loop_EM2⁻¹ᵉ* ∘* EM1_functor (ring_right_action r), },
  { intro r r', exact sorry }
end

definition EMproduct_map {A B C : AbGroup} (φ : A → B →g C) (n m : ℕ) (a : A) :
  EMadd1 B n →* EMadd1 C n :=
begin
  fapply EMadd1_functor (φ a) n
end

definition EM0EMadd1product {A B C : AbGroup} (φ : A →g B →gg C) (n : ℕ) :
  A →* EMadd1 B n →** EMadd1 C n :=
EMadd1_pfunctor B C n ∘* pmap_of_homomorphism φ

definition EMadd1product {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  EMadd1 A n →* EMadd1 B m →** EMadd1 C (m + succ n) :=
begin
  assert H1 : is_trunc n.+1 (EMadd1 B m →** EMadd1 C (m + succ n)),
  { refine is_trunc_pmap_of_is_conn _ (m.-1) !is_conn_EMadd1 _ _ _ _ !is_trunc_EMadd1,
    exact le_of_eq (trunc_index.of_nat_add_plus_two_of_nat m n)⁻¹ᵖ },
  apply EMadd1_pmap,
  exact sorry
  /- the underlying pointed map is: -/
  -- refine (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* ∘* ppcompose_left !loopn_EMadd1_add⁻¹ᵉ* ∘*
  --     EM0EMadd1product φ m
end

definition EMproduct {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  EM A n →* EM B m →** EM C (m + n) :=
begin
  cases n with n,
  { cases m with m,
    { exact pmap_of_homomorphism2 φ },
    { exact EM0EMadd1product φ m }},
  { cases m with m,
    { exact ppcompose_left (ptransport (EMadd1 C) (zero_add n)⁻¹) ∘*
        pmap_swap_map (EM0EMadd1product (homomorphism_swap φ) n) },
    { exact ppcompose_left (ptransport (EMadd1 C) !succ_add⁻¹) ∘* EMadd1product φ n m }}
end

definition EMproduct' {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  EM A n →* EM B m →** EM C (m + n) :=
begin
  assert H1 : is_trunc n (InfGroup_pmap' (EM B m) (loop_EM C (m + n))),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
  apply EM_pmap (InfGroup_pmap' (EM B m) (loop_EM C (m + n))) n,
  exact sorry
  -- exact _ /- (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* -/ ∘∞g _ /-ppcompose_left !loopn_EMadd1_add⁻¹ᵉ*-/ ∘∞g
  --      _ ∘∞g inf_homomorphism_of_homomorphism φ

end


end EM
