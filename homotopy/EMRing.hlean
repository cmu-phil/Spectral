-- Authors: Floris van Doorn

import .EM .smash_adjoint ..algebra.ring

open algebra eq EM is_equiv equiv is_trunc is_conn pointed trunc susp smash group nat
namespace EM

definition EM1product_adj {R : Ring} :
  EM1 (AbGroup_of_Ring R) →* ppmap (EM1 (AbGroup_of_Ring R)) (EMadd1 (AbGroup_of_Ring R) 1) :=
begin
  have is_trunc 1 (ppmap (EM1 (AbGroup_of_Ring R)) (EMadd1 (AbGroup_of_Ring R) 1)),
    from is_trunc_pmap_of_is_conn _ _ _ _ _ _ (le.refl 2) !is_trunc_EMadd1,
  fapply EM1_pmap,
  { intro r, refine pfunext _ _, exact !loop_EM2⁻¹ᵉ* ∘* EM1_functor (ring_right_action r), },
  { intro r r', exact sorry }
end

definition EMproduct_map {G H K : AbGroup} (φ : G → H →g K) (n m : ℕ) (g : G) :
  EMadd1 H n →* EMadd1 K n :=
begin
  fapply EMadd1_functor (φ g) n
end

definition EM0EMadd1product {G H K : AbGroup} (φ : G →g H →gg K) (n : ℕ) :
  G →* EMadd1 H n →** EMadd1 K n :=
EMadd1_pfunctor H K n ∘* pmap_of_homomorphism φ

definition EMadd1product {G H K : AbGroup} (φ : G →g H →gg K) (n m : ℕ) :
  EMadd1 G n →* EMadd1 H m →** EMadd1 K (m + succ n) :=
begin
  assert H1 : is_trunc n.+1 (EMadd1 H m →** EMadd1 K (m + succ n)),
  { refine is_trunc_pmap_of_is_conn _ (m.-1) !is_conn_EMadd1 _ _ _ _ !is_trunc_EMadd1,
    exact le_of_eq (trunc_index.of_nat_add_plus_two_of_nat m n)⁻¹ᵖ },
  fapply EMadd1_pmap,
  { refine (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* ∘* ppcompose_left !loopn_EMadd1_add⁻¹ᵉ* ∘*
      EM0EMadd1product φ m },
  { exact sorry }
end

definition EMproduct {G H K : AbGroup} (φ : G →g H →gg K) (n m : ℕ) :
  EM G n →* EM H m →** EM K (m + n) :=
begin
  cases n with n,
  { cases m with m,
    { exact pmap_of_homomorphism2 φ },
    { exact EM0EMadd1product φ m }},
  { cases m with m,
    { exact ppcompose_left (ptransport (EMadd1 K) (zero_add n)⁻¹) ∘*
        pmap_swap_map (EM0EMadd1product (homomorphism_swap φ) n) },
    { exact ppcompose_left (ptransport (EMadd1 K) !succ_add⁻¹) ∘* EMadd1product φ n m }}
end

end EM
