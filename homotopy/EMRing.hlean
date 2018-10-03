-- Authors: Floris van Doorn

import .EM .smash_adjoint ..algebra.ring ..algebra.arrow_group

open algebra eq EM is_equiv equiv is_trunc is_conn pointed trunc susp smash group nat function

namespace EM


definition EM1product_adj {R : Ring} :
  EM1 (AddGroup_of_Ring R) →* ppmap (EM1 (AddGroup_of_Ring R)) (EMadd1 (AddAbGroup_of_Ring R) 1) :=
begin
  have is_trunc 1 (ppmap (EM1 (AddGroup_of_Ring R)) (EMadd1 (AddAbGroup_of_Ring R) 1)),
    from is_trunc_pmap_of_is_conn _ _ !is_conn_EM1 _ _ _ (le.refl 2) !is_trunc_EMadd1,
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

-- TODO: simplify
definition EMadd1product {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  EMadd1 A n →* EMadd1 B m →** EMadd1 C (m + succ n) :=
begin
  assert H1 : is_trunc n.+1 (EMadd1 B m →** EMadd1 C (m + succ n)),
  { refine is_trunc_pmap_of_is_conn _ (m.-1) !is_conn_EMadd1 _ _ _ _ !is_trunc_EMadd1,
    exact le_of_eq (trunc_index.of_nat_add_plus_two_of_nat m n)⁻¹ᵖ },
  apply EMadd1_pmap,
  refine (gloopn_pmap_isomorphism (succ n) _ _)⁻¹ᵍ⁸ ∘∞g
    gpmap_loop_homomorphism_right (EMadd1 B m) (loopn_EMadd1_add_of_eq C !succ_add)⁻¹ᵉ* ∘∞g
    gloop_pmap_isomorphism _ _ ∘∞g
    (deloop_isomorphism _)⁻¹ᵍ⁸ ∘∞g
    EM_ehomomorphism B C (succ m) ∘∞g
    inf_homomorphism_of_homomorphism φ
end

definition EMproduct1 {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
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


definition EMproduct2 {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  EM A n →* (EM B m →** EM C (m + n)) :=
begin
  assert H1 : is_trunc n (gpmap_loop' (EM B m) (loop_EM C (m + n))),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
  apply EM_pmap (gpmap_loop' (EM B m) (loop_EM C (m + n))) n,
  exact sorry
  -- exact _ /- (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* -/ ∘∞g _ /-ppcompose_left !loopn_EMadd1_add⁻¹ᵉ*-/ ∘∞g
  --      _ ∘∞g inf_homomorphism_of_homomorphism φ

end

definition EMproduct3' {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  gEM A n →∞g gpmap_loop' (EM B m) (loop_EM C (m + n)) :=
begin
  assert H1 : is_trunc n (gpmap_loop' (EM B m) (loop_EM C (m + n))),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
--   refine EM_homomorphism _ _ _,
-- --(gmap_loop' (EM B m) (loop_EM C (m + n))) n,
--   exact _ /- (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* -/ ∘∞g _ /-ppcompose_left !loopn_EMadd1_add⁻¹ᵉ*-/ ∘∞g
--        _ ∘∞g inf_homomorphism_of_homomorphism φ
 exact sorry
end

definition EMproduct4 {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  gEM A n →∞g Ωg (EM B m →** EM C (m + n + 1)) :=
begin
  assert H1 : is_trunc (n+1) (EM B m →** EM C (m + n + 1)),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
   apply EM_homomorphism_gloop,
   refine (gloopn_pmap_isomorphism _ _ _)⁻¹ᵍ⁸ ∘∞g _ ∘∞g inf_homomorphism_of_homomorphism φ,

--   exact _ /- (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* -/ ∘∞g _ /-ppcompose_left !loopn_EMadd1_add⁻¹ᵉ*-/ ∘∞g
--        _ ∘∞g inf_homomorphism_of_homomorphism φ
  exact sorry
end

definition EMproduct5 {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  InfGroup_of_deloopable (EM A n) →∞g InfGroup_of_deloopable (EM B m →** EM C (m + n)) :=
begin
  assert H1 : is_trunc (n + 1) (deloop (EM B m →** EM C (m + n))),
  { exact is_trunc_pmap_of_is_conn_nat _ m !is_conn_EM _ _ _ !le.refl !is_trunc_EM },
  refine EM_homomorphism_deloopable _ _ _ _ _,

  -- exact _ /- (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* -/ ∘∞g _ /-ppcompose_left !loopn_EMadd1_add⁻¹ᵉ*-/ ∘∞g
  --      _ ∘∞g inf_homomorphism_of_homomorphism φ
  exact sorry
end

definition EMadd1product2 {A B C : AbGroup} (φ : A →g B →gg C) (n m : ℕ) :
  gEM A (n+1) →∞g Ωg[succ n] (EMadd1 B m →** EMadd1 C m) :=
begin
  assert H1 : is_trunc (n+1) (Ω[n] (EMadd1 B m →** EMadd1 C m)),
  { apply is_trunc_loopn, exact sorry },
--  refine EM_homomorphism_gloop (Ω[n] (EMadd1 B m →** EMadd1 C m)) _ _,
  /- the underlying pointed map is: -/
--  exact sorry
  -- refine (loopn_ppmap_pequiv _ _ _)⁻¹ᵉ* ∘* ppcompose_left !loopn_EMadd1_add⁻¹ᵉ* ∘*
  --     EM0EMadd1product φ m
  exact sorry
end


end EM
