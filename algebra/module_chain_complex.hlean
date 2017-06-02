/-
Author: Jeremy Avigad
-/
import homotopy.chain_complex .left_module .exactness ..move_to_lib
open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc nat trunc
open algebra function
open chain_complex
open succ_str
open left_module

structure module_chain_complex (R : Ring) (N : succ_str) : Type :=
(mod : N → LeftModule R)
(hom : Π (n : N), mod (S n) →lm mod n)
(is_chain_complex :
  Π (n : N) (x : mod (S (S n))), hom n (hom (S n) x) = 0)

namespace module_chain_complex
  variables {R : Ring} {N : succ_str}

  definition mcc_mod [unfold 2] [coercion] (C : module_chain_complex R N) (n : N) :
    LeftModule R :=
  module_chain_complex.mod C n

  definition mcc_carr [unfold 2] [coercion] (C : module_chain_complex R N) (n : N) :
    Type :=
  C n

  definition mcc_pcarr [unfold 2] [coercion] (C : module_chain_complex R N) (n : N) :
    Set* :=
  mcc_mod C n

  definition mcc_hom (C : module_chain_complex R N) {n : N} : C (S n) →lm C n :=
  module_chain_complex.hom C n

  definition mcc_is_chain_complex (C : module_chain_complex R N) (n : N) (x : C (S (S n))) :
  mcc_hom C (mcc_hom C x) = 0 :=
  module_chain_complex.is_chain_complex C n x

  protected definition to_chain_complex [coercion] (C : module_chain_complex R N) :
  chain_complex N :=
    chain_complex.mk
  (λ n, mcc_pcarr C n)
  (λ n, pmap_of_homomorphism (@mcc_hom R N C n))
  (mcc_is_chain_complex C)

  -- maybe we don't even need this?
  definition is_exact_at_m (C : module_chain_complex R N) (n : N) : Type :=
  is_exact_at C n
end module_chain_complex

namespace left_module
  variable  {R : Ring}
  variables {A₀ B₀ C₀ : LeftModule R}
  variables (f₀ : A₀ →lm B₀) (g₀ : B₀ →lm C₀)

  definition is_short_exact := @algebra.is_short_exact  _ _ C₀ f₀ g₀
end left_module
