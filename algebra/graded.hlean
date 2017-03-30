/- Graded modules -/

-- Author: Floris van Doorn

import ..algebra.module

open algebra eq left_module pointed function equiv is_equiv is_trunc prod

namespace left_module

definition graded (str : Type) (I : Type) : Type := I → str
definition graded_module (R : Ring) : Type → Type := graded (LeftModule R)

variables {R : Ring} {I : Type} {M M₁ M₂ M₃ : graded_module R I}

structure graded_module_hom (M₁ M₂ : graded_module R I) : Type :=
mk' ::  (d : I → I)
        (fn : Π⦃i j : I⦄ (p : d i = j), M₁ i →lm M₂ j)

abbreviation degree := @graded_module_hom.d
attribute graded_module_hom.fn [coercion]

definition graded_module_hom.mk {M₁ M₂ : graded_module R I} (d : I → I)
  (fn : Πi, M₁ i →lm M₂ (d i)) : graded_module_hom M₁ M₂ :=
graded_module_hom.mk' d (λi j p, homomorphism_of_eq (ap M₂ p) ∘lm fn i)

notation M₁ ` →gm ` M₂ := graded_module_hom M₁ M₂

-- definition graded_module_hom (d : I → I) (M₁ M₂ : graded_module R I) : Type :=
-- Π⦃i j : I⦄ (p : d i = j), M₁ i →lm M₂ j
exit
-- notation M₁ ` →[` d `] ` M₂ := graded_module_hom d M₁ M₂
variables {d d' d₁ d₂ d₃ : I → I} {f' : M₂ →[d'] M₃} {f : M₁ →[d] M₂} {f₁ : M₁ →[d₁] M₂}
          {f₂ : M₁ →[d₂] M₂} {f₃ : M₁ →[d₃] M₂}

definition graded_module_hom_ap (f : M₁ →[d] M₂) {i : I} (x : M₁ i) : M₂ (d i) :=
f idp x

abbreviation gap := @graded_module_hom_ap

definition is_exact_gmod (f : M₁ →[d] M₂) (f' : M₂ →[d'] M₃) : Type :=
Π{i j k} (p : d i = j) (q : d' j = k), is_exact_mod (f p) (f' q)

structure exact_couple (M₁ M₂ : graded_module R I) : Type :=
  (di dj dk : I → I)
  ( i : M₁ →[di] M₁) (j : M₁ →[dj] M₂) (k : M₂ →[dk] M₁)
  ( exact_ij : is_exact_gmod i j)
  ( exact_jk : is_exact_gmod j k)
  ( exact_ki : is_exact_gmod k i)

  variables {di dj dk : I → I}
            {i : M₁ →[di] M₁} {j : M₁ →[dj] M₂} {k : M₂ →[dk] M₁}
            ( exact_ij : is_exact_gmod i j)
            ( exact_jk : is_exact_gmod j k)
            ( exact_ki : is_exact_gmod k i)

  namespace derived_couple

  definition d : graded_module_hom _ M₂ M₂ :=
  _

  end derived_couple


end left_module
