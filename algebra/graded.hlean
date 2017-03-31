/- Graded (left-) R-modules for a ring R. -/

-- Author: Floris van Doorn

import .left_module .direct_sum

open algebra eq left_module pointed function equiv is_equiv is_trunc prod group

namespace left_module

definition graded [reducible] (str : Type) (I : Type) : Type := I → str
definition graded_module [reducible] (R : Ring) : Type → Type := graded (LeftModule R)

variables {R : Ring} {I : Type} {M M₁ M₂ M₃ : graded_module R I}

/-
  morphisms between graded modules.
  The definition is unconventional in two ways:
  (1) The degree is determined by an endofunction instead of a element of I (and in this case we
    don't need to assume that I is a group). The "standard" degree i corresponds to the endofunction
    which is addition with i on the right. However, this is more flexible. For example, the
    composition of two graded module homomorphisms φ₂ and φ₁ with degrees i₂ and i₁ has type
    M₁ i → M₂ ((i + i₁) + i₂).
    However, a homomorphism with degree i₁ + i₂ must have type
    M₁ i → M₂ (i + (i₁ + i₂)),
    which means that we need to insert a transport. With endofunctions this is not a problem:
    λi, (i + i₁) + i₂
    is a perfectly fine degree of a map
  (2) Since we cannot eliminate all possible transports, we don't define a homomorphism as function
    M₁ i →lm M₂ (i + deg f)  or  M₁ i →lm M₂ (deg f i)
    but as a function taking a path as argument. Specifically, for every path
    deg f i = j
    we get a function M₁ i → M₂ j.
-/
structure graded_hom (M₁ M₂ : graded_module R I) : Type :=
mk' ::  (d : I → I)
        (fn' : Π⦃i j : I⦄ (p : d i = j), M₁ i →lm M₂ j)

notation M₁ ` →gm ` M₂ := graded_hom M₁ M₂

abbreviation deg [unfold 5] := @graded_hom.d
notation `↘` := graded_hom.fn' -- there is probably a better character for this?

definition graded_hom_fn [unfold 5] [coercion] (f : M₁ →gm M₂) (i : I) : M₁ i →lm M₂ (deg f i) :=
↘f idp

definition graded_hom.mk [constructor] {M₁ M₂ : graded_module R I} (d : I → I)
  (fn : Πi, M₁ i →lm M₂ (d i)) : M₁ →gm M₂ :=
graded_hom.mk' d (λi j p, homomorphism_of_eq (ap M₂ p) ∘lm fn i)

variables {f' : M₂ →gm M₃} {f : M₁ →gm M₂}

definition graded_hom_compose [constructor] (f' : M₂ →gm M₃) (f : M₁ →gm M₂) : M₁ →gm M₃ :=
graded_hom.mk (deg f' ∘ deg f) (λi, f' (deg f i) ∘lm f i)

variable (M)
definition graded_hom_id [constructor] [refl] : M →gm M :=
graded_hom.mk id (λi, lmid)
variable {M}

abbreviation gmid [constructor] := graded_hom_id M
infixr ` ∘gm `:75 := graded_hom_compose

structure graded_iso (M₁ M₂ : graded_module R I) : Type :=
  (to_hom : M₁ →gm M₂)
  (is_equiv_deg : is_equiv (deg to_hom))
  (is_equiv_to_hom : Π⦃i j⦄ (p : deg to_hom i = j), is_equiv (↘to_hom p))

infix ` ≃gm `:25 := graded_iso
attribute graded_iso.to_hom [coercion]
attribute graded_iso.is_equiv_deg [instance] [priority 1010]
attribute graded_iso._trans_of_to_hom [unfold 5]

definition is_equiv_graded_iso [instance] [priority 1010] (φ : M₁ ≃gm M₂) (i : I) :
  is_equiv (φ i) :=
graded_iso.is_equiv_to_hom φ idp

definition isomorphism_of_graded_iso' [constructor] (φ : M₁ ≃gm M₂) {i j : I} (p : deg φ i = j) :
  M₁ i ≃lm M₂ j :=
isomorphism.mk (↘φ p) !graded_iso.is_equiv_to_hom

definition isomorphism_of_graded_iso [constructor] (φ : M₁ ≃gm M₂) (i : I) :
  M₁ i ≃lm M₂ (deg φ i) :=
isomorphism.mk (φ i) _

definition graded_iso_of_isomorphism [constructor] (d : I ≃ I) (φ : Πi, M₁ i ≃lm M₂ (d i)) :
  M₁ ≃gm M₂ :=
begin
  apply graded_iso.mk (graded_hom.mk d φ), apply to_is_equiv, intro i j p, induction p,
  exact to_is_equiv (equiv_of_isomorphism (φ i)),
end

definition graded_iso_of_eq [constructor] {M₁ M₂ : graded_module R I} (p : M₁ ~ M₂)
  : M₁ ≃gm M₂ :=
graded_iso_of_isomorphism erfl (λi, isomorphism_of_eq (p i))

-- definition graded_iso.MK [constructor] (d : I ≃ I) (fn : Πi, M₁ i →lm M₂ (d i))
--   : M₁ ≃gm M₂ :=
-- graded_iso.mk _ _ _ --d (λi j p, homomorphism_of_eq (ap M₂ p) ∘lm fn i)

definition isodeg [unfold 5] (φ : M₁ ≃gm M₂) : I ≃ I :=
equiv.mk (deg φ) _

definition graded_iso_to_lminv [constructor] (φ : M₁ ≃gm M₂) : M₂ →gm M₁ :=
graded_hom.mk (deg φ)⁻¹
  abstract begin
    intro i, apply to_lminv,
    apply isomorphism_of_graded_iso' φ,
    apply to_right_inv (isodeg φ) i
  end end

definition to_gminv [constructor] (φ : M₁ ≃gm M₂) : M₂ →gm M₁ :=
graded_hom.mk (deg φ)⁻¹
  abstract begin
    intro i, apply isomorphism.to_hom, symmetry,
    apply isomorphism_of_graded_iso' φ,
    apply to_right_inv (isodeg φ) i
  end end

variable (M)
definition graded_iso.refl [refl] [constructor] : M ≃gm M :=
graded_iso_of_isomorphism equiv.rfl (λi, isomorphism.rfl)
variable {M}

definition graded_iso.rfl [refl] [constructor] : M ≃gm M := graded_iso.refl M

definition graded_iso.symm [symm] [constructor] (φ : M₁ ≃gm M₂) : M₂ ≃gm M₁ :=
graded_iso.mk (to_gminv φ) !is_equiv_inv
  (λi j p, @is_equiv_compose _ _ _ _ _ !isomorphism.is_equiv_to_hom !is_equiv_cast)

definition graded_iso.trans [trans] [constructor] (φ : M₁ ≃gm M₂) (ψ : M₂ ≃gm M₃) : M₁ ≃gm M₃ :=
graded_iso_of_isomorphism (isodeg φ ⬝e isodeg ψ)
  (λi, isomorphism_of_graded_iso φ i ⬝lm isomorphism_of_graded_iso ψ (deg φ i))

definition graded_iso.eq_trans [trans] [constructor]
   {M₁ M₂ : graded_module R I} {M₃ : graded_module R I} (φ : M₁ ~ M₂) (ψ : M₂ ≃gm M₃) : M₁ ≃gm M₃ :=
proof graded_iso.trans (graded_iso_of_eq φ) ψ qed

definition graded_iso.trans_eq [trans] [constructor]
  {M₁ : graded_module R I} {M₂ M₃ : graded_module R I} (φ : M₁ ≃gm M₂) (ψ : M₂ ~ M₃) : M₁ ≃gm M₃ :=
graded_iso.trans φ (graded_iso_of_eq ψ)

postfix `⁻¹ᵍᵐ`:(max + 1) := graded_iso.symm
infixl ` ⬝gm `:75 := graded_iso.trans
infixl ` ⬝gmp `:75 := graded_iso.trans_eq
infixl ` ⬝pgm `:75 := graded_iso.eq_trans

definition graded_hom_of_eq [constructor] {M₁ M₂ : graded_module R I} (p : M₁ ~ M₂)
  : M₁ →gm M₂ :=
graded_iso_of_eq p

/- direct sum of graded R-modules -/

variables {J : Set} (N : graded_module R J)
definition dirsum' : AddAbGroup :=
group.dirsum (λj, AddAbGroup_of_LeftModule (N j))
variable {N}
definition dirsum_smul [constructor] (r : R) : dirsum' N →g dirsum' N :=
dirsum_functor (λi, smul_homomorphism (N i) r)

definition dirsum_smul_right_distrib (r s : R) (n : dirsum' N) :
  dirsum_smul (r + s) n = dirsum_smul r n + dirsum_smul s n :=
begin
  refine dirsum_functor_homotopy _ n ⬝ !dirsum_functor_add⁻¹,
  intro i ni, exact to_smul_right_distrib r s ni
end

definition dirsum_mul_smul (r s : R) (n : dirsum' N) :
  dirsum_smul (r * s) n = dirsum_smul r (dirsum_smul s n) :=
begin
  refine dirsum_functor_homotopy _ n ⬝ !dirsum_functor_compose⁻¹,
  intro i ni, exact to_mul_smul r s ni
end

definition dirsum_one_smul (n : dirsum' N) : dirsum_smul 1 n = n :=
begin
  refine dirsum_functor_homotopy _ n ⬝ !dirsum_functor_gid,
  intro i ni, exact to_one_smul ni
end

definition dirsum : LeftModule R :=
LeftModule_of_AddAbGroup (dirsum' N) (λr n, dirsum_smul r n) (λr, homomorphism.addstruct (dirsum_smul r))
  dirsum_smul_right_distrib
  dirsum_mul_smul
  dirsum_one_smul

/- exact couples -/

definition is_exact_gmod (f : M₁ →gm M₂) (f' : M₂ →gm M₃) : Type :=
Π{i j k} (p : deg f i = j) (q : deg f' j = k), is_exact_mod (↘f p) (↘f' q)

structure exact_couple (M₁ M₂ : graded_module R I) : Type :=
  (i : M₁ →gm M₁) (j : M₁ →gm M₂) (k : M₂ →gm M₁)
  (exact_ij : is_exact_gmod i j)
  (exact_jk : is_exact_gmod j k)
  (exact_ki : is_exact_gmod k i)

  variables {i : M₁ →gm M₁} {j : M₁ →gm M₂} {k : M₂ →gm M₁}
            (exact_ij : is_exact_gmod i j)
            (exact_jk : is_exact_gmod j k)
            (exact_ki : is_exact_gmod k i)

  namespace derived_couple

  definition d : M₂ →gm M₂ := j ∘gm k

  end derived_couple


end left_module
