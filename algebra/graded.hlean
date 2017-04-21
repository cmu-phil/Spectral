/- Graded (left-) R-modules for a ring R. -/

-- Author: Floris van Doorn

import .left_module .direct_sum .submodule

open algebra eq left_module pointed function equiv is_equiv is_trunc prod group sigma

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

definition graded_hom_of_deg (d : I ≃ I) (M₁ M₂ : graded_module R I) : Type :=
Π⦃i j : I⦄ (p : d i = j), M₁ i →lm M₂ j

definition gmd_constant [constructor] (d : I ≃ I) (M₁ M₂ : graded_module R I) : graded_hom_of_deg d M₁ M₂ :=
λi j p, lm_constant (M₁ i) (M₂ j)

definition gmd0 [constructor] {d : I ≃ I} {M₁ M₂ : graded_module R I} : graded_hom_of_deg d M₁ M₂ :=
gmd_constant d M₁ M₂

structure graded_hom (M₁ M₂ : graded_module R I) : Type :=
mk' ::  (d : I ≃ I)
        (fn' : graded_hom_of_deg d M₁ M₂)

notation M₁ ` →gm ` M₂ := graded_hom M₁ M₂

abbreviation deg [unfold 5] := @graded_hom.d
postfix ` ↘`:(max+10) := graded_hom.fn' -- there is probably a better character for this? Maybe ↷?

definition graded_hom_fn [reducible] [unfold 5] [coercion] (f : M₁ →gm M₂) (i : I) : M₁ i →lm M₂ (deg f i) :=
f ↘ idp

definition graded_hom_fn_in [reducible] [unfold 5] (f : M₁ →gm M₂) (i : I) : M₁ ((deg f)⁻¹ i) →lm M₂ i :=
f ↘ (to_right_inv (deg f) i)

infix ` ← `:101 := graded_hom_fn_in -- todo: change notation

definition graded_hom.mk [constructor] {M₁ M₂ : graded_module R I} (d : I ≃ I)
  (fn : Πi, M₁ i →lm M₂ (d i)) : M₁ →gm M₂ :=
graded_hom.mk' d (λi j p, homomorphism_of_eq (ap M₂ p) ∘lm fn i)

definition graded_hom.mk_in [constructor] {M₁ M₂ : graded_module R I} (d : I ≃ I)
  (fn : Πi, M₁ (d⁻¹ i) →lm M₂ i) : M₁ →gm M₂ :=
graded_hom.mk' d (λi j p, fn j ∘lm homomorphism_of_eq (ap M₁ (eq_inv_of_eq p)))

definition graded_hom.mk_out_in [constructor] {M₁ M₂ : graded_module R I} (d₁ : I ≃ I) (d₂ : I ≃ I)
  (fn : Πi, M₁ (d₁ i) →lm M₂ (d₂ i)) : M₁ →gm M₂ :=
graded_hom.mk' (d₁⁻¹ᵉ ⬝e d₂) (λi j p, homomorphism_of_eq (ap M₂ p) ∘lm fn (d₁⁻¹ᵉ i) ∘lm
  homomorphism_of_eq (ap M₁ (to_right_inv d₁ i)⁻¹))

definition graded_hom_eq_transport (f : M₁ →gm M₂) {i j : I} (p : deg f i = j) (m : M₁ i) :
  f ↘ p m = transport M₂ p (f i m) :=
by induction p; reflexivity

definition graded_hom_eq_zero {f : M₁ →gm M₂} {i j k : I} {q : deg f i = j} {p : deg f i = k}
  (m : M₁ i) (r : f ↘ q m = 0) : f ↘ p m = 0 :=
have f ↘ p m = transport M₂ (q⁻¹ ⬝ p) (f ↘ q m), begin induction p, induction q, reflexivity end,
this ⬝ ap (transport M₂ (q⁻¹ ⬝ p)) r ⬝ tr_eq_of_pathover (apd (λi, 0) (q⁻¹ ⬝ p))

variables {f' : M₂ →gm M₃} {f g : M₁ →gm M₂}

definition graded_hom_compose [constructor] (f' : M₂ →gm M₃) (f : M₁ →gm M₂) : M₁ →gm M₃ :=
graded_hom.mk (deg f ⬝e deg f') (λi, f' (deg f i) ∘lm f i)

infixr ` ∘gm `:75 := graded_hom_compose

definition graded_hom_compose_fn (f' : M₂ →gm M₃) (f : M₁ →gm M₂) (i : I) (m : M₁ i) :
  (f' ∘gm f) i m = f' (deg f i) (f i m) :=
proof idp qed

variable (M)
definition graded_hom_id [constructor] [refl] : M →gm M :=
graded_hom.mk erfl (λi, lmid)
variable {M}
abbreviation gmid [constructor] := graded_hom_id M

definition gm_constant [constructor] (M₁ M₂ : graded_module R I) (d : I ≃ I) : M₁ →gm M₂ :=
graded_hom.mk' d (gmd_constant d M₁ M₂)

structure graded_iso (M₁ M₂ : graded_module R I) : Type :=
mk' :: (to_hom : M₁ →gm M₂)
       (is_equiv_to_hom : Π⦃i j⦄ (p : deg to_hom i = j), is_equiv (to_hom ↘ p))

infix ` ≃gm `:25 := graded_iso
attribute graded_iso.to_hom [coercion]
attribute graded_iso._trans_of_to_hom [unfold 5]

definition is_equiv_graded_iso [instance] [priority 1010] (φ : M₁ ≃gm M₂) (i : I) :
  is_equiv (φ i) :=
graded_iso.is_equiv_to_hom φ idp

definition isomorphism_of_graded_iso' [constructor] (φ : M₁ ≃gm M₂) {i j : I} (p : deg φ i = j) :
  M₁ i ≃lm M₂ j :=
isomorphism.mk (φ ↘ p) !graded_iso.is_equiv_to_hom

definition isomorphism_of_graded_iso [constructor] (φ : M₁ ≃gm M₂) (i : I) :
  M₁ i ≃lm M₂ (deg φ i) :=
isomorphism.mk (φ i) _

definition isomorphism_of_graded_iso_in [constructor] (φ : M₁ ≃gm M₂) (i : I) :
  M₁ ((deg φ)⁻¹ i) ≃lm M₂ i :=
isomorphism_of_graded_iso' φ !to_right_inv

protected definition graded_iso.mk [constructor] (d : I ≃ I) (φ : Πi, M₁ i ≃lm M₂ (d i)) :
  M₁ ≃gm M₂ :=
begin
  apply graded_iso.mk' (graded_hom.mk d φ),
  intro i j p, induction p,
  exact to_is_equiv (equiv_of_isomorphism (φ i)),
end

protected definition graded_iso.mk_in [constructor] (d : I ≃ I) (φ : Πi, M₁ (d⁻¹ i) ≃lm M₂ i) :
  M₁ ≃gm M₂ :=
begin
  apply graded_iso.mk' (graded_hom.mk_in d φ),
  intro i j p, esimp,
  exact @is_equiv_compose _ _ _ _ _ !is_equiv_cast _,
end

definition graded_iso_of_eq [constructor] {M₁ M₂ : graded_module R I} (p : M₁ ~ M₂)
  : M₁ ≃gm M₂ :=
graded_iso.mk erfl (λi, isomorphism_of_eq (p i))

-- definition to_gminv [constructor] (φ : M₁ ≃gm M₂) : M₂ →gm M₁ :=
-- graded_hom.mk_in (deg φ)⁻¹ᵉ
--   abstract begin
--     intro i, apply isomorphism.to_hom, symmetry,
--     apply isomorphism_of_graded_iso φ
--   end end

variable (M)
definition graded_iso.refl [refl] [constructor] : M ≃gm M :=
graded_iso.mk equiv.rfl (λi, isomorphism.rfl)
variable {M}

definition graded_iso.rfl [refl] [constructor] : M ≃gm M := graded_iso.refl M

definition graded_iso.symm [symm] [constructor] (φ : M₁ ≃gm M₂) : M₂ ≃gm M₁ :=
graded_iso.mk_in (deg φ)⁻¹ᵉ (λi, (isomorphism_of_graded_iso φ i)⁻¹ˡᵐ)

definition graded_iso.trans [trans] [constructor] (φ : M₁ ≃gm M₂) (ψ : M₂ ≃gm M₃) : M₁ ≃gm M₃ :=
graded_iso.mk (deg φ ⬝e deg ψ)
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

structure graded_homotopy (f g : M₁ →gm M₂) : Type :=
mk' :: (hd : deg f ~ deg g)
       (hfn : Π⦃i j : I⦄ (pf : deg f i = j) (pg : deg g i = j) (r : hd i ⬝ pg = pf), f ↘ pf ~ g ↘ pg)

infix ` ~gm `:50 := graded_homotopy

definition graded_homotopy.mk (hd : deg f ~ deg g) (hfn : Πi m, f i m =[hd i] g i m) : f ~gm g :=
graded_homotopy.mk' hd
  begin
    intro i j pf pg r m, induction r, induction pg, esimp,
    exact graded_hom_eq_transport f (hd i) m ⬝ tr_eq_of_pathover (hfn i m),
  end

definition graded_homotopy_of_deg (d : I ≃ I) (f g : graded_hom_of_deg d M₁ M₂) : Type :=
Π⦃i j : I⦄ (p : d i = j), f p ~ g p

notation f ` ~[`:50 d:0 `] `:0 g:50 := graded_homotopy_of_deg d f g

variables {d : I ≃ I} {f₁ f₂ : graded_hom_of_deg d M₁ M₂}
-- definition graded_homotopy_elim' [unfold 8] := @graded_homotopy_of_deg.elim'
-- definition graded_homotopy_elim [reducible] [unfold 8] [coercion] (h : f₁ ~[d] f₂) (i : I) :
--   f₁ (refl i) ~ f₂ (refl i) :=
-- graded_homotopy_elim' _ _

-- definition graded_homotopy_elim_in [reducible] [unfold 8] (f : M₁ →gm M₂) (i : I) : M₁ ((deg f)⁻¹ i) →lm M₂ i :=
-- f ↘ (to_right_inv (deg f) i)

definition graded_homotopy_of_deg.mk [constructor] (h : Πi, f₁ (idpath (d i)) ~ f₂ (idpath (d i))) :
  f₁ ~[d] f₂ :=
begin
  intro i j p, induction p, exact h i
end

-- definition graded_homotopy.mk_in [constructor] {M₁ M₂ : graded_module R I} (d : I ≃ I)
--   (fn : Πi, M₁ (d⁻¹ i) →lm M₂ i) : M₁ →gm M₂ :=
-- graded_hom.mk' d (λi j p, fn j ∘lm homomorphism_of_eq (ap M₁ (eq_inv_of_eq p)))
-- definition is_gconstant (f : M₁ →gm M₂) : Type :=
-- f↘ ~[deg f] gmd0

definition compose_constant (f' : M₂ →gm M₃) (f : M₁ →gm M₂) : Type :=
Π⦃i j k : I⦄ (p : deg f i = j) (q : deg f' j = k) (m : M₁ i), f' ↘ q (f ↘ p m) = 0

definition compose_constant.mk (h : Πi m, f' (deg f i) (f i m) = 0) : compose_constant f' f :=
by intros; induction p; induction q; exact h i m

definition compose_constant.elim (h : compose_constant f' f) (i : I) (m : M₁ i) : f' (deg f i) (f i m) = 0 :=
h idp idp m

definition is_gconstant (f : M₁ →gm M₂) : Type :=
Π⦃i j : I⦄ (p : deg f i = j) (m : M₁ i), f ↘ p m = 0

definition is_gconstant.mk (h : Πi m, f i m = 0) : is_gconstant f :=
by intros; induction p; exact h i m

definition is_gconstant.elim (h : is_gconstant f) (i : I) (m : M₁ i) : f i m = 0 :=
h idp m

/- direct sum of graded R-modules -/

variables {J : Set} (N : graded_module R J)
definition dirsum' : AddAbGroup :=
group.dirsum (λj, AddAbGroup_of_LeftModule (N j))
variable {N}
definition dirsum_smul [constructor] (r : R) : dirsum' N →a dirsum' N :=
dirsum_functor (λi, smul_homomorphism (N i) r)

definition dirsum_smul_right_distrib (r s : R) (n : dirsum' N) :
  dirsum_smul (r + s) n = dirsum_smul r n + dirsum_smul s n :=
begin
  refine dirsum_functor_homotopy _ n ⬝ !dirsum_functor_add⁻¹,
  intro i ni, exact to_smul_right_distrib r s ni
end

definition dirsum_mul_smul' (r s : R) (n : dirsum' N) :
  dirsum_smul (r * s) n = (dirsum_smul r ∘a dirsum_smul s) n :=
begin
  refine dirsum_functor_homotopy _ n ⬝ (dirsum_functor_compose _ _ n)⁻¹ᵖ,
  intro i ni, exact to_mul_smul r s ni
end

definition dirsum_mul_smul (r s : R) (n : dirsum' N) :
  dirsum_smul (r * s) n = dirsum_smul r (dirsum_smul s n) :=
proof dirsum_mul_smul' r s n qed

definition dirsum_one_smul (n : dirsum' N) : dirsum_smul 1 n = n :=
begin
  refine dirsum_functor_homotopy _ n ⬝ !dirsum_functor_gid,
  intro i ni, exact to_one_smul ni
end

definition dirsum : LeftModule R :=
LeftModule_of_AddAbGroup (dirsum' N) (λr n, dirsum_smul r n)
  (λr, homomorphism.addstruct (dirsum_smul r))
  dirsum_smul_right_distrib
  dirsum_mul_smul
  dirsum_one_smul

/- graded variants of left-module constructions -/

definition graded_submodule [constructor] (S : Πi, submodule_rel (M i)) : graded_module R I :=
λi, submodule (S i)

definition graded_submodule_incl [constructor] (S : Πi, submodule_rel (M i)) :
  graded_submodule S →gm M :=
graded_hom.mk erfl (λi, submodule_incl (S i))

definition graded_hom_lift [constructor] {S : Πi, submodule_rel (M₂ i)} (φ : M₁ →gm M₂)
  (h : Π(i : I) (m : M₁ i), S (deg φ i) (φ i m)) : M₁ →gm graded_submodule S :=
graded_hom.mk (deg φ) (λi, hom_lift (φ i) (h i))

definition graded_image (f : M₁ →gm M₂) : graded_module R I :=
λi, image_module (f ↘ (to_right_inv (deg f) i))

definition graded_image_lift [constructor] (f : M₁ →gm M₂) : M₁ →gm graded_image f :=
graded_hom.mk_in (deg f) (λi, image_lift (f ↘ (to_right_inv (deg f) i)))

definition graded_image_elim [constructor] {f : M₁ →gm M₂} (g : M₁ →gm M₃)
  (h : Π⦃i m⦄, f i m = 0 → g i m = 0) :
  graded_image f →gm M₃ :=
begin
  apply graded_hom.mk_out_in (deg f) (deg g),
  intro i,
  apply image_elim (g ↘ (ap (deg g) (to_left_inv (deg f) i))),
  intro m p,
  refine graded_hom_eq_zero m (h _),
  exact graded_hom_eq_zero m p
end

definition graded_quotient (S : Πi, submodule_rel (M i)) : graded_module R I :=
λi, quotient_module (S i)

definition graded_quotient_map [constructor] (S : Πi, submodule_rel (M i)) :
  M →gm graded_quotient S :=
graded_hom.mk erfl (λi, quotient_map (S i))

definition graded_homology (g : M₂ →gm M₃) (f : M₁ →gm M₂) : graded_module R I :=
λi, homology (g i) (f ↘ (to_right_inv (deg f) i))

definition graded_homology_elim {g : M₂ →gm M₃} {f : M₁ →gm M₂} (h : M₂ →gm M)
  (H : compose_constant h f) : graded_homology g f →gm M :=
graded_hom.mk (deg h) (λi, homology_elim (h i) (H _ _))


/- exact couples -/

definition is_exact_gmod (f : M₁ →gm M₂) (f' : M₂ →gm M₃) : Type :=
Π⦃i j k⦄ (p : deg f i = j) (q : deg f' j = k), is_exact_mod (f ↘ p) (f' ↘ q)

definition gmod_im_in_ker (h : is_exact_gmod f f') : compose_constant f' f :=
λi j k p q, is_exact.im_in_ker (h p q)

structure exact_couple (M₁ M₂ : graded_module R I) : Type :=
  (i : M₁ →gm M₁) (j : M₁ →gm M₂) (k : M₂ →gm M₁)
  (exact_ij : is_exact_gmod i j)
  (exact_jk : is_exact_gmod j k)
  (exact_ki : is_exact_gmod k i)

end left_module

namespace left_module
  namespace derived_couple
  section
  parameters {R : Ring} {I : Type} {D E : graded_module R I} {i : D →gm D} {j : D →gm E} {k : E →gm D}
            (exact_ij : is_exact_gmod i j)
            (exact_jk : is_exact_gmod j k)
            (exact_ki : is_exact_gmod k i)

  definition d : E →gm E := j ∘gm k
  definition D' : graded_module R I := graded_image i
  definition E' : graded_module R I := graded_homology d d
  definition i' : D' →gm D' := graded_image_lift i ∘gm graded_submodule_incl _
  include exact_jk exact_ki

  theorem j_lemma1 ⦃x : I⦄ (m : D x) : d ((deg j) x) (j x m) = 0 :=
  begin
    rewrite [graded_hom_compose_fn,↑d,graded_hom_compose_fn],
    refine ap (graded_hom_fn j (deg k (deg j x))) _ ⬝ !to_respect_zero,
    exact compose_constant.elim (gmod_im_in_ker exact_jk) x m
  end

  theorem j_lemma2 : Π⦃x : I⦄ ⦃m : D x⦄ (p : i x m = 0),
    (graded_quotient_map _ ∘gm graded_hom_lift j j_lemma1) x m = 0 :> E' _ :=
  begin
    have Π⦃x : I⦄ ⦃m : D (deg k x)⦄ (p : i (deg k x) m = 0), image (d x) (j (deg k x) m),
    begin
      intros,
      note m_in_im_k := is_exact.ker_in_im (exact_ki idp _) _ p,
      induction m_in_im_k with e q,
      induction q,
      apply image.mk e idp
    end,
    have Π⦃x : I⦄ ⦃m : D x⦄ (p : i x m = 0), image (d ← (deg j x)) (j x m),
    begin
      exact sorry
    end,
    intros,
    rewrite [graded_hom_compose_fn],
    exact quotient_map_eq_zero _ (this p)
  end

  definition j' : D' →gm E' :=
  graded_image_elim (!graded_quotient_map ∘gm graded_hom_lift j j_lemma1) j_lemma2

  definition k' : E' →gm D' :=
  graded_homology_elim (graded_image_lift i ∘gm k)
    abstract begin
      apply compose_constant.mk, intro x m,
      rewrite [graded_hom_compose_fn],
      refine ap (graded_hom_fn (graded_image_lift i) (deg k (deg d x))) _ ⬝ !to_respect_zero,
      exact compose_constant.elim (gmod_im_in_ker exact_jk) (deg k x) (k x m)
    end end

  end

  end derived_couple


end left_module
