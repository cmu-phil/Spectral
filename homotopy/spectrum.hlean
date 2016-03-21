/-
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman

-/

import init.equiv types.nat types.pointed types.int types.pointed2 homotopy.susp types.fiber algebra.homotopy_group types.trunc
open eq pointed nat pmap susp phomotopy sigma is_equiv equiv homotopy fiber int algebra trunc trunc_index

/---------------------
  Basic definitions
  ---------------------/

/- I gather from looking at other files that I should be using
namespaces somehow here, but I don't really understand the conventions
for how to use them.  -/

structure prespectrum :=
  (deloop : ℕ → Type*)
  (glue : Πn, (deloop n) →* (Ω (deloop (succ n))))

open prespectrum
attribute prespectrum.deloop [coercion]

structure is_spectrum [class] (E : prespectrum) :=
  (is_equiv_glue : Πn, is_equiv (glue E n))

open is_spectrum

attribute is_equiv_glue [instance]

definition equiv_glue (E : prespectrum) [H : is_spectrum E] (n:ℕ) : (E n) ≃* (Ω (E (succ n))) := 
  pequiv_of_pmap (glue E n) (is_equiv_glue E n)

structure spectrum :=
  (to_prespectrum : prespectrum)
  (to_is_spectrum : is_spectrum to_prespectrum)

open spectrum

attribute spectrum.to_prespectrum [coercion]
attribute spectrum.to_is_spectrum [instance]

/- Spectrum maps -/
structure smap (E F : prespectrum) :=
  (to_fun : Πn, E n →* F n)
  (glue_square : Πn, glue F n ∘* to_fun n ~* Ω→ (to_fun (succ n)) ∘* glue E n)

open smap
infix ` →ₛ `:30 := smap

attribute smap.to_fun [coercion]

definition scompose {X Y Z : prespectrum} (g : Y →ₛ Z) (f : X →ₛ Y) : X →ₛ Z :=
  smap.mk (λn, g n ∘* f n)
    (λn, calc glue Z n ∘* to_fun g n ∘* to_fun f n
           ~* (glue Z n ∘* to_fun g n) ∘* to_fun f n                 : passoc
       ... ~* (Ω→(to_fun g (succ n)) ∘* glue Y n) ∘* to_fun f n      : pwhisker_right (to_fun f n) (glue_square g n)
       ... ~* Ω→(to_fun g (succ n)) ∘* (glue Y n ∘* to_fun f n)      : passoc
       ... ~* Ω→(to_fun g (succ n)) ∘* (Ω→ (f (succ n)) ∘* glue X n) : pwhisker_left Ω→(to_fun g (succ n)) (glue_square f n)
       ... ~* (Ω→(to_fun g (succ n)) ∘* Ω→(f (succ n))) ∘* glue X n  : passoc
       ... ~* Ω→(to_fun g (succ n) ∘* to_fun f (succ n)) ∘* glue X n : pwhisker_right (glue X n) (ap1_compose _ _))

infixr ` ∘ₛ `:60 := scompose

/- Suspension prespectra -/

definition psp_suspn : ℕ →  Type* → Type*
| psp_suspn 0 X        := X
| psp_suspn (succ n) X := psusp (psp_suspn n X)

definition psp_susp_oo (X : Type*) :=
  prespectrum.mk (λn, psp_suspn n X) (λn, loop_susp_unit (psp_suspn n X))

/- Truncations -/

definition inc (n : ℕ) (k : ℕ₋₂) : ℕ₋₂ :=
  nat.rec_on n k (λa, λm, succ m)

definition strunc (k : ℕ₋₂) (E : spectrum) : spectrum :=
  spectrum.mk (prespectrum.mk (λn, ptrunc (inc n k) (E n))
    (λn, (loop_ptrunc_pequiv (inc n k) (E (succ n)))⁻¹ᵉ* ∘* (ptrunc_pequiv_ptrunc (inc n k) (equiv_glue E n))))
    -- typeclass inference is failing me
    (is_spectrum.mk (λn, @is_equiv_compose _ _ _ _ (loop_ptrunc_pequiv (inc n k) (E (succ n)))⁻¹ᵉ* _ (pequiv.to_is_equiv _)))

/---------------------
  Homotopy groups
 ---------------------/

/- A spectrum has homotopy groups indexed by all integers.  The naive
definition would be

match n with
| neg_succ_of_nat k := π[0] (E (1+k))
| of_nat k          := π[k] (E 0)
end

but in order to ensure easily that they are all abelian groups, we
start shifting out earlier.  Since homotopy groups commute
appropriately with loop spaces, this is equivalent.
-/
definition shomotopy_group [constructor] (n : ℤ) (E : spectrum) : CommGroup :=
match n with
| neg_succ_of_nat k      := πag[0+2] (E (3 + k))
| of_nat 0               := πag[0+2] (E 2)
| of_nat 1               := πag[0+2] (E 1)
| of_nat (succ (succ k)) := πag[k+2] (E 0)
end

notation `πₛ[`:95  n:0    `] `:0 E:95 := shomotopy_group n E

/---------------------
  More pointed stuff
---------------------/

/- Most of this stuff should really be in one of the "pointed" files. -/

definition pmap.sigma_char [constructor] {A B : Type*} : (A →* B) ≃ Σ(f : A → B), f pt = pt :=
begin
  fapply equiv.mk,
  { intros f, exact ⟨to_fun f , resp_pt f⟩ },
  fapply is_equiv.adjointify,
  { intros f, cases f with f p, exact pmap.mk f p },
  { intros f, cases f with f p, esimp },
  { intros f, cases f with f p, esimp }
end

definition phomotopy.sigma_char [constructor] {A B : Type*} (f g : A →* B) : (f ~* g) ≃ Σ(p : f ~ g), p pt ⬝ resp_pt g = resp_pt f :=
begin
  fapply equiv.mk,
  { intros h, exact ⟨homotopy h , homotopy_pt h⟩ },
  fapply is_equiv.adjointify,
  { intros h, cases h with h p, exact phomotopy.mk h p },
  { intros h, cases h with h p, esimp },
  { intros h, cases h with h p, esimp }
end

-- I couldn't find the bundled version of is_equiv_ap anywhere.  What should it be named?  Apparently equiv.equiv_ap is something different?
definition my_equiv_ap {A B : Type} (f : A → B) [H : is_equiv f] (x y : A) : (x = y) ≃ (f x = f y) :=
  equiv.mk (ap f) _

-- should be in types.sigma
definition sigma_equiv_sigma_left' [constructor] {A A' : Type} {B : A' → Type} (Hf : A ≃ A') : (Σa, B (Hf a)) ≃ (Σa', B a') :=
  sigma_equiv_sigma Hf (λa, erfl)

definition pmap_eq_equiv {A B : Type*} (f g : A →* B) : (f = g) ≃ (f ~* g) :=
  calc (f = g) ≃ pmap.sigma_char f = pmap.sigma_char g
                 : my_equiv_ap pmap.sigma_char f g
          ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), pathover (λh, h pt = pt) (resp_pt f) p (resp_pt g)
                 : sigma_eq_equiv _ _
          ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), resp_pt f = ap (λh, h pt) p ⬝ resp_pt g
                 : sigma_equiv_sigma_right (λp, pathover_eq_equiv_Fl p (resp_pt f) (resp_pt g))
          ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), resp_pt f = ap10 p pt ⬝ resp_pt g
                 : sigma_equiv_sigma_right (λp, equiv_eq_closed_right _ (whisker_right (ap_eq_ap10 p _) _))
          ...  ≃ Σ(p : pmap.to_fun f ~ pmap.to_fun g), resp_pt f = p pt ⬝ resp_pt g
                 : sigma_equiv_sigma_left' eq_equiv_homotopy
          ...  ≃ Σ(p : pmap.to_fun f ~ pmap.to_fun g), p pt ⬝ resp_pt g = resp_pt f
                 : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
          ...  ≃ (f ~* g) : phomotopy.sigma_char f g

definition loop_pmap_commute (A B : Type*) : Ω(ppmap A B) ≃* (ppmap A (Ω B)) :=
  pequiv_of_equiv
    (calc Ω(ppmap A B) /- ≃ (pconst A B = pconst A B)                        : erfl
                   ... -/ ≃ (pconst A B ~* pconst A B)                       : pmap_eq_equiv _ _
                   ...    ≃ Σ(p : pconst A B ~ pconst A B), p pt ⬝ rfl = rfl : phomotopy.sigma_char
                   ... /- ≃ Σ(f : A → Ω B), f pt = pt                        : erfl
                   ... -/ ≃ (A →* Ω B)                                       : pmap.sigma_char)
    (by esimp)

definition ppcompose_left {A B C : Type*} (g : B →* C) : ((ppmap A B) →* (ppmap A C)) :=
  pmap.mk (pcompose g) (eq_of_phomotopy (phomotopy.mk (λa, resp_pt g) (idp_con _)⁻¹))

definition is_equiv_ppcompose_left [instance] {A B C : Type*} (g : B →* C) [H : is_equiv g] : is_equiv (@ppcompose_left A B C g) :=
begin
  fapply is_equiv.adjointify,
  { exact (ppcompose_left (pequiv_of_pmap g H)⁻¹ᵉ*) },
  { intros f, esimp, apply eq_of_phomotopy,
    exact calc g ∘* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* f) ~* (g ∘* (pequiv_of_pmap g H)⁻¹ᵉ*) ∘* f : passoc _ _ _
                                                ... ~* pid _ ∘* f : pwhisker_right f (pright_inv (pequiv_of_pmap g H))
                                                ... ~* f : pid_comp f },
  { intros f, esimp, apply eq_of_phomotopy,
    exact calc (pequiv_of_pmap g H)⁻¹ᵉ* ∘* (g ∘* f) ~* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* g) ∘* f : passoc _ _ _
                                                ... ~* pid _ ∘* f : pwhisker_right f (pleft_inv (pequiv_of_pmap g H))
                                                ... ~* f : pid_comp f }
end

definition is_equiv_pcompose [instance] {A B C : Type*} (g : B →* C) (f : A →* B) [Hg : is_equiv g] [Hf : is_equiv f] : is_equiv (g ∘* f) :=
  (is_equiv_compose f g)

/-------------------------------
  Cotensor of spectra by types
-------------------------------/

definition psp_cotensor (A : Type*) (B : prespectrum) : prespectrum :=
  prespectrum.mk (λn, ppmap A (B n))
    (λn, (pequiv.to_pmap (loop_pmap_commute A (B (succ n)))⁻¹ᵉ*) ∘*
         (ppcompose_left (glue B n)))

definition is_spectrum_cotensor [instance] (A : Type*) (B : prespectrum) [H : is_spectrum B] : is_spectrum (psp_cotensor A B) :=
begin
  apply is_spectrum.mk, intros n, unfold psp_cotensor, esimp,
  -- typeclass inference is failing me...
  refine (@is_equiv_compose _ _ _ _ ((pequiv.to_fun (loop_pmap_commute A (B (succ n)))⁻¹ᵉ*)) _ _),
  apply is_equiv_ppcompose_left,
  apply pequiv.to_is_equiv
end

definition sp_cotensor (A : Type*) (B : spectrum) : spectrum :=
  spectrum.mk (psp_cotensor A B) _

/- Mapping spectra -/

/- Fibers and long exact sequences -/

/- Spectrification -/

/- Tensor by spaces -/

/- Smash product of spectra -/

/- Cofibers and stability -/
