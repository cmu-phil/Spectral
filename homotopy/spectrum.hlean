/-
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman

-/

import types.int types.pointed2 types.trunc homotopy.susp algebra.homotopy_group
open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index

/-----------------------------------------
  Stuff that should go in other files
-----------------------------------------/

namespace sigma

  definition sigma_equiv_sigma_left' [constructor] {A A' : Type} {B : A' → Type} (Hf : A ≃ A') : (Σa, B (Hf a)) ≃ (Σa', B a') :=
    sigma_equiv_sigma Hf (λa, erfl)

end sigma
open sigma

namespace pointed

  definition pequiv_compose {A B C : Type*} (g : B ≃* C) (f : A ≃* B) : A ≃* C :=
    pequiv_of_pmap (g ∘* f) (is_equiv_compose f g)

  infixr ` ∘*ᵉ `:60 := pequiv_compose

  definition pmap.sigma_char [constructor] {A B : Type*} : (A →* B) ≃ Σ(f : A → B), f pt = pt :=
  begin
    fapply equiv.MK : intros f,
    { exact ⟨to_fun f , resp_pt f⟩ },
    all_goals cases f with f p,
    { exact pmap.mk f p },
    all_goals reflexivity
  end

  definition phomotopy.sigma_char [constructor] {A B : Type*} (f g : A →* B) : (f ~* g) ≃ Σ(p : f ~ g), p pt ⬝ resp_pt g = resp_pt f :=
  begin
    fapply equiv.MK : intros h,
    { exact ⟨h , to_homotopy_pt h⟩ },
    all_goals cases h with h p,
    { exact phomotopy.mk h p },
    all_goals reflexivity
  end

  definition pmap_eq_equiv {A B : Type*} (f g : A →* B) : (f = g) ≃ (f ~* g) :=
    calc (f = g) ≃ pmap.sigma_char f = pmap.sigma_char g
                   : eq_equiv_fn_eq pmap.sigma_char f g
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
      (by reflexivity)

  definition ppcompose_left {A B C : Type*} (g : B →* C) : ppmap A B →* ppmap A C :=
    pmap.mk (pcompose g) (eq_of_phomotopy (phomotopy.mk (λa, resp_pt g) (idp_con _)⁻¹))

  definition is_equiv_ppcompose_left [instance] {A B C : Type*} (g : B →* C) [H : is_equiv g] : is_equiv (@ppcompose_left A B C g) :=
  begin
    fapply is_equiv.adjointify,
    { exact (ppcompose_left (pequiv_of_pmap g H)⁻¹ᵉ*) },
    all_goals (intros f; esimp; apply eq_of_phomotopy),
    { exact calc g ∘* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* f) ~* (g ∘* (pequiv_of_pmap g H)⁻¹ᵉ*) ∘* f : passoc
                                                  ... ~* pid _ ∘* f : pwhisker_right f (pright_inv (pequiv_of_pmap g H))
                                                  ... ~* f : pid_comp f },
    { exact calc (pequiv_of_pmap g H)⁻¹ᵉ* ∘* (g ∘* f) ~* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* g) ∘* f : passoc
                                                  ... ~* pid _ ∘* f : pwhisker_right f (pleft_inv (pequiv_of_pmap g H))
                                                  ... ~* f : pid_comp f }
  end

  definition equiv_ppcompose_left {A B C : Type*} (g : B ≃* C) : ppmap A B ≃* ppmap A C :=
    pequiv_of_pmap (ppcompose_left g) _

  definition pfiber_loop_space {A B : Type*} (f : A →* B) : pfiber (Ω→ f) ≃* Ω (pfiber f) :=
    pequiv_of_equiv
    (calc pfiber (Ω→ f) ≃ Σ(p : Point A = Point A), ap1 f p = rfl                                : (fiber.sigma_char (ap1 f) (Point Ω B))
                    ... ≃ Σ(p : Point A = Point A), (respect_pt f) = ap f p ⬝ (respect_pt f)      : (sigma_equiv_sigma_right (λp,
                              calc (ap1 f p = rfl) ≃ !respect_pt⁻¹ ⬝ (ap f p ⬝ !respect_pt) = rfl : equiv_eq_closed_left _ (con.assoc _ _ _)
                                               ... ≃ ap f p ⬝ (respect_pt f) = (respect_pt f)     : eq_equiv_inv_con_eq_idp
                                               ... ≃ (respect_pt f) = ap f p ⬝ (respect_pt f)     : eq_equiv_eq_symm))
                    ... ≃ fiber.mk (Point A) (respect_pt f) = fiber.mk pt (respect_pt f)          : fiber_eq_equiv
                    ... ≃ Ω (pfiber f)                                                            : erfl)
    (begin cases f with f p, cases A with A a, cases B with B b, esimp at p, esimp at f, induction p, reflexivity end)

  definition pfiber_equiv_of_phomotopy {A B : Type*} {f g : A →* B} (h : f ~* g) : pfiber f ≃* pfiber g :=
  begin
    fapply pequiv_of_equiv,
    { refine (fiber.sigma_char f pt ⬝e _ ⬝e (fiber.sigma_char g pt)⁻¹ᵉ),
      apply sigma_equiv_sigma_right, intros a,
      apply equiv_eq_closed_left, apply (to_homotopy h) },
    { refine (fiber_eq rfl _),
      change (h pt)⁻¹ ⬝ respect_pt f = idp ⬝ respect_pt g,
      rewrite idp_con, apply inv_con_eq_of_eq_con, symmetry, exact (to_homotopy_pt h) }
  end

  definition transport_fiber_equiv {A B : Type} (f : A → B) {b1 b2 : B} (p : b1 = b2) : fiber f b1 ≃ fiber f b2 :=
    calc fiber f b1 ≃ Σa, f a = b1 : fiber.sigma_char
               ...  ≃ Σa, f a = b2 : sigma_equiv_sigma_right (λa, equiv_eq_closed_right (f a) p)
               ...  ≃ fiber f b2   : fiber.sigma_char

  definition pequiv_postcompose {A B B' : Type*} (f : A →* B) (g : B ≃* B') : pfiber (g ∘* f) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp, 
    refine ((transport_fiber_equiv (g ∘* f) (respect_pt g)⁻¹) ⬝e (@fiber.equiv_postcompose A B f (Point B) B' g _)),
    -- change (eq_equiv_fn_eq g _ _)⁻¹ ((ap g (respect_pt f) ⬝ respect_pt g) ⬝ (respect_pt g)⁻¹) = respect_pt f,
    exact sorry
  end
    
  definition pfiber_equiv_of_square {A B C D : Type*} {f : A →* B} {g : C →* D} {h : A ≃* C} {k : B ≃* D} (s : k ∘* f ~* g ∘* h)
    : pfiber f ≃* pfiber g :=
    calc pfiber f ≃* pfiber (k ∘* f) : /- fiber.equiv_postcompose; need a pointed version (WIP above) -/ sorry
              ... ≃* pfiber (g ∘* h) : pfiber_equiv_of_phomotopy s
              ... ≃* pfiber g : /- fiber.equiv_precompose -/ sorry

end pointed
open pointed

/---------------------
  Basic definitions
  ---------------------/

structure prespectrum :=
  (deloop : ℕ → Type*)
  (glue : Πn, (deloop n) →* (Ω (deloop (succ n))))

attribute prespectrum.deloop [coercion]

structure is_spectrum [class] (E : prespectrum) :=
  (is_equiv_glue : Πn, is_equiv (prespectrum.glue E n))

attribute is_spectrum.is_equiv_glue [instance]

definition equiv_glue (E : prespectrum) [H : is_spectrum E] (n:ℕ) : (E n) ≃* (Ω (E (succ n))) := 
  pequiv_of_pmap (prespectrum.glue E n) _

structure spectrum :=
  (to_prespectrum : prespectrum)
  (to_is_spectrum : is_spectrum to_prespectrum)

attribute spectrum.to_prespectrum [coercion]
attribute spectrum.to_is_spectrum [instance]

namespace spectrum

  abbreviation glue := prespectrum.glue

  -- An easy way to define a spectrum.
  definition MK (deloop : ℕ → Type*) (glue : Πn, (deloop n) ≃* (Ω (deloop (succ n)))) : spectrum :=
    spectrum.mk (prespectrum.mk deloop (λn, glue n)) (is_spectrum.mk (λn, _))

  /- Spectrum maps -/
  structure smap (E F : prespectrum) :=
    (to_fun : Πn, E n →* F n)
    (glue_square : Πn, glue F n ∘* to_fun n ~* Ω→ (to_fun (succ n)) ∘* glue E n)

  open smap
  infix ` →ₛ `:30 := smap

  attribute smap.to_fun [coercion]

  definition sglue_square {E F : spectrum} (f : E →ₛ F) (n : ℕ)
    : equiv_glue F n ∘* f n ~* Ω→ (f (succ n)) ∘* equiv_glue E n
    := glue_square f n

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

  definition strunc (k : ℕ₋₂) (E : spectrum) : spectrum :=
    spectrum.MK (λ(n:ℕ), ptrunc (k + n) (E n))
      (λ(n:ℕ), (loop_ptrunc_pequiv (k + n) (E (succ n)))⁻¹ᵉ* ∘*ᵉ (ptrunc_pequiv_ptrunc (k + n) (equiv_glue E n)))

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

  /-------------------------------
    Cotensor of spectra by types
  -------------------------------/

  definition sp_cotensor (A : Type*) (B : spectrum) : spectrum :=
    spectrum.MK (λn, ppmap A (B n))
      (λn, (loop_pmap_commute A (B (succ n)))⁻¹ᵉ* ∘*ᵉ (equiv_ppcompose_left (equiv_glue B n)))

  /-----------------------------------------
    Fibers and long exact sequences
  -----------------------------------------/

  definition sfiber (E F : spectrum) (f : E →ₛ F) : spectrum :=
    spectrum.MK (λn, pfiber (f n))
      (λn, pfiber_loop_space (f (succ n)) ∘*ᵉ pfiber_equiv_of_square (sglue_square f n))

  /- Mapping spectra -/

  /- Spectrification -/

  /- Tensor by spaces -/

  /- Smash product of spectra -/

  /- Cofibers and stability -/

end spectrum
