/-
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman

-/

import types.int types.pointed2 types.trunc homotopy.susp algebra.homotopy_group .chain_complex
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

open succ_str

/- The basic definitions of spectra and prespectra make sense for any successor-structure. -/

structure gen_prespectrum (N : succ_str) :=
  (deloop : N → Type*)
  (glue : Π(n:N), (deloop n) →* (Ω (deloop (S n))))

attribute gen_prespectrum.deloop [coercion]

structure is_spectrum [class] {N : succ_str} (E : gen_prespectrum N) :=
  (is_equiv_glue : Πn, is_equiv (gen_prespectrum.glue E n))

attribute is_spectrum.is_equiv_glue [instance]

structure gen_spectrum (N : succ_str) :=
  (to_prespectrum : gen_prespectrum N)
  (to_is_spectrum : is_spectrum to_prespectrum)

attribute gen_spectrum.to_prespectrum [coercion]
attribute gen_spectrum.to_is_spectrum [instance]

-- Classically, spectra and prespectra use the successor structure +ℕ.
-- But we will use +ℤ instead, to reduce case analysis later on.

abbreviation spectrum := gen_spectrum +ℤ
abbreviation spectrum.mk := @gen_spectrum.mk +ℤ

namespace spectrum

  definition glue {{N : succ_str}} := @gen_prespectrum.glue N
  --definition glue := (@gen_prespectrum.glue +ℤ)
  definition equiv_glue {N : succ_str} (E : gen_prespectrum N) [H : is_spectrum E] (n:N) : (E n) ≃* (Ω (E (S n))) := 
    pequiv_of_pmap (glue E n) (is_spectrum.is_equiv_glue E n)

  -- Sometimes an ℕ-indexed version does arise naturally, however, so
  -- we give a standard way to extend an ℕ-indexed (pre)spectrum to a
  -- ℤ-indexed one.

  definition psp_of_nat_indexed [constructor] (E : gen_prespectrum +ℕ) : gen_prespectrum +ℤ :=
    gen_prespectrum.mk
    (λ(n:ℤ), match n with
             | of_nat k          := E k
             | neg_succ_of_nat k := Ω[succ k] (E 0)
             end)
    begin
      intros n, cases n with n n: esimp,
      { exact (gen_prespectrum.glue E n) },
      cases n with n,
      { exact (pid _) },
      { exact (pid _) }
    end

  definition is_spectrum_of_nat_indexed [instance] (E : gen_prespectrum +ℕ) [H : is_spectrum E] : is_spectrum (psp_of_nat_indexed E) :=
  begin
    apply is_spectrum.mk, intros n, cases n with n n: esimp,
    { apply is_spectrum.is_equiv_glue },
    cases n with n: apply is_equiv_id
  end

  protected definition of_nat_indexed (E : gen_prespectrum +ℕ) [H : is_spectrum E] : spectrum
  := spectrum.mk (psp_of_nat_indexed E) (is_spectrum_of_nat_indexed E)

  -- In fact, a (pre)spectrum indexed on any pointed successor structure
  -- gives rise to one indexed on +ℕ, so in this sense +ℤ is a
  -- "universal" successor structure for indexing spectra.

  definition succ_str.of_nat {N : succ_str} (z : N) : ℕ → N
  | succ_str.of_nat zero   := z
  | succ_str.of_nat (succ k) := S (succ_str.of_nat k)

  definition psp_of_gen_indexed [constructor] {N : succ_str} (z : N) (E : gen_prespectrum N) : gen_prespectrum +ℤ :=
    psp_of_nat_indexed (gen_prespectrum.mk (λn, E (succ_str.of_nat z n)) (λn, gen_prespectrum.glue E (succ_str.of_nat z n)))

  definition is_spectrum_of_gen_indexed [instance] {N : succ_str} (z : N) (E : gen_prespectrum N) [H : is_spectrum E]
  : is_spectrum (psp_of_gen_indexed z E) :=
  begin
    apply is_spectrum_of_nat_indexed, apply is_spectrum.mk, intros n, esimp, apply is_spectrum.is_equiv_glue
  end

  protected definition of_gen_indexed [constructor] {N : succ_str} (z : N) (E : gen_spectrum N) : spectrum :=
    spectrum.mk (psp_of_gen_indexed z E) (is_spectrum_of_gen_indexed z E)

  -- Generally it's easiest to define a spectrum by giving 'equiv's
  -- directly.  This works for any indexing succ_str.
  protected definition MK {N : succ_str} (deloop : N → Type*) (glue : Π(n:N), (deloop n) ≃* (Ω (deloop (S n)))) : gen_spectrum N :=
    gen_spectrum.mk (gen_prespectrum.mk deloop (λ(n:N), glue n))
    (begin
      apply is_spectrum.mk, intros n, esimp,
      apply pequiv.to_is_equiv  -- Why doesn't typeclass inference find this?
    end)

  -- Finally, we combine them and give a way to produce a (ℤ-)spectrum from a ℕ-indexed family of 'equiv's.
  protected definition Mk (deloop : ℕ → Type*) (glue : Π(n:ℕ), (deloop n) ≃* (Ω (deloop (nat.succ n)))) : spectrum :=
    spectrum.of_nat_indexed (spectrum.MK deloop glue)

  -- (Pre)spectrum maps.  These make sense for any succ_str.
  structure smap {N : succ_str} (E F : gen_prespectrum N) :=
    (to_fun : Π(n:N), E n →* F n)
    (glue_square : Π(n:N), glue F n ∘* to_fun n ~* Ω→ (to_fun (S n)) ∘* glue E n)

  open smap
  infix ` →ₛ `:30 := smap

  attribute smap.to_fun [coercion]

  -- A version of 'glue_square' in the spectrum case that uses 'equiv_glue'
  definition sglue_square {N : succ_str} {E F : gen_spectrum N} (f : E →ₛ F) (n : N)
    : equiv_glue F n ∘* f n ~* Ω→ (f (S n)) ∘* equiv_glue E n
    -- I guess this is necessary because structures lack definitional eta?
    := phomotopy.mk (glue_square f n) (to_homotopy_pt (glue_square f n))

  definition scompose {N : succ_str} {X Y Z : gen_prespectrum N} (g : Y →ₛ Z) (f : X →ₛ Y) : X →ₛ Z :=
    smap.mk (λn, g n ∘* f n)
      (λn, calc glue Z n ∘* to_fun g n ∘* to_fun f n
             ~* (glue Z n ∘* to_fun g n) ∘* to_fun f n                 : passoc
         ... ~* (Ω→(to_fun g (S n)) ∘* glue Y n) ∘* to_fun f n      : pwhisker_right (to_fun f n) (glue_square g n)
         ... ~* Ω→(to_fun g (S n)) ∘* (glue Y n ∘* to_fun f n)      : passoc
         ... ~* Ω→(to_fun g (S n)) ∘* (Ω→ (f (S n)) ∘* glue X n) : pwhisker_left Ω→(to_fun g (S n)) (glue_square f n)
         ... ~* (Ω→(to_fun g (S n)) ∘* Ω→(f (S n))) ∘* glue X n  : passoc
         ... ~* Ω→(to_fun g (S n) ∘* to_fun f (S n)) ∘* glue X n : pwhisker_right (glue X n) (ap1_compose _ _))

  infixr ` ∘ₛ `:60 := scompose

  /- Suspension prespectra -/

  -- This should probably go in 'susp'
  definition psuspn : ℕ → Type* → Type*
  | psuspn 0 X          := X
  | psuspn (succ n) X   := psusp (psuspn n X)

  -- Suspension prespectra are one that's naturally indexed on the natural numbers
  definition psp_susp (X : Type*) : gen_prespectrum +ℕ :=
    gen_prespectrum.mk (λn, psuspn n X) (λn, loop_susp_unit (psuspn n X))

  /- Truncations -/

  -- We could truncate prespectra too, but since the operation
  -- preserves spectra and isn't "correct" acting on prespectra
  -- without spectrifying them first anyway, why bother?
  definition strunc (k : ℕ₋₂) (E : spectrum) : spectrum :=
    spectrum.Mk (λ(n:ℕ), ptrunc (k + n) (E n))
      (λ(n:ℕ), (loop_ptrunc_pequiv (k + n) (E (succ n)))⁻¹ᵉ*
               ∘*ᵉ (ptrunc_pequiv_ptrunc (k + n) (equiv_glue E (int.of_nat n))))

  /---------------------
    Homotopy groups
   ---------------------/

  -- Here we start to reap the rewards of using ℤ-indexing: we can
  -- read off the homotopy groups without any tedious case-analysis of
  -- n.  We increment by 2 in order to ensure that they are all
  -- automatically abelian groups.
  definition shomotopy_group [constructor] (n : ℤ) (E : spectrum) : CommGroup := πag[0+2] (E (2 + n))

  notation `πₛ[`:95  n:0    `] `:0 E:95 := shomotopy_group n E

  /-------------------------------
    Cotensor of spectra by types
  -------------------------------/

  -- Makes sense for any indexing succ_str.  Could be done for
  -- prespectra too, but as with truncation, why bother?
  definition sp_cotensor {N : succ_str} (A : Type*) (B : gen_spectrum N) : gen_spectrum N :=
    spectrum.MK (λn, ppmap A (B n))
      (λn, (loop_pmap_commute A (B (S n)))⁻¹ᵉ* ∘*ᵉ (equiv_ppcompose_left (equiv_glue B n)))

  /-----------------------------------------
    Fibers and long exact sequences
  -----------------------------------------/

  definition sfiber {N : succ_str} (E F : gen_spectrum N) (f : E →ₛ F) : gen_spectrum N :=
    spectrum.MK (λn, pfiber (f n))
      (λn, pfiber_loop_space (f (S n)) ∘*ᵉ pfiber_equiv_of_square (sglue_square f n))

  /- Mapping spectra -/

  /- Spectrification -/

  /- Tensor by spaces -/

  /- Smash product of spectra -/

  /- Cofibers and stability -/

end spectrum
