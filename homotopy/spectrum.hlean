/-
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman, Floris van Doorn

-/

import types.int types.pointed types.trunc homotopy.susp algebra.homotopy_group homotopy.chain_complex cubical .splice homotopy.LES_of_homotopy_groups
open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group

/-----------------------------------------
  Stuff that should go in other files
-----------------------------------------/

attribute equiv.symm equiv.trans is_equiv.is_equiv_ap fiber.equiv_postcompose fiber.equiv_precompose pequiv.to_pmap pequiv._trans_of_to_pmap ghomotopy_group_succ_in isomorphism_of_eq [constructor]
attribute is_equiv.eq_of_fn_eq_fn' [unfold 3]
attribute isomorphism._trans_of_to_hom [unfold 3]
attribute homomorphism.struct [unfold 3]
attribute pequiv.trans pequiv.symm [constructor]

namespace sigma

  definition sigma_equiv_sigma_left' [constructor] {A A' : Type} {B : A' → Type} (Hf : A ≃ A') : (Σa, B (Hf a)) ≃ (Σa', B a') :=
    sigma_equiv_sigma Hf (λa, erfl)

end sigma
open sigma

namespace group
  open is_trunc
  definition pSet_of_Group (G : Group) : Set* := ptrunctype.mk G _ 1

  definition pmap_of_isomorphism [constructor] {G₁ G₂ : Group} (φ : G₁ ≃g G₂) :
    pType_of_Group G₁ →* pType_of_Group G₂ :=
  pequiv_of_isomorphism φ

  definition pequiv_of_isomorphism_of_eq {G₁ G₂ : Group} (p : G₁ = G₂) :
    pequiv_of_isomorphism (isomorphism_of_eq p) = pequiv_of_eq (ap pType_of_Group p) :=
  begin
    induction p,
    apply pequiv_eq,
    fapply pmap_eq,
    { intro g, reflexivity},
    { apply is_prop.elim}
  end

  definition homomorphism_change_fun [constructor] {G₁ G₂ : Group} (φ : G₁ →g G₂) (f : G₁ → G₂)
    (p : φ ~ f) : G₁ →g G₂ :=
  homomorphism.mk f (λg h, (p (g * h))⁻¹ ⬝ to_respect_mul φ g h ⬝ ap011 mul (p g) (p h))

end group open group

namespace pi -- move to types.arrow

  definition pmap_eq_idp {X Y : Type*} (f : X →* Y) :
    pmap_eq (λx, idpath (f x)) !idp_con⁻¹ = idpath f :=
  begin
    cases f with f p, esimp [pmap_eq],
    refine apd011 (apd011 pmap.mk) !eq_of_homotopy_idp _,
    exact sorry
  end

  definition pfunext [constructor] (X Y : Type*) : ppmap X (Ω Y) ≃* Ω (ppmap X Y) :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK: esimp,
      { intro f, fapply pmap_eq,
        { intro x, exact f x },
        { exact (respect_pt f)⁻¹ }},
      { intro p, fapply pmap.mk,
        { intro x, exact ap010 pmap.to_fun p x },
        { note z := apd respect_pt p,
          note z2 := square_of_pathover z,
          refine eq_of_hdeg_square z2 ⬝ !ap_constant }},
      { intro p, exact sorry },
      { intro p, exact sorry }},
    { apply pmap_eq_idp}
  end


end pi open pi

namespace eq

  definition pathover_eq_Fl' {A B : Type} {f : A → B} {a₁ a₂ : A} {b : B} (p : a₁ = a₂) (q : f a₂ = b) : (ap f p) ⬝ q =[p] q :=
  by induction p; induction q; exact idpo

end eq open eq

namespace pointed

  definition pequiv_compose {A B C : Type*} (g : B ≃* C) (f : A ≃* B) : A ≃* C :=
    pequiv_of_pmap (g ∘* f) (is_equiv_compose g f)

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
                   : sigma_equiv_sigma_right (λp, equiv_eq_closed_right _ (whisker_right (ap_eq_apd10 p _) _))
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

  definition pcompose_pconst {A B C : Type*} (f : B →* C) : f ∘* pconst A B ~* pconst A C :=
    phomotopy.mk (λa, respect_pt f) (idp_con _)⁻¹

  definition pconst_pcompose {A B C : Type*} (f : A →* B) : pconst B C ∘* f ~* pconst A C :=
    phomotopy.mk (λa, rfl) (ap_constant _ _)⁻¹

  definition ap1_pconst (A B : Type*) : Ω→(pconst A B) ~* pconst (Ω A) (Ω B) :=
    phomotopy.mk (λp, idp_con _ ⬝ ap_constant p pt) rfl

  definition pfiber_loop_space {A B : Type*} (f : A →* B) : pfiber (Ω→ f) ≃* Ω (pfiber f) :=
    pequiv_of_equiv
    (calc pfiber (Ω→ f) ≃ Σ(p : Point A = Point A), ap1 f p = rfl                                : (fiber.sigma_char (ap1 f) (Point (Ω B)))
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

  definition transport_fiber_equiv [constructor] {A B : Type} (f : A → B) {b1 b2 : B} (p : b1 = b2) : fiber f b1 ≃ fiber f b2 :=
    calc fiber f b1 ≃ Σa, f a = b1 : fiber.sigma_char
               ...  ≃ Σa, f a = b2 : sigma_equiv_sigma_right (λa, equiv_eq_closed_right (f a) p)
               ...  ≃ fiber f b2   : fiber.sigma_char

  definition pequiv_postcompose {A B B' : Type*} (f : A →* B) (g : B ≃* B') : pfiber (g ∘* f) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine transport_fiber_equiv (g ∘* f) (respect_pt g)⁻¹ ⬝e fiber.equiv_postcompose f g (Point B),
    esimp, apply (ap (fiber.mk (Point A))), refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
    rewrite [con.assoc, con.right_inv, con_idp, -ap_compose'], apply ap_con_eq_con
  end

  definition pequiv_precompose {A A' B : Type*} (f : A →* B) (g : A' ≃* A) : pfiber (f ∘* g) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine fiber.equiv_precompose f g (Point B),
    esimp, apply (eq_of_fn_eq_fn (fiber.sigma_char _ _)), fapply sigma_eq: esimp,
    { apply respect_pt g },
    { apply pathover_eq_Fl' }
  end

  definition pfiber_equiv_of_square {A B C D : Type*} {f : A →* B} {g : C →* D} {h : A ≃* C} {k : B ≃* D} (s : k ∘* f ~* g ∘* h)
    : pfiber f ≃* pfiber g :=
    calc pfiber f ≃* pfiber (k ∘* f) : pequiv_postcompose
              ... ≃* pfiber (g ∘* h) : pfiber_equiv_of_phomotopy s
              ... ≃* pfiber g : pequiv_precompose

  definition loop_ppi_commute {A : Type} (B : A → Type*) : Ω(ppi B) ≃* Π*a, Ω (B a) :=
    pequiv_of_equiv eq_equiv_homotopy rfl

  definition equiv_ppi_right {A : Type} {P Q : A → Type*} (g : Πa, P a ≃* Q a)
    : (Π*a, P a) ≃* (Π*a, Q a) :=
    pequiv_of_equiv (pi_equiv_pi_right g)
      begin esimp, apply eq_of_homotopy, intros a, esimp, exact (respect_pt (g a)) end

  definition pcast_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pcast (ap C p) ∘* f a₁ ~* f a₂ ∘* pcast (ap B p) :=
  phomotopy.mk
    begin induction p, reflexivity end
    begin induction p, esimp, refine !idp_con ⬝ !idp_con ⬝ !ap_id⁻¹ end

  definition pequiv_of_eq_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pequiv_of_eq (ap C p) ∘* f a₁ ~* f a₂ ∘* pequiv_of_eq (ap B p) :=
  pcast_commute f p

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

  ------------------------------
  -- Maps and homotopies of (pre)spectra
  ------------------------------

  -- These make sense for any succ_str.
  structure smap {N : succ_str} (E F : gen_prespectrum N) :=
    (to_fun : Π(n:N), E n →* F n)
    (glue_square : Π(n:N), glue F n ∘* to_fun n ~* Ω→ (to_fun (S n)) ∘* glue E n)

  open smap
  infix ` →ₛ `:30 := smap

  attribute smap.to_fun [coercion]

  -- A version of 'glue_square' in the spectrum case that uses 'equiv_glue'
  definition sglue_square {N : succ_str} {E F : gen_spectrum N} (f : E →ₛ F) (n : N)
    : equiv_glue F n ∘* f n ~* Ω→ (f (S n)) ∘* equiv_glue E n
    -- I guess this manual eta-expansion is necessary because structures lack definitional eta?
    := phomotopy.mk (glue_square f n) (to_homotopy_pt (glue_square f n))

  definition sid {N : succ_str} (E : gen_spectrum N) : E →ₛ E :=
    smap.mk (λn, pid (E n))
    (λn, calc glue E n ∘* pid (E n) ~* glue E n                   : comp_pid
                              ...   ~* pid (Ω(E (S n))) ∘* glue E n : pid_comp
                              ...   ~* Ω→(pid (E (S n))) ∘* glue E n : pwhisker_right (glue E n) ap1_id⁻¹*)

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

  definition szero {N : succ_str} (E F : gen_prespectrum N) : E →ₛ F :=
    smap.mk (λn, pconst (E n) (F n))
      (λn, calc glue F n ∘* pconst (E n) (F n) ~* pconst (E n) (Ω(F (S n)))                    : pcompose_pconst
                                         ...   ~* pconst (Ω(E (S n))) (Ω(F (S n))) ∘* glue E n : pconst_pcompose
                                         ...   ~* Ω→(pconst (E (S n)) (F (S n))) ∘* glue E n   : pwhisker_right (glue E n) (ap1_pconst _ _))

  structure shomotopy {N : succ_str} {E F : gen_prespectrum N} (f g : E →ₛ F) :=
    (to_phomotopy : Πn, f n ~* g n)
    (glue_homotopy : Πn, pwhisker_left (glue F n) (to_phomotopy n) ⬝* glue_square g n
                         =      -- Ideally this should be a "phomotopy2"
                         glue_square f n ⬝* pwhisker_right (glue E n) (ap1_phomotopy (to_phomotopy (S n))))

  infix ` ~ₛ `:50 := shomotopy

  ------------------------------
  -- Suspension prespectra
  ------------------------------

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
  definition shomotopy_group [constructor] (n : ℤ) (E : spectrum) : CommGroup := πag[0+2] (E (2 - n))

  notation `πₛ[`:95 n:0 `]`:0 := shomotopy_group n

  definition shomotopy_group_fun [constructor] (n : ℤ) {E F : spectrum} (f : E →ₛ F) :
    πₛ[n] E →g πₛ[n] F :=
  π→g[1+1] (f (2 - n))

  notation `πₛ→[`:95 n:0 `]`:0 := shomotopy_group_fun n

  /-------------------------------
    Cotensor of spectra by types
  -------------------------------/

  -- Makes sense for any indexing succ_str.  Could be done for
  -- prespectra too, but as with truncation, why bother?
  definition sp_cotensor {N : succ_str} (A : Type*) (B : gen_spectrum N) : gen_spectrum N :=
    spectrum.MK (λn, ppmap A (B n))
      (λn, (loop_pmap_commute A (B (S n)))⁻¹ᵉ* ∘*ᵉ (equiv_ppcompose_left (equiv_glue B n)))

  ----------------------------------------
  -- Sections of parametrized spectra
  ----------------------------------------

  definition spi {N : succ_str} (A : Type) (E : A -> gen_spectrum N) : gen_spectrum N :=
    spectrum.MK (λn, ppi (λa, E a n))
      (λn, (loop_ppi_commute (λa, E a (S n)))⁻¹ᵉ* ∘*ᵉ equiv_ppi_right (λa, equiv_glue (E a) n))

  /-----------------------------------------
    Fibers and long exact sequences
  -----------------------------------------/

  definition sfiber {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y) : gen_spectrum N :=
    spectrum.MK (λn, pfiber (f n))
      (λn, pfiber_loop_space (f (S n)) ∘*ᵉ pfiber_equiv_of_square (sglue_square f n))

  /- the map from the fiber to the domain. The fact that the square commutes requires work -/
  definition spoint {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y) : sfiber f →ₛ X :=
  smap.mk (λn, ppoint (f n))
    begin
      intro n, exact sorry
    end

  definition π_glue (X : spectrum) (n : ℤ) : π*[2] (X (2 - succ n)) ≃* π*[3] (X (2 - n)) :=
  begin
    refine phomotopy_group_pequiv 2 (equiv_glue X (2 - succ n)) ⬝e* _,
    assert H : succ (2 - succ n) = 2 - n, exact ap succ !sub_sub⁻¹ ⬝ sub_add_cancel (2-n) 1,
    exact pequiv_of_eq (ap (λn, π*[2] (Ω (X n))) H),
  end

  definition πg_glue (X : spectrum) (n : ℤ) : πg[1+1] (X (2 - succ n)) ≃g πg[2+1] (X (2 - n)) :=
  begin
    refine homotopy_group_isomorphism_of_pequiv 1 (equiv_glue X (2 - succ n)) ⬝g _,
    assert H : succ (2 - succ n) = 2 - n, exact ap succ !sub_sub⁻¹ ⬝ sub_add_cancel (2-n) 1,
    exact isomorphism_of_eq (ap (λn, πg[1+1] (Ω (X n))) H),
  end

  definition πg_glue_homotopy_π_glue (X : spectrum) (n : ℤ) : πg_glue X n ~ π_glue X n :=
  begin
    intro x,
    esimp [πg_glue, π_glue],
    apply ap (λp, cast p _),
    refine !ap_compose'⁻¹ ⬝ !ap_compose'
  end

  definition π_glue_square {X Y : spectrum} (f : X →ₛ Y) (n : ℤ) :
    π_glue Y n ∘* π→*[2] (f (2 - succ n)) ~* π→*[3] (f (2 - n)) ∘* π_glue X n :=
  begin
    refine !passoc ⬝* _,
    assert H1 : phomotopy_group_pequiv 2 (equiv_glue Y (2 - succ n)) ∘* π→*[2] (f (2 - succ n))
     ~* π→*[2] (Ω→ (f (succ (2 - succ n)))) ∘* phomotopy_group_pequiv 2 (equiv_glue X (2 - succ n)),
    { refine !phomotopy_group_functor_compose⁻¹* ⬝* _,
      refine phomotopy_group_functor_phomotopy 2 !sglue_square ⬝* _,
      apply phomotopy_group_functor_compose },
    refine pwhisker_left _ H1 ⬝* _, clear H1,
    refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
    apply pwhisker_right,
    refine !pequiv_of_eq_commute ⬝* by reflexivity
  end

  section
  open chain_complex prod fin group

  universe variable u
  parameters {X Y : spectrum.{u}} (f : X →ₛ Y)

  definition LES_of_shomotopy_groups : chain_complex +3ℤ :=
  splice (λ(n : ℤ), LES_of_homotopy_groups (f (2 - n))) (2, 0)
         (π_glue Y) (π_glue X) (π_glue_square f)

  -- This LES is definitionally what we want:
  example (n : ℤ) : LES_of_shomotopy_groups (n, 0) = πₛ[n] Y := idp
  example (n : ℤ) : LES_of_shomotopy_groups (n, 1) = πₛ[n] X := idp
  example (n : ℤ) : LES_of_shomotopy_groups (n, 2) = πₛ[n] (sfiber f) := idp
  example (n : ℤ) : cc_to_fn LES_of_shomotopy_groups (n, 0) = πₛ→[n] f := idp
  example (n : ℤ) : cc_to_fn LES_of_shomotopy_groups (n, 1) = πₛ→[n] (spoint f) := idp
  -- the maps are ugly for (n, 2)

  definition comm_group_LES_of_shomotopy_groups : Π(v : +3ℤ), comm_group (LES_of_shomotopy_groups v)
  | (n, fin.mk 0 H) := proof CommGroup.struct (πₛ[n] Y) qed
  | (n, fin.mk 1 H) := proof CommGroup.struct (πₛ[n] X) qed
  | (n, fin.mk 2 H) := proof CommGroup.struct (πₛ[n] (sfiber f)) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end
  local attribute comm_group_LES_of_shomotopy_groups [instance]

  definition is_homomorphism_LES_of_shomotopy_groups :
    Π(v : +3ℤ), is_homomorphism (cc_to_fn LES_of_shomotopy_groups v)
  | (n, fin.mk 0 H) := proof homomorphism.struct (πₛ→[n] f) qed
  | (n, fin.mk 1 H) := proof homomorphism.struct (πₛ→[n] (spoint f)) qed
  | (n, fin.mk 2 H) := proof homomorphism.struct
        (homomorphism_LES_of_homotopy_groups_fun (f (2 - n)) (1, 2) ∘g
         homomorphism_change_fun (πg_glue Y n) _ (πg_glue_homotopy_π_glue Y n)) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  -- In the comments below is a start on an explicit description of the LES for spectra
  -- Maybe it's slightly nicer to work with than the above version

--   definition shomotopy_groups [reducible] : -3ℤ → CommGroup
--   | (n, fin.mk 0 H) := πₛ[n] Y
--   | (n, fin.mk 1 H) := πₛ[n] X
--   | (n, fin.mk k H) := πₛ[n] (sfiber f)

--   definition shomotopy_groups_fun : Π(n : -3ℤ), shomotopy_groups (S n) →g shomotopy_groups n
--   | (n, fin.mk 0 H) := proof π→g[1+1] (f (n + 2)) qed --π→*[2] f (n+2)
-- --pmap_of_homomorphism (πₛ→[n] f)
--   | (n, fin.mk 1 H) := proof π→g[1+1] (ppoint (f (n + 2))) qed
--   | (n, fin.mk 2 H) :=
--     proof _ ∘g π→g[1+1] equiv_glue Y (pred n + 2) qed
-- --π→*[n] boundary_map ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y n))
--   | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  end

  structure sp_chain_complex (N : succ_str) : Type :=
    (car : N → spectrum)
    (fn : Π(n : N), car (S n) →ₛ car n)
    (is_chain_complex : Πn, fn n ∘ₛ fn (S n) ~ₛ szero _ _)

  section
    variables {N : succ_str} (X : sp_chain_complex N) (n : N)

    definition scc_to_car [unfold 2] [coercion] := @sp_chain_complex.car
    definition scc_to_fn [unfold 2] : X (S n) →ₛ X n := sp_chain_complex.fn X n
    definition scc_is_chain_complex [unfold 2] : scc_to_fn X n ∘ₛ scc_to_fn X (S n) ~ₛ szero _ _
      := sp_chain_complex.is_chain_complex X n
  end

  /- Mapping spectra -/

  definition mapping_prespectrum [constructor] {N : succ_str} (X : Type*) (Y : gen_prespectrum N) :
    gen_prespectrum N :=
  gen_prespectrum.mk (λn, ppmap X (Y n)) (λn, pfunext X (Y (S n)) ∘* ppcompose_left (glue Y n))

  definition mapping_spectrum [constructor] {N : succ_str} (X : Type*) (Y : gen_spectrum N) :
    gen_spectrum N :=
  gen_spectrum.mk
    (mapping_prespectrum X Y)
    (is_spectrum.mk (λn, to_is_equiv (equiv_ppcompose_left (equiv_glue Y n) ⬝e
                         pfunext X (Y (S n)))))

  /- Spectrification -/

  /- Tensor by spaces -/

  /- Smash product of spectra -/

  /- Cofibers and stability -/

end spectrum
