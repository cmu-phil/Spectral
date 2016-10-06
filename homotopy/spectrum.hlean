/-
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman, Floris van Doorn

-/

import homotopy.LES_of_homotopy_groups .splice homotopy.susp ..move_to_lib ..colim
open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     seq_colim

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

abbreviation prespectrum := gen_prespectrum +ℤ
abbreviation prespectrum.mk := @gen_prespectrum.mk +ℤ
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
  protected definition MK [constructor] {N : succ_str} (deloop : N → Type*)
    (glue : Π(n:N), (deloop n) ≃* (Ω (deloop (S n)))) : gen_spectrum N :=
    gen_spectrum.mk (gen_prespectrum.mk deloop (λ(n:N), glue n))
    (begin
      apply is_spectrum.mk, intros n, esimp,
      apply pequiv.to_is_equiv  -- Why doesn't typeclass inference find this?
    end)

  -- Finally, we combine them and give a way to produce a (ℤ-)spectrum from a ℕ-indexed family of 'equiv's.
  protected definition Mk [constructor] (deloop : ℕ → Type*)
    (glue : Π(n:ℕ), (deloop n) ≃* (Ω (deloop (nat.succ n)))) : spectrum :=
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
    (λn, calc glue E n ∘* pid (E n) ~* glue E n                   : pcompose_pid
                              ...   ~* pid (Ω(E (S n))) ∘* glue E n : pid_pcompose
                              ...   ~* Ω→(pid (E (S n))) ∘* glue E n : pwhisker_right (glue E n) ap1_pid⁻¹*)

  definition scompose {N : succ_str} {X Y Z : gen_prespectrum N} (g : Y →ₛ Z) (f : X →ₛ Y) : X →ₛ Z :=
    smap.mk (λn, g n ∘* f n)
      (λn, calc glue Z n ∘* to_fun g n ∘* to_fun f n
             ~* (glue Z n ∘* to_fun g n) ∘* to_fun f n                 : passoc
         ... ~* (Ω→(to_fun g (S n)) ∘* glue Y n) ∘* to_fun f n      : pwhisker_right (to_fun f n) (glue_square g n)
         ... ~* Ω→(to_fun g (S n)) ∘* (glue Y n ∘* to_fun f n)      : passoc
         ... ~* Ω→(to_fun g (S n)) ∘* (Ω→ (f (S n)) ∘* glue X n) : pwhisker_left Ω→(to_fun g (S n)) (glue_square f n)
         ... ~* (Ω→(to_fun g (S n)) ∘* Ω→(f (S n))) ∘* glue X n  : passoc
         ... ~* Ω→(to_fun g (S n) ∘* to_fun f (S n)) ∘* glue X n : pwhisker_right (glue X n) (ap1_pcompose _ _))

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
      (λn, (loop_pmap_commute A (B (S n)))⁻¹ᵉ* ∘*ᵉ (pequiv_ppcompose_left (equiv_glue B n)))

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

  definition π_glue (X : spectrum) (n : ℤ) : π[2] (X (2 - succ n)) ≃* π[3] (X (2 - n)) :=
  begin
    refine homotopy_group_pequiv 2 (equiv_glue X (2 - succ n)) ⬝e* _,
    assert H : succ (2 - succ n) = 2 - n, exact ap succ !sub_sub⁻¹ ⬝ sub_add_cancel (2-n) 1,
    exact pequiv_of_eq (ap (λn, π[2] (Ω (X n))) H),
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
    π_glue Y n ∘* π→[2] (f (2 - succ n)) ~* π→[3] (f (2 - n)) ∘* π_glue X n :=
  begin
    refine !passoc ⬝* _,
    assert H1 : homotopy_group_pequiv 2 (equiv_glue Y (2 - succ n)) ∘* π→[2] (f (2 - succ n))
     ~* π→[2] (Ω→ (f (succ (2 - succ n)))) ∘* homotopy_group_pequiv 2 (equiv_glue X (2 - succ n)),
    { refine !homotopy_group_functor_compose⁻¹* ⬝* _,
      refine homotopy_group_functor_phomotopy 2 !sglue_square ⬝* _,
      apply homotopy_group_functor_compose },
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
--   | (n, fin.mk 0 H) := proof π→g[1+1] (f (n + 2)) qed --π→[2] f (n+2)
-- --pmap_of_homomorphism (πₛ→[n] f)
--   | (n, fin.mk 1 H) := proof π→g[1+1] (ppoint (f (n + 2))) qed
--   | (n, fin.mk 2 H) :=
--     proof _ ∘g π→g[1+1] equiv_glue Y (pred n + 2) qed
-- --π→[n] boundary_map ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y n))
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
    (is_spectrum.mk (λn, to_is_equiv (pequiv_ppcompose_left (equiv_glue Y n) ⬝e
                         pfunext X (Y (S n)))))

  /- Spectrification -/

  open chain_complex
  definition spectrify_type_term {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) : Type* :=
  Ω[k] (X (n +' k))

  definition spectrify_type_fun' {N : succ_str} (X : gen_prespectrum N) (k : ℕ) (n : N) :
    Ω[k] (X n) →* Ω[k+1] (X (S n)) :=
  !loopn_succ_in⁻¹ᵉ* ∘* Ω→[k] (glue X n)

  definition spectrify_type_fun {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) :
    spectrify_type_term X n k →* spectrify_type_term X n (k+1) :=
  spectrify_type_fun' X k (n +' k)

  definition spectrify_type {N : succ_str} (X : gen_prespectrum N) (n : N) : Type* :=
  pseq_colim (spectrify_type_fun X n)

  definition spectrify_pequiv {N : succ_str} (X : gen_prespectrum N) (n : N) :
    spectrify_type X n ≃* Ω (spectrify_type X (S n)) :=
  begin
    refine _ ⬝e* !pseq_colim_loop⁻¹ᵉ*,
    refine !pshift_equiv ⬝e* _,
    refine _ ⬝e* pseq_colim_equiv_constant (λn, !ap1_pcompose⁻¹*),
    transitivity pseq_colim (λk, spectrify_type_fun' X (succ k) (S n +' k)),
    rotate 1, --exact pseq_colim_equiv_constant (λn, !ap1_pcompose⁻¹*),
    reflexivity,
    transitivity pseq_colim (λk, spectrify_type_fun' X (succ k) (n +' succ k)),
    reflexivity,
    fapply pseq_colim_pequiv,
    { intro n, apply loopn_pequiv_loopn, apply pequiv_ap X, apply succ_str.add_succ },
    { intro n, apply to_homotopy, exact sorry }
  end

  definition spectrify [constructor] {N : succ_str} (X : gen_prespectrum N) : gen_spectrum N :=
  spectrum.MK (spectrify_type X) (spectrify_pequiv X)

  definition gluen {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ)
    : X n →* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact !loopn_succ_in⁻¹ᵉ* ∘* Ω→[k] (glue X (n +' k)) ∘* f

  -- note: the forward map is (currently) not definitionally equal to gluen.
  definition equiv_gluen {N : succ_str} (X : gen_spectrum N) (n : N) (k : ℕ)
    : X n ≃* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact f ⬝e* loopn_pequiv_loopn k (equiv_glue X (n +' k))
                                                ⬝e* !loopn_succ_in⁻¹ᵉ*

  definition spectrify_map {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X →ₛ Y) : spectrify X →ₛ Y :=
  begin
    fapply smap.mk,
    { intro n, fapply pseq_colim.elim,
      { intro k, refine !equiv_gluen⁻¹ᵉ* ∘* apn k (f (n +' k)) },
      { intro k, apply to_homotopy, exact sorry }},
    { intro n, exact sorry }
  end

  /- Tensor by spaces -/

  /- Smash product of spectra -/

  /- Cofibers and stability -/

end spectrum
