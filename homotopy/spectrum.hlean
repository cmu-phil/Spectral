/-
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman, Floris van Doorn

-/

import homotopy.LES_of_homotopy_groups .splice ..colim types.pointed2 .EM ..pointed_pi .smash_adjoint
open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     seq_colim succ_str EM EM.ops

/---------------------
  Basic definitions
  ---------------------/

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
definition prespectrum.mk (Y : ℤ → Type*) (e : Π(n : ℤ), Y n →* Ω (Y (n+1))) : prespectrum :=
gen_prespectrum.mk Y e
abbreviation spectrum := gen_spectrum +ℤ
abbreviation spectrum.mk (Y : prespectrum) (e : is_spectrum Y) : spectrum :=
gen_spectrum.mk Y e

namespace spectrum

  definition glue {{N : succ_str}} := @gen_prespectrum.glue N
  --definition glue := (@gen_prespectrum.glue +ℤ)
  definition equiv_glue {N : succ_str} (E : gen_prespectrum N) [H : is_spectrum E] (n:N) : (E n) ≃* (Ω (E (S n))) :=
    pequiv_of_pmap (glue E n) (is_spectrum.is_equiv_glue E n)

  definition equiv_glue2 (Y : spectrum) (n : ℤ) : Ω (Ω (Y (n+2))) ≃* Y n :=
  begin
    refine (!equiv_glue ⬝e* loop_pequiv_loop (!equiv_glue ⬝e* loop_pequiv_loop _))⁻¹ᵉ*,
    refine pequiv_of_eq (ap Y _),
    exact add.assoc n 1 1
  end

  -- a square when we compose glue with transporting over a path in N
  definition glue_ptransport {N : succ_str} (X : gen_prespectrum N) {n n' : N} (p : n = n') :
    glue X n' ∘* ptransport X p ~* Ω→ (ptransport X (ap S p)) ∘* glue X n :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹* ⬝* pwhisker_right _ !ap1_pid⁻¹*

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
    gen_spectrum.mk (psp_of_gen_indexed z E) (is_spectrum_of_gen_indexed z E)

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

  definition sid {N : succ_str} (E : gen_prespectrum N) : E →ₛ E :=
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
         ... ~* Ω→(to_fun g (S n)) ∘* (Ω→ (f (S n)) ∘* glue X n) : pwhisker_left (Ω→(to_fun g (S n))) (glue_square f n)
         ... ~* (Ω→(to_fun g (S n)) ∘* Ω→(f (S n))) ∘* glue X n  : passoc
         ... ~* Ω→(to_fun g (S n) ∘* to_fun f (S n)) ∘* glue X n : pwhisker_right (glue X n) (ap1_pcompose _ _))

  infixr ` ∘ₛ `:60 := scompose

  definition szero [constructor] {N : succ_str} (E F : gen_prespectrum N) : E →ₛ F :=
    smap.mk (λn, pconst (E n) (F n))
      (λn, calc glue F n ∘* pconst (E n) (F n) ~* pconst (E n) (Ω(F (S n)))                    : pcompose_pconst
                                         ...   ~* pconst (Ω(E (S n))) (Ω(F (S n))) ∘* glue E n : pconst_pcompose
                                         ...   ~* Ω→(pconst (E (S n)) (F (S n))) ∘* glue E n   : pwhisker_right (glue E n) (ap1_pconst _ _))

  definition stransport [constructor] {N : succ_str} {A : Type} {a a' : A} (p : a = a')
  (E : A → gen_prespectrum N) : E a →ₛ E a' :=
  smap.mk (λn, ptransport (λa, E a n) p)
          begin
            intro n, induction p,
            exact !pcompose_pid ⬝* !pid_pcompose⁻¹* ⬝* pwhisker_right _ !ap1_pid⁻¹*,
          end

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
    gen_prespectrum.mk (λn, psuspn n X) (λn, loop_psusp_unit (psuspn n X))

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
  definition shomotopy_group (n : ℤ) (E : spectrum) : AbGroup := πag[2] (E (2 - n))

  notation `πₛ[`:95 n:0 `]`:0 := shomotopy_group n

  definition shomotopy_group_fun (n : ℤ) {E F : spectrum} (f : E →ₛ F) :
    πₛ[n] E →g πₛ[n] F :=
  π→g[2] (f (2 - n))

  notation `πₛ→[`:95 n:0 `]`:0 := shomotopy_group_fun n

  /-------------------------------
    Cotensor of spectra by types
  -------------------------------/

  -- Makes sense for any indexing succ_str.  Could be done for
  -- prespectra too, but as with truncation, why bother?

  definition sp_cotensor [constructor] {N : succ_str} (A : Type*) (B : gen_spectrum N) : gen_spectrum N :=
    spectrum.MK (λn, ppmap A (B n))
      (λn, (loop_ppmap_commute A (B (S n)))⁻¹ᵉ* ∘*ᵉ (pequiv_ppcompose_left (equiv_glue B n)))

  ----------------------------------------
  -- Sections of parametrized spectra
  ----------------------------------------

  definition spi [constructor] {N : succ_str} (A : Type*) (E : A -> gen_spectrum N) : gen_spectrum N :=
    spectrum.MK (λn, Π*a, E a n)
      (λn, !ppi_loop_pequiv⁻¹ᵉ* ∘*ᵉ ppi_pequiv_right (λa, equiv_glue (E a) n))

  /-----------------------------------------
    Fibers and long exact sequences
  -----------------------------------------/

  definition sfiber {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y) : gen_spectrum N :=
    spectrum.MK (λn, pfiber (f n))
       (λn, (loop_pfiber (f (S n)))⁻¹ᵉ* ∘*ᵉ pfiber_pequiv_of_square _ _ (sglue_square f n))

  /- the map from the fiber to the domain -/
  definition spoint {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y) : sfiber f →ₛ X :=
  smap.mk (λn, ppoint (f n))
    begin
      intro n,
      refine _ ⬝* !passoc,
      refine _ ⬝* pwhisker_right _ !ppoint_loop_pfiber_inv⁻¹*,
      rexact (pfiber_pequiv_of_square_ppoint (equiv_glue X n) (equiv_glue Y n) (sglue_square f n))⁻¹*
    end

  definition scompose_spoint {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y)
    : f ∘ₛ spoint f ~ₛ szero (sfiber f) Y :=
  begin
    fapply shomotopy.mk,
    { intro n, exact pcompose_ppoint (f n) },
    { intro n, exact sorry }
  end

  definition equiv_glue_neg (X : spectrum) (n : ℤ) : X (2 - succ n) ≃* Ω (X (2 - n)) :=
  have H : succ (2 - succ n) = 2 - n, from ap succ !sub_sub⁻¹ ⬝ sub_add_cancel (2-n) 1,
  equiv_glue X (2 - succ n) ⬝e* loop_pequiv_loop (pequiv_of_eq (ap X H))

  definition π_glue (X : spectrum) (n : ℤ) : π[2] (X (2 - succ n)) ≃* π[3] (X (2 - n)) :=
  homotopy_group_pequiv 2 (equiv_glue_neg X n)

  definition πg_glue (X : spectrum) (n : ℤ) : πg[2] (X (2 - succ n)) ≃g πg[3] (X (2 - n)) :=
  by rexact homotopy_group_isomorphism_of_pequiv _ (equiv_glue_neg X n)

  definition πg_glue_homotopy_π_glue (X : spectrum) (n : ℤ) : πg_glue X n ~ π_glue X n :=
  by reflexivity

  definition π_glue_square {X Y : spectrum} (f : X →ₛ Y) (n : ℤ) :
    π_glue Y n ∘* π→[2] (f (2 - succ n)) ~* π→[3] (f (2 - n)) ∘* π_glue X n :=
  begin
    change π→[2] (equiv_glue_neg Y n) ∘* π→[2] (f (2 - succ n)) ~*
           π→[2] (Ω→ (f (2 - n))) ∘* π→[2] (equiv_glue_neg X n),
    refine homotopy_group_functor_psquare 2 _,
    refine !sglue_square ⬝v* ap1_psquare !pequiv_of_eq_commute
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

  definition ab_group_LES_of_shomotopy_groups : Π(v : +3ℤ), ab_group (LES_of_shomotopy_groups v)
  | (n, fin.mk 0 H) := proof AbGroup.struct (πₛ[n] Y) qed
  | (n, fin.mk 1 H) := proof AbGroup.struct (πₛ[n] X) qed
  | (n, fin.mk 2 H) := proof AbGroup.struct (πₛ[n] (sfiber f)) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end
  local attribute ab_group_LES_of_shomotopy_groups [instance]

  definition is_mul_hom_LES_of_shomotopy_groups :
    Π(v : +3ℤ), is_mul_hom (cc_to_fn LES_of_shomotopy_groups v)
  | (n, fin.mk 0 H) := proof homomorphism.struct (πₛ→[n] f) qed
  | (n, fin.mk 1 H) := proof homomorphism.struct (πₛ→[n] (spoint f)) qed
  | (n, fin.mk 2 H) := proof homomorphism.struct
        (homomorphism_LES_of_homotopy_groups_fun (f (2 - n)) (1, 2) ∘g πg_glue Y n) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition is_exact_LES_of_shomotopy_groups : is_exact LES_of_shomotopy_groups :=
  begin
    apply is_exact_splice, intro n, apply is_exact_LES_of_homotopy_groups,
  end

  -- In the comments below is a start on an explicit description of the LES for spectra
  -- Maybe it's slightly nicer to work with than the above version

  definition shomotopy_groups [reducible] : +3ℤ → AbGroup
  | (n, fin.mk 0 H) := πₛ[n] Y
  | (n, fin.mk 1 H) := πₛ[n] X
  | (n, fin.mk k H) := πₛ[n] (sfiber f)

  definition shomotopy_groups_fun : Π(v : +3ℤ), shomotopy_groups (S v) →g shomotopy_groups v
  | (n, fin.mk 0 H) := proof πₛ→[n] f qed
  | (n, fin.mk 1 H) := proof πₛ→[n] (spoint f) qed
  | (n, fin.mk 2 H) := proof homomorphism_LES_of_homotopy_groups_fun (f (2 - n)) (nat.succ nat.zero, 2) ∘g
                             πg_glue Y n ∘g (by reflexivity) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end
--(homomorphism_LES_of_homotopy_groups_fun (f (2 - n)) (1, 2) ∘g πg_glue Y n)
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
  -- note: see also cotensor above


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

  /-
    Let Y = spectify X ≡ colim_k Ω^k X (n + k). Then
    Ω Y (n+1) ≡ Ω colim_k Ω^k X ((n + 1) + k)
          ... = colim_k Ω^{k+1} X ((n + 1) + k)
          ... = colim_k Ω^{k+1} X (n + (k + 1))
          ... = colim_k Ω^k X(n + k)
          ... ≡ Y n
  -/

  definition spectrify_pequiv {N : succ_str} (X : gen_prespectrum N) (n : N) :
    spectrify_type X n ≃* Ω (spectrify_type X (S n)) :=
  begin
    refine !pshift_equiv ⬝e* _,
    transitivity pseq_colim (λk, spectrify_type_fun' X (succ k) (S n +' k)),
    fapply pseq_colim_pequiv,
    { intro n, apply loopn_pequiv_loopn, apply pequiv_ap X, apply succ_str.add_succ },
    { intro k, apply to_homotopy,
      refine !passoc⁻¹* ⬝* _, refine pwhisker_right _ (loopn_succ_in_inv_natural (succ k) _) ⬝* _,
      refine !passoc ⬝* _ ⬝* !passoc⁻¹*, apply pwhisker_left,
      refine !apn_pcompose⁻¹* ⬝* _ ⬝* !apn_pcompose, apply apn_phomotopy,
      exact !glue_ptransport⁻¹* },
    refine _ ⬝e* !pseq_colim_loop⁻¹ᵉ*,
    refine pseq_colim_equiv_constant (λn, !ap1_pcompose⁻¹*),
  end

  definition spectrify [constructor] {N : succ_str} (X : gen_prespectrum N) : gen_spectrum N :=
  spectrum.MK (spectrify_type X) (spectrify_pequiv X)

  definition gluen {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ)
    : X n →* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact !loopn_succ_in⁻¹ᵉ* ∘* Ω→[k] (glue X (n +' k)) ∘* f

  -- note: the forward map is (currently) not definitionally equal to gluen. Is that a problem?
  definition equiv_gluen {N : succ_str} (X : gen_spectrum N) (n : N) (k : ℕ)
    : X n ≃* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact f ⬝e* loopn_pequiv_loopn k (equiv_glue X (n +' k))
                                                ⬝e* !loopn_succ_in⁻¹ᵉ*

  definition spectrify_map {N : succ_str} {X : gen_prespectrum N} : X →ₛ spectrify X :=
  begin
    fapply smap.mk,
    { intro n, exact pinclusion _ 0 },
    { intro n, apply phomotopy_of_psquare, refine !pid_pcompose⁻¹* ⬝ph* _,
      refine !pid_pcompose⁻¹* ⬝ph* _,
      --pshift_equiv_pinclusion (spectrify_type_fun X n) 0
      refine _ ⬝v* _,
      rotate 1, exact pshift_equiv_pinclusion (spectrify_type_fun X n) 0,
--      refine !passoc⁻¹* ⬝* pwhisker_left _ _ ⬝* _,
      exact sorry
}
  end

  definition spectrify.elim {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X →ₛ Y) : spectrify X →ₛ Y :=
  begin
    fapply smap.mk,
    { intro n, fapply pseq_colim.elim,
      { intro k, refine !equiv_gluen⁻¹ᵉ* ∘* apn k (f (n +' k)) },
      { intro k, apply to_homotopy, exact sorry }},
    { intro n, exact sorry }
  end

  definition spectrify_fun {N : succ_str} {X Y : gen_prespectrum N} (f : X →ₛ Y) : spectrify X →ₛ spectrify Y :=
  spectrify.elim ((@spectrify_map _ Y) ∘ₛ f)

  /- Tensor by spaces -/

  /- Smash product of spectra -/

open smash

definition smash_prespectrum (X : Type*) (Y : prespectrum) : prespectrum :=
prespectrum.mk (λ z, X ∧ Y z) begin
  intro n, refine loop_psusp_pintro (X ∧ Y n) (X ∧ Y (n + 1)) _,
  refine _ ∘* (smash_psusp X (Y n))⁻¹ᵉ*,
  refine smash_functor !pid _,
  refine psusp_pelim (Y n) (Y (n + 1)) _,
  exact !glue
end

definition smash_prespectrum_fun {X X' : Type*} {Y Y' : prespectrum} (f : X →* X') (g : Y →ₛ Y') : smash_prespectrum X Y →ₛ smash_prespectrum X' Y' :=
smap.mk (λn, smash_functor f (g n)) begin
  intro n,
  refine susp_to_loop_psquare _ _ _ _ _,
  refine pvconcat (psquare_transpose (phinverse (smash_psusp_natural f (g n)))) _,
  refine vconcat_phomotopy _ (smash_functor_split f (g (S n))),
  refine phomotopy_vconcat (smash_functor_split f (psusp_functor (g n))) _,
  refine phconcat _ _,
  let glue_adjoint := psusp_pelim (Y n) (Y (S n)) (glue Y n),
  exact pid X' ∧→ glue_adjoint,
  exact smash_functor_psquare (pvrefl f) (phrefl glue_adjoint),
  refine smash_functor_psquare (phrefl (pid X')) _,
  refine loop_to_susp_square _ _ _ _ _,
  exact smap.glue_square g n
end

definition smash_spectrum (X : Type*) (Y : spectrum) : spectrum :=
spectrify (smash_prespectrum X Y)

definition smash_spectrum_fun {X X' : Type*} {Y Y' : spectrum} (f : X →* X') (g : Y →ₛ Y') : smash_spectrum X Y →ₛ smash_spectrum X' Y' :=
spectrify_fun (smash_prespectrum_fun f g)

  /- Cofibers and stability -/

  /- The Eilenberg-MacLane spectrum -/

  definition EM_spectrum /-[constructor]-/ (G : AbGroup) : spectrum :=
  spectrum.Mk (K G) (λn, (loop_EM G n)⁻¹ᵉ*)


end spectrum
