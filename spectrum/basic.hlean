/-
Copyright (c) 2016 Michael Shulman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shulman, Floris van Doorn, Egbert Rijke, Stefano Piceghello, Yuri Sulyma

-/

import homotopy.LES_of_homotopy_groups ..algebra.splice ..algebra.seq_colim ..homotopy.EM ..homotopy.fwedge
       ..pointed_cubes

open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     succ_str EM EM.ops function unit lift is_trunc

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
attribute gen_spectrum._trans_of_to_prespectrum [unfold 2]

-- Classically, spectra and prespectra use the successor structure +ℕ.
-- But we will use +ℤ instead, to reduce case analysis later on.

abbreviation prespectrum := gen_prespectrum +ℤ
definition prespectrum.mk (Y : ℤ → Type*) (e : Π(n : ℤ), Y n →* Ω (Y (n+1))) : prespectrum :=
gen_prespectrum.mk Y e
abbreviation spectrum := gen_spectrum +ℤ
abbreviation spectrum.mk (Y : prespectrum) (e : is_spectrum Y) : spectrum :=
gen_spectrum.mk Y e

namespace spectrum

  definition glue [unfold 2] {{N : succ_str}} := @gen_prespectrum.glue N
  --definition glue := (@gen_prespectrum.glue +ℤ)
  definition equiv_glue {N : succ_str} (E : gen_prespectrum N) [H : is_spectrum E] (n:N) : (E n) ≃* (Ω (E (S n))) :=
    pequiv_of_pmap (glue E n) (is_spectrum.is_equiv_glue E n)

  definition equiv_glue2 (Y : spectrum) (n : ℤ) : Ω (Ω (Y (n+2))) ≃* Y n :=
  begin
    refine (!equiv_glue ⬝e* loop_pequiv_loop (!equiv_glue ⬝e* loop_pequiv_loop _))⁻¹ᵉ*,
    refine pequiv_of_eq (ap Y _),
    exact add.assoc n 1 1
  end

  definition gluen {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ)
    : X n →* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact !loopn_succ_in⁻¹ᵉ* ∘* Ω→[k] (glue X (n +' k)) ∘* f

  -- note: the forward map is (currently) not definitionally equal to gluen. Is that a problem?
  definition equiv_gluen {N : succ_str} (X : gen_spectrum N) (n : N) (k : ℕ)
    : X n ≃* Ω[k] (X (n +' k)) :=
  by induction k with k f; reflexivity; exact f ⬝e* (loopn_pequiv_loopn k (equiv_glue X (n +' k))
                                                ⬝e* !loopn_succ_in⁻¹ᵉ*)

  definition equiv_gluen_inv_succ {N : succ_str} (X : gen_spectrum N) (n : N) (k : ℕ) :
    (equiv_gluen X n (k+1))⁻¹ᵉ* ~*
    (equiv_gluen X n k)⁻¹ᵉ* ∘* Ω→[k] (equiv_glue X (n +' k))⁻¹ᵉ* ∘* !loopn_succ_in :=
  begin
    refine !trans_pinv ⬝* pwhisker_left _ _, refine !trans_pinv ⬝* _, refine pwhisker_left _ !pinv_pinv
  end

  definition succ_str_add_eq_int_add (n : ℤ) (m : ℕ) : @succ_str.add sint n m = n + m :=
  begin
    induction m with m IH,
    { symmetry, exact add_zero n },
    { exact ap int.succ IH ⬝ add.assoc n m 1 }
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

  definition psp_of_gen_indexed [constructor] {N : succ_str} (z : N) (E : gen_prespectrum N) : prespectrum :=
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
    (glue_square : Π(n:N), psquare
      (to_fun n)
      (Ω→ (to_fun (S n)))
      (glue E n)
      (glue F n)
    )

  definition smap_sigma {N : succ_str} (X Y : gen_prespectrum N) : Type :=
    Σ (to_fun : Π(n:N), X n →* Y n),
    Π(n:N), psquare
      (to_fun n)
      (Ω→ (to_fun (S n)))
      (glue X n)
      (glue Y n)

  open smap
  infix ` →ₛ `:30 := smap

  attribute smap.to_fun [coercion]

  definition smap_to_sigma [unfold 4] {N : succ_str} {X Y : gen_prespectrum N} (f : X →ₛ Y) : smap_sigma X Y :=
  begin
    induction f with f fsq,
    exact sigma.mk f fsq,
  end

  definition smap_to_struc [unfold 4] {N : succ_str} {X Y : gen_prespectrum N} (f : smap_sigma X Y) : X →ₛ Y :=
  begin
    induction f with f fsq,
    exact smap.mk f fsq,
  end

  definition smap_to_sigma_isretr {N : succ_str} {X Y : gen_prespectrum N} (f : smap_sigma X Y) :
    smap_to_sigma (smap_to_struc f) = f :=
  begin
    induction f, reflexivity
  end

  definition smap_to_sigma_issec {N : succ_str} {X Y : gen_prespectrum N} (f : X →ₛ Y) :
    smap_to_struc (smap_to_sigma f) = f :=
  begin
    induction f, reflexivity
  end

  definition smap_sigma_equiv [constructor] {N : succ_str} (X Y : gen_prespectrum N) : (smap_sigma X Y) ≃ (X →ₛ Y) :=
  begin
    fapply equiv.mk,
    exact smap_to_struc,
    fapply adjointify,
    exact smap_to_sigma,
    exact smap_to_sigma_issec,
    exact smap_to_sigma_isretr
  end

  -- A version of 'glue_square' in the spectrum case that uses 'equiv_glue'
  definition sglue_square {N : succ_str} {E F : gen_spectrum N} (f : E →ₛ F) (n : N)
    : psquare (f n) (Ω→ (f (S n))) (equiv_glue E n) (equiv_glue F n) :=
  glue_square f n

  definition sid [constructor] [refl] {N : succ_str} (E : gen_prespectrum N) : E →ₛ E :=
  smap.mk (λ n, pid (E n)) (λ n, psquare_of_phtpy_bot (ap1_pid) (psquare_of_pid_top_bot (phomotopy.rfl)))

  --print sid
 --   smap.mk (λn, pid (E n))
 --   (λn, calc glue E n ∘* pid (E n) ~* glue E n                   : pcompose_pid
 --                             ...   ~* pid (Ω(E (S n))) ∘* glue E n : pid_pcompose
 --                             ...   ~* Ω→(pid (E (S n))) ∘* glue E n : pwhisker_right (glue E n) ap1_pid⁻¹*)

  definition scompose [trans] {N : succ_str} {X Y Z : gen_prespectrum N}
    (g : Y →ₛ Z) (f : X →ₛ Y) : X →ₛ Z :=
    smap.mk (λn, g n ∘* f n)
            (λ n, psquare_of_phtpy_bot
                    (ap1_pcompose (g (S n)) (f (S n)))
                    (psquare_hcompose (glue_square f n) (glue_square g n)))

/-
      (λn, calc glue Z n ∘* to_fun g n ∘* to_fun f n
             ~* (glue Z n ∘* to_fun g n) ∘* to_fun f n                 : passoc
         ... ~* (Ω→(to_fun g (S n)) ∘* glue Y n) ∘* to_fun f n      : pwhisker_right (to_fun f n) (glue_square g n)
         ... ~* Ω→(to_fun g (S n)) ∘* (glue Y n ∘* to_fun f n)      : passoc
         ... ~* Ω→(to_fun g (S n)) ∘* (Ω→ (f (S n)) ∘* glue X n) : pwhisker_left (Ω→(to_fun g (S n))) (glue_square f n)
         ... ~* (Ω→(to_fun g (S n)) ∘* Ω→(f (S n))) ∘* glue X n  : passoc
         ... ~* Ω→(to_fun g (S n) ∘* to_fun f (S n)) ∘* glue X n : pwhisker_right (glue X n) (ap1_pcompose _ _))
-/

  infixr ` ∘ₛ `:60 := scompose

  definition szero [constructor] {N : succ_str} (E F : gen_prespectrum N) : E →ₛ F :=
    smap.mk (λn, pconst (E n) (F n))
            (λn, psquare_of_phtpy_bot (ap1_pconst (E (S n)) (F (S n)))
                   (psquare_of_pconst_top_bot (glue E n) (glue F n)))

/-
      (λn, calc glue F n ∘* pconst (E n) (F n) ~* pconst (E n) (Ω(F (S n)))                    : pcompose_pconst
                                         ...   ~* pconst (Ω(E (S n))) (Ω(F (S n))) ∘* glue E n : pconst_pcompose
                                         ...   ~* Ω→(pconst (E (S n)) (F (S n))) ∘* glue E n   : pwhisker_right (glue E n) (ap1_pconst _ _))
-/

  definition stransport [constructor] {N : succ_str} {A : Type} {a a' : A} (p : a = a')
  (E : A → gen_prespectrum N) : E a →ₛ E a' :=
  smap.mk (λn, ptransport (λa, E a n) p)
          begin
            intro n, induction p,
            exact !pcompose_pid ⬝* !pid_pcompose⁻¹* ⬝* pwhisker_right _ !ap1_pid⁻¹*,
          end

  structure shomotopy {N : succ_str} {E F : gen_prespectrum N} (f g : E →ₛ F) :=
    (to_phomotopy : Πn, f n ~* g n)
    (glue_homotopy : Πn, ptube_v
                           (to_phomotopy n)
                           (ap1_phomotopy (to_phomotopy (S n)))
                           (glue_square f n)
                           (glue_square g n))

/-    (glue_homotopy : Πn, phsquare
                         (pwhisker_left (glue F n) (to_phomotopy n))
                         (pwhisker_right (glue E n) (ap1_phomotopy (to_phomotopy (S n))))
                         (glue_square f n)
                         (glue_square g n))
-/

  infix ` ~ₛ `:50 := shomotopy

  definition shomotopy_compose {N : succ_str} {E F : gen_prespectrum N} {f g h : E →ₛ F} (p : g ~ₛ h) (q : f ~ₛ g) : f ~ₛ h :=
  shomotopy.mk
    (λn, (shomotopy.to_phomotopy q n) ⬝* (shomotopy.to_phomotopy p n))
    begin
      intro n, unfold [ptube_v],
      rewrite (pwhisker_left_trans _),
      rewrite ap1_phomotopy_trans,
      rewrite (pwhisker_right_trans _),
      exact phhconcat ((shomotopy.glue_homotopy q) n) ((shomotopy.glue_homotopy p) n)
    end

  definition shomotopy_inverse {N : succ_str} {E F : gen_prespectrum N} {f g : E →ₛ F} (p : f ~ₛ g) : g ~ₛ f :=
  shomotopy.mk (λn, (shomotopy.to_phomotopy p n)⁻¹*) begin
    intro n, unfold [ptube_v],
    rewrite (pwhisker_left_symm _ _),
    rewrite [-ap1_phomotopy_symm],
    rewrite (pwhisker_right_symm _ _),
    exact phhinverse ((shomotopy.glue_homotopy p) n)
  end


  /- Comparing the structure of shomotopy with a Σ-type -/
  definition shomotopy_sigma {N : succ_str} {X Y : gen_prespectrum N} (f g : X →ₛ Y) : Type :=
  Σ (phtpy : Π (n : N), f n ~* g n),
    Πn, ptube_v
      (phtpy n)
      (ap1_phomotopy (phtpy (S n)))
      (glue_square f n)
      (glue_square g n)

  definition shomotopy_to_sigma [unfold 6] {N : succ_str} {X Y : gen_prespectrum N} {f g : X →ₛ Y} (H : f ~ₛ g) : shomotopy_sigma f g :=
  begin
    induction H with H Hsq,
    exact sigma.mk H Hsq,
  end

  definition shomotopy_to_struct [unfold 6] {N : succ_str} {X Y : gen_prespectrum N} {f g : X →ₛ Y} (H : shomotopy_sigma f g) : f ~ₛ g :=
  begin
    induction H with H Hsq,
    exact shomotopy.mk H Hsq,
  end

  definition shomotopy_to_sigma_isretr {N : succ_str} {X Y : gen_prespectrum N} {f g : X →ₛ Y} (H : shomotopy_sigma f g) :
    shomotopy_to_sigma (shomotopy_to_struct H) = H
  :=
  begin
    induction H with H Hsq, reflexivity
  end

  definition shomotopy_to_sigma_issec {N : succ_str} {X Y : gen_prespectrum N} {f g : X →ₛ Y} (H : f ~ₛ g) :
    shomotopy_to_struct (shomotopy_to_sigma H) = H
  :=
  begin
    induction H, reflexivity
  end

  definition shomotopy_sigma_equiv [constructor] {N : succ_str} {X Y : gen_prespectrum N} (f g : X →ₛ Y) :
    shomotopy_sigma f g ≃ (f ~ₛ g) :=
  begin
    fapply equiv.mk,
    exact shomotopy_to_struct,
    fapply adjointify,
    exact shomotopy_to_sigma,
    exact shomotopy_to_sigma_issec,
    exact shomotopy_to_sigma_isretr,
  end

  /- equivalence of shomotopy and eq -/
  /-
  definition eq_of_shomotopy_pfun {N : succ_str} {X Y : gen_prespectrum N} {f g : X →ₛ Y} (H : f ~ₛ g) (n : N) : f n = g n :=
  begin
    fapply eq_of_fn_eq_fn (smap_sigma_equiv X Y),
    repeat exact sorry
  end-/

  definition fam_phomotopy_of_eq
    {N : Type} {X Y: N → Type*} (f g : Π n, X n →* Y n) : (f = g) ≃ (Π n, f n ~* g n) :=
    (eq.eq_equiv_homotopy) ⬝e pi_equiv_pi_right (λ n, pmap_eq_equiv (f n) (g n))

/-
  definition phomotopy_rec_on_eq [recursor]
    {k' : ppi B x₀}
    {Q : (k ~* k') → Type}
    (p : k ~* k')
    (H : Π(q : k = k'), Q (phomotopy_of_eq q))
    : Q p :=
  phomotopy_of_eq_of_phomotopy p ▸ H (eq_of_phomotopy p)
-/
  definition fam_phomotopy_rec_on_eq {N : Type} {X Y : N → Type*} (f g : Π n, X n →* Y n)
    {Q : (Π n, f n ~* g n) → Type}
    (p : Π n, f n ~* g n)
    (H : Π (q : f = g), Q (fam_phomotopy_of_eq f g q)) : Q p :=
  begin
    refine _ ▸ H ((fam_phomotopy_of_eq f g)⁻¹ᵉ p),
    have q : to_fun (fam_phomotopy_of_eq f g) (to_fun (fam_phomotopy_of_eq f g)⁻¹ᵉ p) = p,
    from right_inv (fam_phomotopy_of_eq f g) p,
    krewrite q
  end

/-
  definition phomotopy_rec_idp [recursor]
    {Q : Π {k' : ppi B x₀},  (k ~* k') → Type}
    (q : Q (phomotopy.refl k)) {k' : ppi B x₀} (H : k ~* k') : Q H :=
  begin
    induction H using phomotopy_rec_on_eq with t,
    induction t, exact eq_phomotopy_refl_phomotopy_of_eq_refl k ▸ q,
  end
-/

--set_option pp.coercions true

  definition fam_phomotopy_rec_idp {N : Type} {X Y : N → Type*} (f : Π n, X n →* Y n)
    (Q : Π (g : Π n, X n →* Y n) (H : Π n, f n ~* g n), Type)
    (q : Q f (λ n, phomotopy.rfl))
    (g : Π n, X n →* Y n) (H : Π n, f n ~* g n) : Q g H :=
  begin
    fapply fam_phomotopy_rec_on_eq,
    refine λ(p : f = g), _, --ugly trick
    intro p, induction p,
    exact q,
  end

  definition eq_of_shomotopy {N : succ_str} {X Y : gen_prespectrum N} {f g : X →ₛ Y} (H : f ~ₛ g) : f = g :=
  begin
    fapply eq_of_fn_eq_fn (smap_sigma_equiv X Y)⁻¹ᵉ,
    induction f with f fsq,
    induction g with g gsq,
    induction H with H Hsq,
    fapply sigma_eq,
    fapply eq_of_homotopy,
    intro n, fapply eq_of_phomotopy, exact H n,
    fapply pi_pathover_constant,
    intro n,
    esimp at *,
    revert g H gsq Hsq n,
    refine fam_phomotopy_rec_idp f _ _,
    intro gsq Hsq n,
    refine change_path _ _,
--    have p : eq_of_homotopy (λ n, eq_of_phomotopy phomotopy.rfl) = refl f,
    reflexivity,
    refine (eq_of_homotopy_eta rfl)⁻¹ ⬝ _,
    fapply ap (eq_of_homotopy), fapply eq_of_homotopy, intro n, refine (eq_of_phomotopy_refl _)⁻¹,
--    fapply eq_of_phomotopy,
    fapply pathover_idp_of_eq,
    note Hsq' := ptube_v_eq_bot phomotopy.rfl (ap1_phomotopy_refl _) (fsq n) (gsq n) (Hsq n),
    unfold ptube_v at *,
    unfold phsquare at *,
    refine _ ⬝ Hsq'⁻¹ ⬝ _,
    refine (trans_refl (fsq n))⁻¹ ⬝ _,
    exact idp ◾** (pwhisker_right_refl _ _)⁻¹,
    refine _ ⬝ (refl_trans (gsq n)),
    refine _ ◾** idp,
    exact pwhisker_left_refl _ _,
  end

  ------------------------------
  -- Equivalences of prespectra
  ------------------------------

  definition spectrum_pequiv_of_pequiv_succ {E F : spectrum} (n : ℤ) (e : E (n + 1) ≃* F (n + 1)) :
    E n ≃* F n :=
  equiv_glue E n ⬝e* loop_pequiv_loop e ⬝e* (equiv_glue F n)⁻¹ᵉ*

  definition spectrum_pequiv_of_nat {E F : spectrum} (e : Π(n : ℕ), E n ≃* F n) (n : ℤ) :
    E n ≃* F n :=
  begin
    induction n with n n,
      exact e n,
    induction n with n IH,
    { exact spectrum_pequiv_of_pequiv_succ -[1+0] (e 0) },
    { exact spectrum_pequiv_of_pequiv_succ -[1+succ n] IH }
  end

  definition spectrum_pequiv_of_nat_add {E F : spectrum} (m : ℕ)
    (e : Π(n : ℕ), E (n + m) ≃* F (n + m)) : Π(n : ℤ), E n ≃* F n :=
  begin
    apply spectrum_pequiv_of_nat,
    refine nat.rec_down _ m e _,
    intro n f k, cases k with k,
    exact spectrum_pequiv_of_pequiv_succ _ (f 0),
    exact pequiv_ap E (ap of_nat (succ_add k n)) ⬝e* f k ⬝e*
          pequiv_ap F (ap of_nat (succ_add k n))⁻¹
  end

  definition is_contr_spectrum_of_nat {E : spectrum} (e : Π(n : ℕ), is_contr (E n)) (n : ℤ) :
    is_contr (E n)  :=
  begin
    have Πn, is_contr (E (n + 1)) → is_contr (E n),
    from λn H, @(is_trunc_equiv_closed_rev -2 !equiv_glue) (is_contr_loop_of_is_contr H),
    induction n with n n,
      exact e n,
    induction n with n IH,
    { exact this -[1+0] (e 0) },
    { exact this -[1+succ n] IH }
  end

  structure is_sequiv {N : succ_str} {E F : gen_prespectrum N} (f : E →ₛ F) : Type :=
  (to_linv : F →ₛ E)
  (is_retr : to_linv ∘ₛf ~ₛ sid E)
  (to_rinv : F →ₛ E)
  (is_sec  : f ∘ₛ to_rinv ~ₛ sid F)

  structure sequiv {N : succ_str} (E F : gen_prespectrum N) : Type :=
  (to_fun  : E →ₛ F)
  (to_is_sequiv : is_sequiv to_fun)

  infix ` ≃ₛ ` : 25 := sequiv

  definition is_sequiv_smap {N : succ_str} {E F : gen_prespectrum N} (f : E →ₛ F) : Type := Π (n: N), is_equiv (f n)

  definition is_sequiv_of_smap_pequiv {N : succ_str} {E F : gen_prespectrum N} (f : E →ₛ F) (H : is_sequiv_smap f) (n : N) : E n ≃* F n :=
  begin
    fapply pequiv_of_pmap,
    exact f n,
    fapply H,
  end

  definition is_sequiv_of_smap_inv {N : succ_str} {E F : gen_prespectrum N} (f : E →ₛ F) (H : is_sequiv_smap f) : F →ₛ E :=
  begin
    fapply smap.mk,
    intro n,
    exact (is_sequiv_of_smap_pequiv f H n)⁻¹ᵉ*,
    intro n,
    refine _ ⬝vp* (to_pinv_loopn_pequiv_loopn 1 (is_sequiv_of_smap_pequiv f H (S n)))⁻¹*,
    fapply phinverse,
    exact glue_square f n,
  end

  local postfix `⁻¹ˢ` : (max + 1) := is_sequiv_of_smap_inv

  definition is_sequiv_of_smap_isretr {N : succ_str} {E F : gen_prespectrum N} (f : E →ₛ F) (H : is_sequiv_smap f) : is_sequiv_of_smap_inv f H ∘ₛ f ~ₛ sid E :=
  begin
    fapply shomotopy.mk,
    intro n,
    fapply pleft_inv,
    intro n,
    refine _ ⬝hp** _,
    repeat exact sorry,
  end

  definition is_sequiv_of_smap_issec {N : succ_str} {E F : gen_prespectrum N} (f : E →ₛ F) (H : is_sequiv_smap f) : f ∘ₛ is_sequiv_of_smap_inv f H ~ₛ sid F :=
  begin
    repeat exact sorry
  end

  definition is_sequiv_of_smap {N : succ_str} {E F : gen_prespectrum N} (f : E →ₛ F) : is_sequiv_smap f → is_sequiv f :=
  begin
    intro H,
    fapply is_sequiv.mk,
    fapply is_sequiv_of_smap_inv f H,
    fapply is_sequiv_of_smap_isretr f H,
    fapply is_sequiv_of_smap_inv f H,
    fapply is_sequiv_of_smap_issec f H,
  end

  /---------
    Fibers
  ----------/

  definition sfiber [constructor] {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y) :
    gen_spectrum N :=
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
    : f ∘ₛ spoint f ~ₛ !szero :=
  begin
    fapply shomotopy.mk,
    { intro n, exact pcompose_ppoint (f n) },
    { intro n, exact sorry }
  end

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
  proof π→g[2] (f (2 - n)) qed

  definition shomotopy_group_isomorphism_of_pequiv (n : ℤ) {E F : spectrum} (f : Πn, E n ≃* F n) :
    πₛ[n] E ≃g πₛ[n] F :=
  proof homotopy_group_isomorphism_of_pequiv 1 (f (2 - n)) qed

  definition shomotopy_group_isomorphism_of_pequiv_nat (n : ℕ) {E F : spectrum}
    (f : Πn, E n ≃* F n) : πₛ[n] E ≃g πₛ[n] F :=
  shomotopy_group_isomorphism_of_pequiv n (spectrum_pequiv_of_nat f)

  notation `πₛ→[`:95 n:0 `]`:0 := shomotopy_group_fun n

  /- properties about homotopy groups -/
  definition equiv_glue_neg (X : spectrum) (n : ℤ) : X (2 - succ n) ≃* Ω (X (2 - n)) :=
  have H : succ (2 - succ n) = 2 - n, from ap succ !sub_sub⁻¹ ⬝ sub_add_cancel (2-n) 1,
  equiv_glue X (2 - succ n) ⬝e* loop_pequiv_loop (pequiv_of_eq (ap X H))

  definition π_glue (X : spectrum) (n : ℤ) : π[2] (X (2 - succ n)) ≃* π[3] (X (2 - n)) :=
  homotopy_group_pequiv 2 (equiv_glue_neg X n)

  definition πg_glue (X : spectrum) (n : ℤ) : πg[2] (X (2 - succ n)) ≃g πg[3] (X (2 - n)) :=
  begin
    change πg[2] (X (2 - succ n)) ≃g πg[2] (Ω (X (2 - n))),
    apply homotopy_group_isomorphism_of_pequiv,
    exact equiv_glue_neg X n
  end

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

  definition homotopy_group_spectrum_irrel_one {n m : ℤ} {k : ℕ} (E : spectrum) (p : n + 1 = m + k)
    [Hk : is_succ k] : πg[k] (E n) ≃g π₁ (E m) :=
  begin
    induction Hk with k,
    change π₁ (Ω[k] (E n)) ≃g π₁ (E m),
    apply homotopy_group_isomorphism_of_pequiv 0,
    symmetry,
    have m + k = n, from (pred_succ (m + k))⁻¹ ⬝ ap pred (add.assoc m k 1 ⬝ p⁻¹) ⬝ pred_succ n,
    induction (succ_str_add_eq_int_add m k ⬝ this),
    exact equiv_gluen E m k
  end

  definition homotopy_group_spectrum_irrel {n m : ℤ} {l k : ℕ} (E : spectrum) (p : n + l = m + k)
    [Hk : is_succ k] [Hl : is_succ l] : πg[k] (E n) ≃g πg[l] (E m) :=
  proof
  have Πa b c : ℤ, a + (b + c) = c + (b + a), from λa b c,
  !add.assoc⁻¹ ⬝ add.comm (a + b) c ⬝ ap (λx, c + x) (add.comm a b),
  have n + 1 = m + 1 - l + k, from
  ap succ (add_sub_cancel n l)⁻¹ ⬝ !add.assoc ⬝ ap (λx, x + (-l + 1)) p ⬝ !add.assoc ⬝
  ap (λx, m + x) (this k (-l) 1) ⬝ !add.assoc⁻¹ ⬝ !add.assoc⁻¹,
  homotopy_group_spectrum_irrel_one E this ⬝g
  (homotopy_group_spectrum_irrel_one E (sub_add_cancel (m+1) l)⁻¹)⁻¹ᵍ
  qed

  definition shomotopy_group_isomorphism_homotopy_group {n m : ℤ} {l : ℕ} (E : spectrum) (p : n + m = l)
    [H : is_succ l] : πₛ[n] E ≃g πg[l] (E m) :=
  have 2 - n + l = m + 2, from
  ap (λx, 2 - n + x) p⁻¹ ⬝ !add.assoc⁻¹ ⬝ ap (λx, x + m) (sub_add_cancel 2 n) ⬝ add.comm 2 m,
  homotopy_group_spectrum_irrel E this

  definition shomotopy_group_pequiv_homotopy_group_ab {n m : ℤ} {l : ℕ} (E : spectrum) (p : n + m = l)
    [H : is_at_least_two l] : πₛ[n] E ≃g πag[l] (E m) :=
  begin
    induction H with l,
    exact shomotopy_group_isomorphism_homotopy_group E p
  end

  definition shomotopy_group_pequiv_homotopy_group {n m : ℤ} {l : ℕ} (E : spectrum) (p : n + m = l) :
    πₛ[n] E ≃* π[l] (E m) :=
  begin
    cases l with l,
    { apply ptrunc_pequiv_ptrunc, symmetry,
      change E m ≃* Ω (Ω (E (2 - n))),
      refine !equiv_glue ⬝e* loop_pequiv_loop _,
      refine !equiv_glue ⬝e* loop_pequiv_loop _,
      apply pequiv_ap E,
      have -n = m, from neg_eq_of_add_eq_zero p,
      induction this,
      rexact add.assoc (-n) 1 1 ⬝ add.comm (-n) 2 },
    { exact pequiv_of_isomorphism (shomotopy_group_isomorphism_homotopy_group E p) }
  end

  /- the long exact sequence of homotopy groups for spectra -/
  section LES
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
  end LES

  /- homotopy group of a prespectrum -/

  definition pshomotopy_group_hom (n : ℤ) (E : prespectrum) (k : ℕ)
    : πag[k + 2] (E (-n - 2 + k)) →g πag[k + 3] (E (-n - 2 + (k + 1))) :=
  begin
    refine _ ∘g π→g[k+2] (glue E _),
    refine (ghomotopy_group_succ_in _ (k+1))⁻¹ᵍ ∘g _,
    refine homotopy_group_isomorphism_of_pequiv (k+1)
      (loop_pequiv_loop (pequiv_of_eq (ap E (add.assoc (-n - 2) k 1))))
  end

  definition pshomotopy_group (n : ℤ) (E : prespectrum) : AbGroup :=
  group.seq_colim (λ(k : ℕ), πag[k+2] (E (-n - 2 + k))) (pshomotopy_group_hom n E)

  notation `πₚₛ[`:95 n:0 `]`:0 := pshomotopy_group n

  definition pshomotopy_group_fun (n : ℤ) {E F : prespectrum} (f : E →ₛ F) :
    πₚₛ[n] E →g πₚₛ[n] F :=
  proof
  group.seq_colim_functor (λk, π→g[k+2] (f (-n - 2 +[ℤ] k)))
    begin
      intro k,
      note sq1 := homotopy_group_homomorphism_psquare (k+2) (ptranspose (smap.glue_square f (-n - 2 +[ℤ] k))),
      note sq2 := homotopy_group_functor_hsquare (k+2) (ap1_psquare (ptransport_natural E F f (add.assoc (-n - 2) k 1))),
      note sq3 := (homotopy_group_succ_in_natural (k+2) (f (-n - 2 +[ℤ] (k+1))))⁻¹ʰᵗʸʰ,
      note sq4 := hsquare_of_psquare sq2,
      note rect := sq1 ⬝htyh sq4 ⬝htyh sq3,
      exact sorry --sq1 ⬝htyh sq4 ⬝htyh sq3,
    end
  qed

  notation `πₚₛ→[`:95 n:0 `]`:0 := pshomotopy_group_fun n


  /- a chain complex of spectra (not yet used anywhere) -/

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


  ------------------------------
  -- Suspension prespectra
  ------------------------------

  -- Suspension prespectra are one that's naturally indexed on the natural numbers
  definition psp_susp (X : Type*) : gen_prespectrum +ℕ :=
    gen_prespectrum.mk (λn, iterate_susp n X) (λn, loop_susp_unit (iterate_susp n X))

  -- The sphere prespectrum
  definition psp_sphere : gen_prespectrum +ℕ :=
    psp_susp bool.pbool


  /-------------------------------
    Cotensor of spectra by types
  -------------------------------/

  -- Makes sense for any indexing succ_str.  Could be done for
  -- prespectra too, but as with truncation, why bother?

  definition sp_cotensor [constructor] {N : succ_str} (A : Type*) (B : gen_spectrum N) :
    gen_spectrum N :=
    spectrum.MK (λn, ppmap A (B n))
      (λn, (loop_ppmap_commute A (B (S n)))⁻¹ᵉ* ∘*ᵉ (pequiv_ppcompose_left (equiv_glue B n)))

  /- unpointed cotensor -/
  definition sp_ucotensor [constructor] {N : succ_str} (A : Type) (B : gen_spectrum N) :
    gen_spectrum N :=
  spectrum.MK (λn, A →ᵘ* B n)
              (λn, pumap_pequiv_right A (equiv_glue B n) ⬝e* (loop_pumap A (B (S n)))⁻¹ᵉ*)

  ----------------------------------------
  -- Sections of parametrized spectra
  ----------------------------------------

  definition spi [constructor] {N : succ_str} (A : Type*) (E : A → gen_spectrum N) :
    gen_spectrum N :=
  spectrum.MK (λn, Π*a, E a n)
    (λn, !loop_pppi_pequiv⁻¹ᵉ* ∘*ᵉ ppi_pequiv_right (λa, equiv_glue (E a) n))

  definition spi_compose_left [constructor] {N : succ_str} {A : Type*} {E F : A -> gen_spectrum N}
    (f : Πa, E a →ₛ F a) : spi A E →ₛ spi A F :=
  smap.mk (λn, pppi_compose_left (λa, f a n))
    begin
      intro n,
      exact psquare_pppi_compose_left (λa, (glue_square (f a) n)) ⬝v* !loop_pppi_pequiv_natural⁻¹ᵛ*
    end

  -- unpointed spi
  definition supi [constructor] {N : succ_str} (A : Type) (E : A → gen_spectrum N) :
    gen_spectrum N :=
  spectrum.MK (λn, Πᵘ*a, E a n)
              (λn, pupi_pequiv_right (λa, equiv_glue (E a) n) ⬝e* (loop_pupi (λa, E a (S n)))⁻¹ᵉ*)

  /- Mapping spectra -/
  -- note: see also cotensor above

  /-
    suspension of a spectrum

    this is just a shift. We could call a shift in the other direction loopn,
    though it might be more convenient to just take a negative suspension
  -/

  definition ssusp [constructor] {N : succ_str} (X : gen_spectrum N) : gen_spectrum N :=
  spectrum.MK (λn, X (S n)) (λn, equiv_glue X (S n))

  definition ssuspn [constructor] (k : ℤ) (X : spectrum) : spectrum :=
  spectrum.MK (λn, X (n + k))
              (λn, equiv_glue X (n + k) ⬝e* loop_pequiv_loop (pequiv_ap X !add.right_comm))

  definition shomotopy_group_ssuspn (k : ℤ) (X : spectrum) (n : ℤ) :
    πₛ[k] (ssuspn n X) ≃g πₛ[k - n] X :=
  have k - n + (2 - k + n) = 2, from
  !add.comm ⬝
  ap (λx, x + (k - n)) (!add.assoc ⬝ ap (λx, 2 + x) (ap (λx, -k + x) !neg_neg⁻¹ ⬝ !neg_add⁻¹)) ⬝
  sub_add_cancel 2 (k - n),
  (shomotopy_group_isomorphism_homotopy_group X this)⁻¹ᵍ

  /- Tensor by spaces -/

  /- Cofibers and stability -/

  ------------------------------
  -- Contractible spectrum
  ------------------------------

  definition sunit.{u} [constructor] : spectrum.{u} :=
  spectrum.MK (λn, plift punit) (λn, pequiv_of_is_contr _ _ _ _)

  definition shomotopy_group_sunit.{u} (n : ℤ) : πₛ[n] sunit.{u} ≃g trivial_ab_group_lift.{u} :=
  phomotopy_group_plift_punit 2

  definition add_point_spectrum [constructor] {X : Type} (Y : X → spectrum) (x : X₊) : spectrum :=
  spectrum.MK (λn, add_point_over (λx, Y x n) x)
    begin
      intro n, induction x with x,
        apply pequiv_of_is_contr,
          apply is_trunc_lift,
        apply is_contr_loop_of_is_contr, apply is_trunc_lift,
      exact equiv_glue (Y x) n
    end

  open option
  definition shomotopy_group_add_point_spectrum {X : Type} (Y : X → spectrum) (n : ℤ) :
    Π(x : X₊), πₛ[n] (add_point_spectrum Y x) ≃g add_point_AbGroup (λ (x : X), πₛ[n] (Y x)) x
  | (some x) := by reflexivity
  | none     := proof phomotopy_group_plift_punit 2 qed

  /- The Eilenberg-MacLane spectrum -/

  definition EM_spectrum /-[constructor]-/ (G : AbGroup) : spectrum :=
  spectrum.Mk (K G) (λn, (loop_EM G n)⁻¹ᵉ*)

  definition EM_spectrum_pequiv {G H : AbGroup} (e : G ≃g H) (n : ℤ) :
    EM_spectrum G n ≃* EM_spectrum H n :=
  spectrum_pequiv_of_nat (λk, EM_pequiv_EM k e) n

  definition EM_spectrum_trivial.{u} (n : ℤ) :
    EM_spectrum trivial_ab_group_lift.{u} n ≃* trivial_ab_group_lift.{u} :=
  pequiv_of_is_contr _ _
    (is_contr_spectrum_of_nat (λk, is_contr_EM k !is_trunc_lift) n)
    !is_trunc_lift

  definition is_contr_EM_spectrum_neg (G : AbGroup) (n : ℕ) : is_contr (EM_spectrum G (-[1+n])) :=
  begin
    induction n with n IH,
    { apply is_contr_loop, exact is_trunc_EM G 0 },
    { apply is_contr_loop_of_is_contr, exact IH }
  end

  /- K(πₗ(Aₖ),l) ≃* K(πₙ(A),l) for l = n + k -/
  definition EM_type_pequiv_EM (A : spectrum) {n k : ℤ} {l : ℕ} (p : n + k = l) :
    EM_type (A k) l ≃* EM (πₛ[n] A) l :=
  begin
    symmetry,
    cases l with l,
    { exact shomotopy_group_pequiv_homotopy_group A p },
    { cases l with l,
      { apply EM1_pequiv_EM1, exact shomotopy_group_isomorphism_homotopy_group A p },
      { apply EMadd1_pequiv_EMadd1 (l+1), exact shomotopy_group_isomorphism_homotopy_group A p }}
  end

  /- Wedge of prespectra -/

open fwedge

  definition fwedge_prespectrum.{u v} {I : Type.{v}} (X : I -> prespectrum.{u}) : prespectrum.{max u v} :=
  begin
    fconstructor,
    { intro n, exact fwedge (λ i, X i n) },
    { intro n, fapply fwedge_pmap,
      intro i, exact Ω→ !pinl ∘* !glue }
  end

end spectrum
