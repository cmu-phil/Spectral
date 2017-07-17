/-
Copyright (c) 2017 Yuri Sulyma, Favonia
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuri Sulyma, Favonia, Floris van Doorn

Reduced homology theories
-/

import ..spectrum.smash ..homotopy.wedge

open eq spectrum int pointed group algebra sphere nat equiv susp is_trunc
     function fwedge cofiber lift is_equiv choice algebra pi smash wedge

namespace homology

  /- homology theory -/
  structure homology_theory.{u} : Type.{u+1} :=
    (HH : ℤ → pType.{u} → AbGroup.{u})
    (Hh : Π(n : ℤ) {X Y : Type*} (f : X →* Y), HH n X →g HH n Y)
    (Hpid : Π(n : ℤ) {X : Type*} (x : HH n X), Hh n (pid X) x = x)
    (Hpcompose : Π(n : ℤ) {X Y Z : Type*} (f : Y →* Z) (g : X →* Y),
      Hh n (f ∘* g) ~ Hh n f ∘ Hh n g)
    (Hpsusp : Π(n : ℤ) (X : Type*), HH (succ n) (psusp X) ≃g HH n X)
    (Hpsusp_natural : Π(n : ℤ) {X Y : Type*} (f : X →* Y),
      Hpsusp n Y ∘ Hh (succ n) (psusp_functor f) ~ Hh n f ∘ Hpsusp n X)
    (Hexact : Π(n : ℤ) {X Y : Type*} (f : X →* Y), is_exact_g (Hh n f) (Hh n (pcod f)))
    (Hadditive : Π(n : ℤ) {I : Set.{u}} (X : I → Type*), is_equiv
      (dirsum_elim (λi, Hh n (pinl i)) : dirsum (λi, HH n (X i)) → HH n (⋁ X)))

  structure ordinary_homology_theory.{u} extends homology_theory.{u} : Type.{u+1} :=
    (Hdimension : Π(n : ℤ), n ≠ 0 → is_contr (HH n (plift (psphere 0))))

  section
    universe variable u
    parameter (theory : homology_theory.{u})
    open homology_theory

    theorem HH_base_indep (n : ℤ) {A : Type} (a b : A)
      : HH theory n (pType.mk A a) ≃g HH theory n (pType.mk A b) :=
      calc HH theory n (pType.mk A a) ≃g HH theory (int.succ n) (psusp A) : by exact (Hpsusp theory n (pType.mk A a)) ⁻¹ᵍ
                                  ... ≃g HH theory n (pType.mk A b)       : by exact Hpsusp theory n (pType.mk A b)

    theorem Hh_homotopy' (n : ℤ) {A B : Type*} (f : A → B) (p q : f pt = pt)
      : Hh theory n (pmap.mk f p) ~ Hh theory n (pmap.mk f q) := λ x,
    calc       Hh theory n (pmap.mk f p) x
             = Hh theory n (pmap.mk f p) (Hpsusp theory n A ((Hpsusp theory n A)⁻¹ᵍ x))
               : by exact ap (Hh theory n (pmap.mk f p)) (equiv.to_right_inv (equiv_of_isomorphism (Hpsusp theory n A)) x)⁻¹
         ... = Hpsusp theory n B (Hh theory (succ n) (pmap.mk (susp.functor f) !refl) ((Hpsusp theory n A)⁻¹ x))
               : by exact (Hpsusp_natural theory n (pmap.mk f p) ((Hpsusp theory n A)⁻¹ᵍ x))⁻¹
         ... = Hh theory n (pmap.mk f q) (Hpsusp theory n A ((Hpsusp theory n A)⁻¹ x))
               : by exact Hpsusp_natural theory n (pmap.mk f q) ((Hpsusp theory n A)⁻¹ x)
         ... = Hh theory n (pmap.mk f q) x
               : by exact ap (Hh theory n (pmap.mk f q)) (equiv.to_right_inv (equiv_of_isomorphism (Hpsusp theory n A)) x)

    theorem Hh_homotopy (n : ℤ) {A B : Type*} (f g : A →* B) (h : f ~ g) : Hh theory n f ~ Hh theory n g := λ x,
    calc       Hh theory n f x
             = Hh theory n (pmap.mk f (respect_pt f)) x : by exact ap (λ f, Hh theory n f x) (pmap.eta f)⁻¹
         ... = Hh theory n (pmap.mk f (h pt ⬝ respect_pt g)) x : by exact Hh_homotopy' n f (respect_pt f) (h pt ⬝ respect_pt g) x
         ... = Hh theory n g x : by exact ap (λ f, Hh theory n f x) (@pmap_eq _ _ (pmap.mk f (h pt ⬝ respect_pt g)) _ h (refl (h pt ⬝ respect_pt g)))

    definition HH_isomorphism (n : ℤ) {A B : Type*} (e : A ≃* B)
      : HH theory n A ≃g HH theory n B :=
    begin
      fapply isomorphism.mk,
      { exact Hh theory n e },
      fapply adjointify,
      { exact Hh theory n e⁻¹ᵉ* },
      { intro x, exact calc
              Hh theory n e (Hh theory n e⁻¹ᵉ* x)
            = Hh theory n (e ∘* e⁻¹ᵉ*) x : by exact (Hpcompose theory n e e⁻¹ᵉ* x)⁻¹
        ... = Hh theory n !pid x : by exact Hh_homotopy n (e ∘* e⁻¹ᵉ*) !pid (to_right_inv e) x
        ... = x : by exact Hpid theory n x
      },
      { intro x, exact calc
              Hh theory n e⁻¹ᵉ* (Hh theory n e x)
            = Hh theory n (e⁻¹ᵉ* ∘* e) x : by exact (Hpcompose theory n e⁻¹ᵉ* e x)⁻¹
        ... = Hh theory n !pid x : by exact Hh_homotopy n (e⁻¹ᵉ* ∘* e) !pid (to_left_inv e) x
        ... = x : by exact Hpid theory n x
      }
    end

    definition Hadditive_equiv (n : ℤ) {I : Type} [is_set I] (X : I → Type*)
      : dirsum (λi, HH theory n (X i)) ≃g HH theory n (⋁ X) :=
    isomorphism.mk (dirsum_elim (λi, Hh theory n (fwedge.pinl i))) (Hadditive theory n X)

    definition Hadditive' (n : ℤ) {I : Type₀} [is_set I] (X : I → pType.{u}) : is_equiv
      (dirsum_elim (λi, Hh theory n (pinl i)) : dirsum (λi, HH theory n (X i)) → HH theory n (⋁ X)) :=
    let iso3 := HH_isomorphism n (fwedge_down_left.{0 u} X) in
    let iso2 := Hadditive_equiv n (X ∘ down.{0 u}) in
    let iso1 := (dirsum_down_left.{0 u} (λ i, HH theory n (X i)))⁻¹ᵍ in
    let iso := calc dirsum (λ i, HH theory n (X i))
                 ≃g dirsum (λ i, HH theory n (X (down.{0 u} i))) : by exact iso1
             ... ≃g HH theory n (⋁ (X ∘ down.{0 u})) : by exact iso2
             ... ≃g HH theory n (⋁ X) : by exact iso3
    in
    begin
      fapply is_equiv_of_equiv_of_homotopy,
      { exact equiv_of_isomorphism iso  },
      { refine dirsum_homotopy _, intro i y,
        refine homomorphism_comp_compute iso3 (iso2 ∘g iso1) _ ⬝ _,
        refine ap iso3 (homomorphism_comp_compute iso2 iso1 _) ⬝ _,
        refine ap (iso3 ∘ iso2) _ ⬝ _,
        { exact dirsum_incl (λ i, HH theory n (X (down i))) (up i) y },
        { refine _ ⬝ dirsum_elim_compute (λi, dirsum_incl (λ i, HH theory n (X (down.{0 u} i))) (up i)) i y,
          reflexivity
        },
        refine ap iso3 _ ⬝ _,
        { exact Hh theory n (fwedge.pinl (up i)) y },
        { refine _ ⬝ dirsum_elim_compute (λi, Hh theory n (fwedge.pinl i)) (up i) y,
          reflexivity
        },
        refine (Hpcompose theory n (fwedge_down_left X) (fwedge.pinl (up i)) y)⁻¹ ⬝ _,
        refine Hh_homotopy n (fwedge_down_left.{0 u} X ∘* fwedge.pinl (up i)) (fwedge.pinl i) (fwedge_pmap_beta (λ i, pinl (down i)) (up i)) y ⬝ _,
        refine (dirsum_elim_compute (λ i, Hh theory n (pinl i)) i y)⁻¹
      }
    end

    definition Hadditive'_equiv (n : ℤ) {I : Type₀} [is_set I] (X : I → Type*)
      : dirsum (λi, HH theory n (X i)) ≃g HH theory n (⋁ X) :=
    isomorphism.mk (dirsum_elim (λi, Hh theory n (fwedge.pinl i))) (Hadditive' n X)

    definition Hfwedge (n : ℤ) {I : Type} [is_set I] (X : I → Type*): HH theory n (⋁ X) ≃g dirsum (λi, HH theory n (X i)) :=
      (isomorphism.mk _ (Hadditive theory n X))⁻¹ᵍ

    definition Hpwedge (n : ℤ) (A B : Type*) : HH theory n (pwedge A B) ≃g HH theory n A ×g HH theory n B :=
    calc HH theory n (A ∨ B) ≃g HH theory n (⋁ (bool.rec A B)) : by exact HH_isomorphism n (pwedge_pequiv_fwedge A B)
                         ... ≃g dirsum (λb, HH theory n (bool.rec A B b)) : by exact (Hadditive'_equiv n (bool.rec A B))⁻¹ᵍ
                         ... ≃g dirsum (bool.rec (HH theory n A) (HH theory n B)) : by exact dirsum_isomorphism (bool.rec !isomorphism.refl !isomorphism.refl)
                         ... ≃g HH theory n A ×g HH theory n B : by exact binary_dirsum (HH theory n A) (HH theory n B)

  end
  section
    universe variables u v
    parameter (theory : homology_theory.{max u v})
    open homology_theory

    definition Hplift_psusp (n : ℤ) (A : Type*): HH theory (n + 1) (plift.{u v} (psusp A)) ≃g HH theory n (plift.{u v} A) :=
    calc HH theory (n + 1) (plift.{u v} (psusp A)) ≃g HH theory (n + 1) (psusp (plift.{u v} A)) : by exact HH_isomorphism theory (n + 1) (plift_psusp _)
                                               ... ≃g HH theory n (plift.{u v} A) : by exact Hpsusp theory n (plift.{u v} A)

    definition Hplift_pwedge (n : ℤ) (A B : Type*): HH theory n (plift.{u v} (A ∨ B)) ≃g HH theory n (plift.{u v} A) ×g HH theory n (plift.{u v} B) :=
    calc HH theory n (plift.{u v} (A ∨ B)) ≃g HH theory n (plift.{u v} A ∨ plift.{u v} B) : by exact HH_isomorphism theory n (plift_pwedge A B)
                                       ... ≃g HH theory n (plift.{u v} A) ×g HH theory n (plift.{u v} B) : by exact Hpwedge theory n (plift.{u v} A) (plift.{u v} B)

    definition Hplift_isomorphism (n : ℤ) {A B : Type*} (e : A ≃* B) : HH theory n (plift.{u v} A) ≃g HH theory n (plift.{u v} B) :=
      HH_isomorphism theory n (!pequiv_plift⁻¹ᵉ* ⬝e* e ⬝e* !pequiv_plift)

  end

/- homology theory associated to a prespectrum -/
definition homology (X : Type*) (E : prespectrum) (n : ℤ) : AbGroup :=
pshomotopy_group n (smash_prespectrum X E)

/- an alternative definition, which might be a bit harder to work with -/
definition homology_spectrum (X : Type*) (E : spectrum) (n : ℤ) : AbGroup :=
shomotopy_group n (smash_spectrum X E)

definition parametrized_homology {X : Type*} (E : X → spectrum) (n : ℤ) : AbGroup :=
sorry

definition ordinary_homology [reducible] (X : Type*) (G : AbGroup) (n : ℤ) : AbGroup :=
homology X (EM_spectrum G) n

definition ordinary_homology_Z [reducible] (X : Type*) (n : ℤ) : AbGroup :=
ordinary_homology X agℤ n

notation `H_` n `[`:0 X:0 `, ` E:0 `]`:0 := homology X E n
notation `H_` n `[`:0 X:0 `]`:0 := ordinary_homology_Z X n
notation `pH_` n `[`:0 binders `, ` r:(scoped E, parametrized_homology E n) `]`:0 := r

definition unpointed_homology (X : Type) (E : spectrum) (n : ℤ) : AbGroup :=
H_ n[X₊, E]

definition homology_functor [constructor] {X Y : Type*} {E F : prespectrum} (f : X →* Y)
  (g : E →ₛ F) (n : ℤ) : homology X E n →g homology Y F n :=
pshomotopy_group_fun n (smash_prespectrum_fun f g)

definition homology_theory_spectrum_is_exact.{u} (E : spectrum.{u}) (n : ℤ) {X Y : Type*} (f : X →* Y) :
  is_exact_g (homology_functor f (sid (gen_spectrum.to_prespectrum E)) n)
      (homology_functor (pcod f) (sid (gen_spectrum.to_prespectrum E)) n) :=
begin
  esimp[is_exact_g],
  -- fconstructor,
  -- { intro a, exact sorry },
  -- { intro a, exact sorry }
  exact sorry
end

definition homology_theory_spectrum.{u} [constructor] (E : spectrum.{u}) : homology_theory.{u} :=
begin
  fapply homology_theory.mk,
  exact (λn X, H_ n[X, E]),
  exact (λn X Y f, homology_functor f (sid E) n),
  exact sorry, -- Hid is uninteresting but potentially very hard to prove
  exact sorry,
  exact sorry,
  exact sorry,
  apply homology_theory_spectrum_is_exact,
  exact sorry
  -- sorry
  -- sorry
  -- sorry
  -- sorry
  -- sorry
  -- sorry
--  (λn A, H^n[A, Y])
--  (λn A B f, cohomology_isomorphism f Y n)
--  (λn A, cohomology_isomorphism_refl A Y n)
--  (λn A B f, cohomology_functor f Y n)
--  (λn A B f g p, cohomology_functor_phomotopy p Y n)
--  (λn A B f x, cohomology_functor_phomotopy_refl f Y n x)
--  (λn A x, cohomology_functor_pid A Y n x)
--  (λn A B C g f x, cohomology_functor_pcompose g f Y n x)
--  (λn A, cohomology_psusp A Y n)
--  (λn A B f, cohomology_psusp_natural f Y n)
--  (λn A B f, cohomology_exact f Y n)
--  (λn I A H, spectrum_additive H A Y n)
end
end homology
