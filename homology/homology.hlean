import ..homotopy.spectrum ..homotopy.EM ..algebra.arrow_group ..algebra.direct_sum ..homotopy.fwedge ..choice ..homotopy.pushout ..move_to_lib

open eq spectrum int pointed group algebra sphere nat equiv susp is_trunc
     function fwedge cofiber lift is_equiv choice algebra pi smash

namespace homology

  /- homology theory -/

  structure homology_theory.{u} : Type.{u+1} :=
    (HH : ℤ → pType.{u} → AbGroup.{u})
    (Hh : Π(n : ℤ) {X Y : Type*} (f : X →* Y), HH n X →g HH n Y)
    (Hid : Π(n : ℤ) {X : Type*} (x : HH n X), Hh n (pid X) x = x)
    (Hcompose : Π(n : ℤ) {X Y Z : Type*} (f : Y →* Z) (g : X →* Y),
      Hh n (f ∘* g) ~ Hh n f ∘ Hh n g)
    (Hsusp : Π(n : ℤ) (X : Type*), HH (succ n) (psusp X) ≃g HH n X)
    (Hsusp_natural : Π(n : ℤ) {X Y : Type*} (f : X →* Y),
      Hsusp n Y ∘ Hh (succ n) (psusp_functor f) ~ Hh n f ∘ Hsusp n X)
    (Hexact : Π(n : ℤ) {X Y : Type*} (f : X →* Y), is_exact_g (Hh n f) (Hh n (pcod f)))
    (Hadditive : Π(n : ℤ) {I : Set.{u}} (X : I → Type*), is_equiv
      (dirsum_elim (λi, Hh n (pinl i)) : dirsum (λi, HH n (X i)) → HH n (⋁ X)))

  section
    parameter (theory : homology_theory)
    open homology_theory

    theorem HH_base_indep (n : ℤ) {A : Type} (a b : A)
      : HH theory n (pType.mk A a) ≃g HH theory n (pType.mk A b) :=
      calc HH theory n (pType.mk A a) ≃g HH theory (int.succ n) (psusp A) : by exact (Hsusp theory n (pType.mk A a)) ⁻¹ᵍ
                                  ... ≃g HH theory n (pType.mk A b)       : by exact Hsusp theory n (pType.mk A b)

    theorem Hh_homotopy' (n : ℤ) {A B : Type*} (f : A → B) (p q : f pt = pt)
      : Hh theory n (pmap.mk f p) ~ Hh theory n (pmap.mk f q) := λ x,
    calc       Hh theory n (pmap.mk f p) x
             = Hh theory n (pmap.mk f p) (Hsusp theory n A ((Hsusp theory n A)⁻¹ᵍ x))
               : by exact ap (Hh theory n (pmap.mk f p)) (equiv.to_right_inv (equiv_of_isomorphism (Hsusp theory n A)) x)⁻¹
         ... = Hsusp theory n B (Hh theory (succ n) (pmap.mk (susp.functor f) !refl) ((Hsusp theory n A)⁻¹ x))
               : by exact (Hsusp_natural theory n (pmap.mk f p) ((Hsusp theory n A)⁻¹ᵍ x))⁻¹
         ... = Hh theory n (pmap.mk f q) (Hsusp theory n A ((Hsusp theory n A)⁻¹ x))
               : by exact Hsusp_natural theory n (pmap.mk f q) ((Hsusp theory n A)⁻¹ x)
         ... = Hh theory n (pmap.mk f q) x
               : by exact ap (Hh theory n (pmap.mk f q)) (equiv.to_right_inv (equiv_of_isomorphism (Hsusp theory n A)) x)

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
            = Hh theory n (e ∘* e⁻¹ᵉ*) x : by exact (Hcompose theory n e e⁻¹ᵉ* x)⁻¹
        ... = Hh theory n !pid x : by exact Hh_homotopy n (e ∘* e⁻¹ᵉ*) !pid (to_right_inv e) x
        ... = x : by exact Hid theory n x
      },
      { intro x, exact calc
              Hh theory n e⁻¹ᵉ* (Hh theory n e x)
            = Hh theory n (e⁻¹ᵉ* ∘* e) x : by exact (Hcompose theory n e⁻¹ᵉ* e x)⁻¹
        ... = Hh theory n !pid x : by exact Hh_homotopy n (e⁻¹ᵉ* ∘* e) !pid (to_left_inv e) x
        ... = x : by exact Hid theory n x
      }
    end

  end

/- homology theory associated to a spectrum -/
definition homology (X : Type*) (E : spectrum) (n : ℤ) : AbGroup :=
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

definition homology_functor [constructor] {X Y : Type*} {E F : spectrum} (f : X →* Y) (g : E →ₛ F) (n : ℤ) : homology X E n →g homology Y F n :=
shomotopy_group_fun n (smash_spectrum_fun f g)

definition homology_theory_spectrum.{u} [constructor] (E : spectrum.{u}) : homology_theory.{u} :=
begin
  refine homology_theory.mk _ _ _ _ _ _ _ _,
  exact (λn X, H_ n[X, E]),
  exact (λn X Y f, homology_functor f (sid E) n),
  exact sorry, -- Hid is uninteresting but potentially very hard to prove
  exact sorry,
  exact sorry,
  exact sorry,
  exact sorry,
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
