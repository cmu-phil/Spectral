/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Reduced cohomology
-/

import .spectrum .EM ..algebra.arrow_group .fwedge ..choice .pushout ..move_to_lib

open eq spectrum int trunc pointed EM group algebra circle sphere nat EM.ops equiv susp is_trunc
     function fwedge cofiber bool lift sigma is_equiv choice pushout algebra

-- TODO: move
structure is_exact {A B : Type} {C : Type*} (f : A → B) (g : B → C) :=
  ( im_in_ker : Π(a:A), g (f a) = pt)
  ( ker_in_im : Π(b:B), (g b = pt) → image f b)

definition is_exact_g {A B C : Group} (f : A →g B) (g : B →g C) :=
is_exact f g

definition is_exact_g.mk {A B C : Group} {f : A →g B} {g : B →g C}
  (H₁ : Πa, g (f a) = 1) (H₂ : Πb, g b = 1 → image f b) : is_exact_g f g :=
is_exact.mk H₁ H₂

definition is_exact_trunc_functor {A B : Type} {C : Type*} {f : A → B} {g : B → C}
  (H : is_exact_t f g) : @is_exact _ _ (ptrunc 0 C) (trunc_functor 0 f) (trunc_functor 0 g) :=
begin
  constructor,
  { intro a, esimp, induction a with a,
    exact ap tr (is_exact_t.im_in_ker H a) },
  { intro b p, induction b with b, note q := !tr_eq_tr_equiv p, induction q with q,
    induction is_exact_t.ker_in_im H b q with a r,
    exact image.mk (tr a) (ap tr r) }
end

definition is_exact_homotopy {A B C : Type*} {f f' : A → B} {g g' : B → C}
  (p : f ~ f') (q : g ~ g') (H : is_exact f g) : is_exact f' g' :=
begin
  induction p using homotopy.rec_on_idp,
  induction q using homotopy.rec_on_idp,
  assumption
end

-- move to arrow group

definition ap1_pmap_mul {X Y : Type*} (f g : X →* Ω Y) :
  Ω→ (pmap_mul f g) ~* pmap_mul (Ω→ f) (Ω→ g) :=
begin
  fconstructor,
  { intro p, esimp,
    refine ap1_gen_con_left p (respect_pt f) (respect_pt f)
             (respect_pt g) (respect_pt g) ⬝ _,
    refine !whisker_right_idp ◾ !whisker_left_idp2, },
  { refine !con.assoc ⬝ _,
    refine _ ◾ idp ⬝ _, rotate 1,
    rexact ap1_gen_con_left_idp (respect_pt f) (respect_pt g), esimp,
    refine !con.assoc ⬝ _,
    apply whisker_left, apply inv_con_eq_idp,
    refine !con2_con_con2 ⬝ ap011 concat2 _ _:
      refine eq_of_square (!natural_square ⬝hp !ap_id) ⬝ !con_idp }
end

definition pmap_mul_pcompose {A B C : Type*} (g h : B →* Ω C) (f : A →* B) :
  pmap_mul g h ∘* f ~* pmap_mul (g ∘* f) (h ∘* f) :=
begin
  fconstructor,
  { intro p, reflexivity },
  { esimp, refine !idp_con ⬝ _, refine !con2_con_con2⁻¹ ⬝ whisker_right _ _,
    refine !ap_eq_ap011⁻¹ }
end

definition pcompose_pmap_mul {A B C : Type*} (h : B →* C) (f g : A →* Ω B) :
  Ω→ h ∘* pmap_mul f g ~* pmap_mul (Ω→ h ∘* f) (Ω→ h ∘* g) :=
begin
  fconstructor,
  { intro p, exact ap1_con2 h (f p) (g p) },
  { refine whisker_left _ !con2_con_con2⁻¹ ⬝ _, refine !con.assoc⁻¹ ⬝ _,
    refine whisker_right _ (eq_of_square !ap1_gen_con_natural) ⬝ _,
    refine !con.assoc ⬝ whisker_left _ _, apply ap1_gen_con_idp }
end

definition loop_psusp_intro_pmap_mul {X Y : Type*} (f g : psusp X →* Ω Y) :
  loop_psusp_intro (pmap_mul f g) ~* pmap_mul (loop_psusp_intro f) (loop_psusp_intro g) :=
pwhisker_right _ !ap1_pmap_mul ⬝* !pmap_mul_pcompose

namespace cohomology

definition EM_spectrum /-[constructor]-/ (G : AbGroup) : spectrum :=
spectrum.Mk (K G) (λn, (loop_EM G n)⁻¹ᵉ*)

definition cohomology (X : Type*) (Y : spectrum) (n : ℤ) : AbGroup :=
AbGroup_trunc_pmap X (Y (n+2))

definition ordinary_cohomology [reducible] (X : Type*) (G : AbGroup) (n : ℤ) : AbGroup :=
cohomology X (EM_spectrum G) n

definition ordinary_cohomology_Z [reducible] (X : Type*) (n : ℤ) : AbGroup :=
ordinary_cohomology X agℤ n

notation `H^` n `[`:0 X:0 `, ` Y:0 `]`:0 := cohomology X Y n
notation `H^` n `[`:0 X:0 `]`:0 := ordinary_cohomology_Z X n

-- check H^3[S¹*,EM_spectrum agℤ]
-- check H^3[S¹*]

definition unpointed_cohomology (X : Type) (Y : spectrum) (n : ℤ) : AbGroup :=
cohomology X₊ Y n

/- functoriality -/

definition cohomology_functor [constructor] {X X' : Type*} (f : X' →* X) (Y : spectrum)
  (n : ℤ) : cohomology X Y n →g cohomology X' Y n :=
Group_trunc_pmap_homomorphism f

definition cohomology_functor_pid (X : Type*) (Y : spectrum) (n : ℤ) (f : H^n[X, Y]) :
  cohomology_functor (pid X) Y n f = f :=
!Group_trunc_pmap_pid

definition cohomology_functor_pcompose {X X' X'' : Type*} (f : X' →* X) (g : X'' →* X')
  (Y : spectrum) (n : ℤ) (h : H^n[X, Y]) : cohomology_functor (f ∘* g) Y n h =
  cohomology_functor g Y n (cohomology_functor f Y n h) :=
!Group_trunc_pmap_pcompose

definition cohomology_functor_phomotopy {X X' : Type*} {f g : X' →* X} (p : f ~* g)
  (Y : spectrum) (n : ℤ) : cohomology_functor f Y n ~ cohomology_functor g Y n :=
Group_trunc_pmap_phomotopy p

definition cohomology_functor_pconst {X X' : Type*} (Y : spectrum) (n : ℤ) (f : H^n[X, Y]) :
  cohomology_functor (pconst X' X) Y n f = 1 :=
!Group_trunc_pmap_pconst

/- suspension axiom -/

definition cohomology_psusp_2 (Y : spectrum) (n : ℤ) :
  Ω (Ω[2] (Y ((n+1)+2))) ≃* Ω[2] (Y (n+2)) :=
begin
  apply loopn_pequiv_loopn 2,
  exact loop_pequiv_loop (pequiv_of_eq (ap Y (add_comm_right n 1 2))) ⬝e* !equiv_glue⁻¹ᵉ*
end

definition cohomology_psusp_1 (X : Type*) (Y : spectrum) (n : ℤ) :
  psusp X →* Ω (Ω (Y (n + 1 + 2))) ≃ X →* Ω (Ω (Y (n+2))) :=
calc
  psusp X →* Ω[2] (Y (n + 1 + 2)) ≃ X →* Ω (Ω[2] (Y (n + 1 + 2))) : psusp_adjoint_loop_unpointed
    ... ≃ X →* Ω[2] (Y (n+2)) : equiv_of_pequiv (pequiv_ppcompose_left
                                                  (cohomology_psusp_2 Y n))

definition cohomology_psusp_1_pmap_mul {X : Type*} {Y : spectrum} {n : ℤ}
  (f g : psusp X →* Ω (Ω (Y (n + 1 + 2)))) : cohomology_psusp_1 X Y n (pmap_mul f g) ~*
  pmap_mul (cohomology_psusp_1 X Y n f) (cohomology_psusp_1 X Y n g) :=
begin
  unfold [cohomology_psusp_1],
  refine pwhisker_left _ !loop_psusp_intro_pmap_mul ⬝* _,
  apply pcompose_pmap_mul
end

definition cohomology_psusp_equiv (X : Type*) (Y : spectrum) (n : ℤ) :
  H^n+1[psusp X, Y] ≃ H^n[X, Y] :=
trunc_equiv_trunc _ (cohomology_psusp_1 X Y n)

definition cohomology_psusp (X : Type*) (Y : spectrum) (n : ℤ) :
  H^n+1[psusp X, Y] ≃g H^n[X, Y] :=
isomorphism_of_equiv (cohomology_psusp_equiv X Y n)
  begin
    intro f₁ f₂, induction f₁ with f₁, induction f₂ with f₂,
    apply ap tr, apply eq_of_phomotopy, exact cohomology_psusp_1_pmap_mul f₁ f₂
  end

definition cohomology_psusp_natural {X X' : Type*} (f : X →* X') (Y : spectrum) (n : ℤ) :
  cohomology_psusp X Y n ∘ cohomology_functor (psusp_functor f) Y (n+1) ~
  cohomology_functor f Y n ∘ cohomology_psusp X' Y n :=
begin
  refine (trunc_functor_compose _ _ _)⁻¹ʰᵗʸ ⬝hty _ ⬝hty trunc_functor_compose _ _ _,
  apply trunc_functor_homotopy, intro g,
  apply eq_of_phomotopy, refine _ ⬝* !passoc⁻¹*, apply pwhisker_left,
  apply loop_psusp_intro_natural
end

/- exactness -/

definition cohomology_exact {X X' : Type*} (f : X →* X') (Y : spectrum) (n : ℤ) :
  is_exact_g (cohomology_functor (pcod f) Y n) (cohomology_functor f Y n) :=
is_exact_trunc_functor (cofiber_exact f)

/- additivity -/

definition additive_hom [constructor] {I : Type} (X : I → Type*) (Y : spectrum) (n : ℤ) :
  H^n[⋁X, Y] →g Πᵍ i, H^n[X i, Y] :=
Group_pi_intro (λi, cohomology_functor (pinl i) Y n)

definition additive_equiv.{u} {I : Type.{u}} (H : has_choice 0 I) (X : I → Type*) (Y : spectrum)
  (n : ℤ) : H^n[⋁X, Y] ≃ Πᵍ i, H^n[X i, Y] :=
trunc_fwedge_pmap_equiv H X (Ω[2] (Y (n+2)))

definition additive {I : Type} (H : has_choice 0 I) (X : I → Type*) (Y : spectrum) (n : ℤ) :
  is_equiv (additive_hom X Y n) :=
is_equiv_of_equiv_of_homotopy (additive_equiv H X Y n) begin intro f, induction f, reflexivity end

/- cohomology theory -/

structure cohomology_theory.{u} : Type.{u+1} :=
  (H : ℤ → pType.{u} → AbGroup.{u})
  (Hh : Π(n : ℤ) {X Y : Type*} (f : X →* Y), H n Y →g H n X)
  (Hh_id : Π(n : ℤ) {X : Type*} (x : H n X), Hh n (pid X) x = x)
  (Hh_compose : Π(n : ℤ) {X Y Z : Type*} (g : Y →* Z) (f : X →* Y) (z : H n Z),
    Hh n (g ∘* f) z = Hh n f (Hh n g z))
  (Hsusp : Π(n : ℤ) (X : Type*), H (succ n) (psusp X) ≃g H n X)
  (Hsusp_natural : Π(n : ℤ) {X Y : Type*} (f : X →* Y),
    Hsusp n X ∘ Hh (succ n) (psusp_functor f) ~ Hh n f ∘ Hsusp n Y)
  (Hexact : Π(n : ℤ) {X Y : Type*} (f : X →* Y), is_exact_g (Hh n (pcod f)) (Hh n f))
  (Hadditive : Π(n : ℤ) {I : Type.{u}} (X : I → Type*), has_choice 0 I →
    is_equiv (Group_pi_intro (λi, Hh n (pinl i)) : H n (⋁ X) → Πᵍ i, H n (X i)))

structure ordinary_theory.{u} extends cohomology_theory.{u} : Type.{u+1} :=
 (Hdimension : Π(n : ℤ), n ≠ 0 → is_contr (H n (plift pbool)))

definition cohomology_theory_spectrum [constructor] (Y : spectrum) : cohomology_theory :=
cohomology_theory.mk
  (λn A, H^n[A, Y])
  (λn A B f, cohomology_functor f Y n)
  (λn A x, cohomology_functor_pid A Y n x)
  (λn A B C g f x, cohomology_functor_pcompose g f Y n x)
  (λn A, cohomology_psusp A Y n)
  (λn A B f, cohomology_psusp_natural f Y n)
  (λn A B f, cohomology_exact f Y n)
  (λn I A H, additive H A Y n)

end cohomology
