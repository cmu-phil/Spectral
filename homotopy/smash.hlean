-- Authors: Floris van Doorn

import homotopy.smash ..pointed .pushout homotopy.red_susp

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function red_susp unit

  /- To prove: Σ(X × Y) ≃ ΣX ∨ ΣY ∨ Σ(X ∧ Y) (?) (notation means suspension, wedge, smash) -/

  /- To prove: Σ(X ∧ Y) ≃ X ★ Y (?) (notation means suspension, smash, join) -/

  /- To prove: A ∧ S¹ ≃ ΣA -/

  /- associativity is proven in smash_adjoint -/
variables {A A' B B' C C' D E F : Type*}

namespace smash

  definition elim_gluel' {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a a' : A) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluel' a a') = Pgl a ⬝ (Pgl a')⁻¹ :=
  !ap_con ⬝ whisker_left _ !ap_inv ⬝ !elim_gluel ◾ !elim_gluel⁻²

  definition elim_gluer' {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (b b' : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluer' b b') = Pgr b ⬝ (Pgr b')⁻¹ :=
  !ap_con ⬝ whisker_left _ !ap_inv ⬝ !elim_gluer ◾ !elim_gluer⁻²

  definition elim_gluel'_same {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a : A) :
    elim_gluel' Pgl Pgr a a =
      ap02 (smash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluel a)) ⬝ (con.right_inv (Pgl a))⁻¹ :=
  begin
    refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
    refine _ ⬝ whisker_right _ !con_idp⁻¹,
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
  end

  definition elim_gluer'_same {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (b : B) :
    elim_gluer' Pgl Pgr b b =
      ap02 (smash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluer b)) ⬝ (con.right_inv (Pgr b))⁻¹ :=
  begin
    refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
    refine _ ⬝ whisker_right _ !con_idp⁻¹,
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
  end

  definition elim'_gluel'_pt {P : Type} {Pmk : Πa b, P}
    (Pgl : Πa : A, Pmk a pt = Pmk pt pt) (Pgr : Πb : B, Pmk pt b = Pmk pt pt)
    (a : A) (ql : Pgl pt = idp) (qr : Pgr pt = idp) :
    ap (smash.elim' Pmk Pgl Pgr ql qr) (gluel' a pt) = Pgl a :=
  !elim_gluel' ⬝ whisker_left _ ql⁻²

  definition elim'_gluer'_pt {P : Type} {Pmk : Πa b, P}
    (Pgl : Πa : A, Pmk a pt = Pmk pt pt) (Pgr : Πb : B, Pmk pt b = Pmk pt pt)
    (b : B) (ql : Pgl pt = idp) (qr : Pgr pt = idp) :
    ap (smash.elim' Pmk Pgl Pgr ql qr) (gluer' b pt) = Pgr b :=
  !elim_gluer' ⬝ whisker_left _ qr⁻²

  protected definition rec_eq {A B : Type*} {C : Type} {f g : smash A B → C}
    (Pmk : Πa b, f (smash.mk a b) = g (smash.mk a b))
    (Pl : f auxl = g auxl) (Pr : f auxr = g auxr)
    (Pgl : Πa, square (Pmk a pt) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : Πb, square (Pmk pt b) Pr (ap f (gluer b)) (ap g (gluer b))) (x : smash' A B) : f x = g x :=
  begin
    induction x with a b a b,
    { exact Pmk a b },
    { exact Pl },
    { exact Pr },
    { apply eq_pathover, apply Pgl },
    { apply eq_pathover, apply Pgr }
  end

  definition rec_eq_gluel {A B : Type*} {C : Type} {f g : smash A B → C}
    {Pmk : Πa b, f (smash.mk a b) = g (smash.mk a b)}
    {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
    (Pgl : Πa, square (Pmk a pt) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : Πb, square (Pmk pt b) Pr (ap f (gluer b)) (ap g (gluer b))) (a : A) :
      natural_square (smash.rec_eq Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  begin
    refine ap square_of_pathover !rec_gluel ⬝ _,
    apply to_right_inv !eq_pathover_equiv_square
  end

  definition rec_eq_gluer {A B : Type*} {C : Type} {f g : smash A B → C}
    {Pmk : Πa b, f (smash.mk a b) = g (smash.mk a b)}
    {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
    (Pgl : Πa, square (Pmk a pt) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : Πb, square (Pmk pt b) Pr (ap f (gluer b)) (ap g (gluer b))) (b : B) :
      natural_square (smash.rec_eq Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  begin
    refine ap square_of_pathover !rec_gluer ⬝ _,
    apply to_right_inv !eq_pathover_equiv_square
  end

  /- the functorial action of the smash product -/
  definition smash_functor' [unfold 7] (f : A →* C) (g : B →* D) : A ∧ B → C ∧ D :=
  begin
    intro x, induction x,
    { exact smash.mk (f a) (g b) },
    { exact auxl },
    { exact auxr },
    { exact ap (smash.mk (f a)) (respect_pt g) ⬝ gluel (f a) },
    { exact ap (λa, smash.mk a (g b)) (respect_pt f) ⬝ gluer (g b) }
  end

  definition smash_functor [constructor] (f : A →* C) (g : B →* D) : A ∧ B →* C ∧ D :=
  begin
    fapply pmap.mk,
    { exact smash_functor' f g },
    { exact ap011 smash.mk (respect_pt f) (respect_pt g) },
  end

  infixr ` ∧→ `:65 := smash_functor

  definition functor_gluel (f : A →* C) (g : B →* D) (a : A) :
    ap (f ∧→ g) (gluel a) = ap (smash.mk (f a)) (respect_pt g) ⬝ gluel (f a) :=
  !elim_gluel

  definition functor_gluer (f : A →* C) (g : B →* D) (b : B) :
    ap (f ∧→ g) (gluer b) = ap (λc, smash.mk c (g b)) (respect_pt f) ⬝ gluer (g b) :=
  !elim_gluer

  definition functor_gluel2 {C D : Type} (f : A → C) (g : B → D) (a : A) :
    ap (pmap_of_map f pt ∧→ pmap_of_map g pt) (gluel a) = gluel (f a) :=
  begin
    refine !elim_gluel ⬝ !idp_con
  end

  definition functor_gluer2 {C D : Type} (f : A → C) (g : B → D) (b : B) :
    ap (pmap_of_map f pt ∧→ pmap_of_map g pt) (gluer b) = gluer (g b) :=
  begin
    refine !elim_gluer ⬝ !idp_con
  end

  definition functor_gluel' (f : A →* C) (g : B →* D) (a a' : A) :
    ap (f ∧→ g) (gluel' a a') = ap (smash.mk (f a)) (respect_pt g) ⬝
      gluel' (f a) (f a') ⬝ (ap (smash.mk (f a')) (respect_pt g))⁻¹ :=
  begin
    refine !elim_gluel' ⬝ _,
    refine whisker_left _ !con_inv ⬝ _,
    refine !con.assoc⁻¹ ⬝ _, apply whisker_right,
    apply con.assoc
  end

  definition functor_gluer' (f : A →* C) (g : B →* D) (b b' : B) :
    ap (f ∧→ g) (gluer' b b') = ap (λc, smash.mk c (g b)) (respect_pt f) ⬝
      gluer' (g b) (g b') ⬝ (ap (λc, smash.mk c (g b')) (respect_pt f))⁻¹ :=
  begin
    refine !elim_gluer' ⬝ _,
    refine whisker_left _ !con_inv ⬝ _,
    refine !con.assoc⁻¹ ⬝ _, apply whisker_right,
    apply con.assoc
  end

  /- the statements of the above rules becomes easier if one of the functions respects the basepoint
     by reflexivity -/
  -- definition functor_gluel'2 {D : Type} (f : A →* C) (g : B → D) (a a' : A) :
  --   ap (f ∧→ (pmap_of_map g pt)) (gluel' a a') = gluel' (f a) (f a') :=
  -- begin
  --   refine !ap_con ⬝ whisker_left _ !ap_inv ⬝ _,
  --   refine (!functor_gluel ⬝ !idp_con) ◾  (!functor_gluel ⬝ !idp_con)⁻²
  -- end

  -- definition functor_gluer'2 {C : Type} (f : A → C) (g : B →* D) (b b' : B) :
  --   ap (pmap_of_map f pt ∧→ g) (gluer' b b') = gluer' (g b) (g b') :=
  -- begin
  --   refine !ap_con ⬝ whisker_left _ !ap_inv ⬝ _,
  --   refine (!functor_gluer ⬝ !idp_con) ◾  (!functor_gluer ⬝ !idp_con)⁻²
  -- end

  definition functor_gluel'2 {C D : Type} (f : A → C) (g : B → D) (a a' : A) :
    ap (pmap_of_map f pt ∧→ pmap_of_map g pt) (gluel' a a') = gluel' (f a) (f a') :=
  !ap_con ⬝ whisker_left _ !ap_inv ⬝ !functor_gluel2 ◾ !functor_gluel2⁻²

  definition functor_gluer'2 {C D : Type} (f : A → C) (g : B → D) (b b' : B) :
    ap (pmap_of_map f pt ∧→ pmap_of_map g pt) (gluer' b b') = gluer' (g b) (g b') :=
  !ap_con ⬝ whisker_left _ !ap_inv ⬝ !functor_gluer2 ◾ !functor_gluer2⁻²

  lemma functor_gluel'2_same {C D : Type} (f : A → C) (g : B → D) (a : A) :
    functor_gluel'2 f (pmap_of_map g pt) a a =
    ap02 (pmap_of_map f pt ∧→ pmap_of_map g pt) (con.right_inv (gluel a)) ⬝
    (con.right_inv (gluel (f a)))⁻¹ :=
  begin
    refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
    refine _ ⬝ whisker_right _ !con_idp⁻¹,
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
  end

  lemma functor_gluer'2_same {C D : Type} (f : A → C) (g : B → D) (b : B) :
    functor_gluer'2 (pmap_of_map f pt) g b b =
    ap02 (pmap_of_map f pt ∧→ pmap_of_map g pt) (con.right_inv (gluer b)) ⬝
    (con.right_inv (gluer (g b)))⁻¹ :=
  begin
    refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
    refine _ ⬝ whisker_right _ !con_idp⁻¹,
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
  end

  definition smash_functor_pid [constructor] (A B : Type*) :
    pid A ∧→ pid B ~* pid (A ∧ B) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with a b a b,
      { reflexivity },
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square, exact !functor_gluel ⬝ !idp_con },
      { apply eq_pathover_id_right, apply hdeg_square, exact !functor_gluer ⬝ !idp_con }},
    { reflexivity }
  end

  /- the functorial action of the smash product respects pointed homotopies, and some computation
     rules for this pointed homotopy -/
  definition smash_functor_phomotopy {f f' : A →* C} {g g' : B →* D}
    (h₁ : f ~* f') (h₂ : g ~* g') : f ∧→ g ~* f' ∧→ g' :=
  begin
    induction h₁ using phomotopy_rec_on_idp,
    induction h₂ using phomotopy_rec_on_idp,
    reflexivity
  end

  /- a more explicit proof, if we ever need it -/
  -- definition smash_functor_homotopy [unfold 11] {f f' : A →* C} {g g' : B →* D}
  --   (h₁ : f ~* f') (h₂ : g ~* g') : f ∧→ g ~ f' ∧→ g' :=
  -- begin
  --   intro x, induction x with a b a b,
  --   { exact ap011 smash.mk (h₁ a) (h₂ b) },
  --   { reflexivity },
  --   { reflexivity },
  --   { apply eq_pathover,
  --     refine !functor_gluel ⬝ph _ ⬝hp !functor_gluel⁻¹,
  --     refine _ ⬝v square_of_eq_top (ap_mk_left (h₁ a)),
  --     exact ap011_ap_square_right smash.mk (h₁ a) (to_homotopy_pt h₂) },
  --   { apply eq_pathover,
  --     refine !functor_gluer ⬝ph _ ⬝hp !functor_gluer⁻¹,
  --     refine _ ⬝v square_of_eq_top (ap_mk_right (h₂ b)),
  --     exact ap011_ap_square_left smash.mk (h₂ b) (to_homotopy_pt h₁) },
  -- end

  -- definition smash_functor_phomotopy [constructor] {f f' : A →* C} {g g' : B →* D}
  --   (h₁ : f ~* f') (h₂ : g ~* g') : f ∧→ g ~* f' ∧→ g' :=
  -- begin
  --   apply phomotopy.mk (smash_functor_homotopy h₁ h₂),
  --   induction h₁ with h₁ h₁₀, induction h₂ with h₂ h₂₀,
  --   induction f with f f₀, induction g with g g₀,
  --   induction f' with f' f'₀, induction g' with g' g'₀,
  --   induction C with C c₀, induction D with D d₀, esimp at *,
  --   induction h₁₀, induction h₂₀, induction f'₀, induction g'₀,
  --   exact !ap_ap011⁻¹
  -- end

  definition smash_functor_phomotopy_refl (f : A →* C) (g : B →* D) :
    smash_functor_phomotopy (phomotopy.refl f) (phomotopy.refl g) = phomotopy.rfl :=
  !phomotopy_rec_on_idp_refl ⬝ !phomotopy_rec_on_idp_refl

  definition smash_functor_phomotopy_symm {f₁ f₂ : A →* C} {g₁ g₂ : B →* D}
    (h : f₁ ~* f₂) (k : g₁ ~* g₂) :
    smash_functor_phomotopy h⁻¹* k⁻¹* = (smash_functor_phomotopy h k)⁻¹* :=
  begin
    induction h using phomotopy_rec_on_idp, induction k using phomotopy_rec_on_idp,
    exact ap011 smash_functor_phomotopy !refl_symm !refl_symm ⬝ !smash_functor_phomotopy_refl ⬝
      !refl_symm⁻¹ ⬝ !smash_functor_phomotopy_refl⁻¹⁻²**
  end

  definition smash_functor_phomotopy_trans {f₁ f₂ f₃ : A →* C} {g₁ g₂ g₃ : B →* D}
    (h₁ : f₁ ~* f₂) (h₂ : f₂ ~* f₃) (k₁ : g₁ ~* g₂) (k₂ : g₂ ~* g₃) :
    smash_functor_phomotopy (h₁ ⬝* h₂) (k₁ ⬝* k₂) =
    smash_functor_phomotopy h₁ k₁ ⬝* smash_functor_phomotopy h₂ k₂ :=
  begin
    induction h₁ using phomotopy_rec_on_idp, induction h₂ using phomotopy_rec_on_idp,
    induction k₁ using phomotopy_rec_on_idp, induction k₂ using phomotopy_rec_on_idp,
    refine ap011 smash_functor_phomotopy !trans_refl !trans_refl ⬝ !trans_refl⁻¹ ⬝ idp ◾** _,
    exact !smash_functor_phomotopy_refl⁻¹
  end

  definition smash_functor_phomotopy_trans_right {f₁ f₂ : A →* C} {g₁ g₂ g₃ : B →* D}
    (h₁ : f₁ ~* f₂) (k₁ : g₁ ~* g₂) (k₂ : g₂ ~* g₃) :
    smash_functor_phomotopy h₁ (k₁ ⬝* k₂) =
    smash_functor_phomotopy h₁ k₁ ⬝* smash_functor_phomotopy phomotopy.rfl k₂ :=
  begin
    refine ap (λx, smash_functor_phomotopy x _) !trans_refl⁻¹ ⬝ !smash_functor_phomotopy_trans,
  end

  definition smash_functor_phomotopy_phsquare {f₁ f₂ f₃ f₄ : A →* C} {g₁ g₂ g₃ g₄ : B →* D}
    {h₁ : f₁ ~* f₂} {h₂ : f₃ ~* f₄} {h₃ : f₁ ~* f₃} {h₄ : f₂ ~* f₄}
    {k₁ : g₁ ~* g₂} {k₂ : g₃ ~* g₄} {k₃ : g₁ ~* g₃} {k₄ : g₂ ~* g₄}
    (p : phsquare h₁ h₂ h₃ h₄) (q : phsquare k₁ k₂ k₃ k₄) :
    phsquare (smash_functor_phomotopy h₁ k₁)
             (smash_functor_phomotopy h₂ k₂)
             (smash_functor_phomotopy h₃ k₃)
             (smash_functor_phomotopy h₄ k₄) :=
  !smash_functor_phomotopy_trans⁻¹ ⬝ ap011 smash_functor_phomotopy p q ⬝
  !smash_functor_phomotopy_trans

  definition smash_functor_eq_of_phomotopy (f : A →* C) {g g' : B →* D}
    (p : g ~* g') : ap (smash_functor f) (eq_of_phomotopy p) =
    eq_of_phomotopy (smash_functor_phomotopy phomotopy.rfl p) :=
  begin
    induction p using phomotopy_rec_on_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
    refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
    apply ap eq_of_phomotopy,
    exact !smash_functor_phomotopy_refl⁻¹
  end

  /- the functorial action preserves compositions, the interchange law -/
  definition smash_functor_pcompose_homotopy [unfold 11] {C D E F : Type}
    (f' : C → E) (f : A → C) (g' : D → F) (g : B → D) :
    (pmap_of_map f' (f pt) ∘* pmap_of_map f pt) ∧→ (pmap_of_map g' (g pt) ∘* pmap_of_map g pt) ~
    (pmap_of_map f' (f pt) ∧→ pmap_of_map g' (g pt)) ∘* (pmap_of_map f pt ∧→ pmap_of_map g pt) :=
  begin
    intro x, induction x with a b a b,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, refine !functor_gluel2 ⬝ph _, esimp,
      refine _ ⬝hp (ap_compose (_ ∧→  _) _ _)⁻¹,
      refine _ ⬝hp ap02 _ !functor_gluel2⁻¹, refine _ ⬝hp !functor_gluel2⁻¹, exact hrfl },
    { apply eq_pathover, refine !functor_gluer2 ⬝ph _, esimp,
      refine _ ⬝hp (ap_compose (_ ∧→ _) _ _)⁻¹,
      refine _ ⬝hp ap02 _ !functor_gluer2⁻¹, refine _ ⬝hp !functor_gluer2⁻¹, exact hrfl }
  end

  definition smash_functor_pcompose (f' : C →* E) (f : A →* C) (g' : D →* F) (g : B →* D) :
    (f' ∘* f) ∧→ (g' ∘* g) ~* f' ∧→ g' ∘* f ∧→ g :=
  begin
    induction C with C, induction D with D, induction E with E, induction F with F,
    induction f with f f₀, induction f' with f' f'₀, induction g with g g₀,
    induction g' with g' g'₀, esimp at *,
    induction f₀, induction f'₀, induction g₀, induction g'₀,
    fapply phomotopy.mk,
    { rexact smash_functor_pcompose_homotopy f' f g' g },
    { reflexivity }
  end

  definition smash_functor_split (f : A →* C) (g : B →* D) :
    f ∧→ g ~* (pid C) ∧→ g ∘* f ∧→ (pid B)  :=
  smash_functor_phomotopy !pid_pcompose⁻¹* !pcompose_pid⁻¹* ⬝* !smash_functor_pcompose

  /- An alternative proof which doesn't start by applying inductions, so which is more explicit -/
  -- definition smash_functor_pcompose_homotopy [unfold 11] (f' : C →* E) (f : A →* C) (g' : D →* F)
  --   (g : B →* D) : (f' ∘* f) ∧→ (g' ∘* g) ~ (f' ∧→ g') ∘* (f ∧→ g) :=
  -- begin
  --   intro x, induction x with a b a b,
  --   { reflexivity },
  --   { reflexivity },
  --   { reflexivity },
  --   { apply eq_pathover, exact abstract begin apply hdeg_square,
  --     refine !functor_gluel ⬝ _ ⬝ (ap_compose (f' ∧→ g') _ _)⁻¹,
  --     refine whisker_right _ !ap_con ⬝ !con.assoc ⬝ _ ⬝ ap02 _ !functor_gluel⁻¹,
  --     refine (!ap_compose'⁻¹ ⬝ !ap_compose') ◾ proof !functor_gluel⁻¹ qed ⬝ !ap_con⁻¹ end end },
  --   { apply eq_pathover, exact abstract begin apply hdeg_square,
  --     refine !functor_gluer ⬝ _ ⬝ (ap_compose (f' ∧→ g') _ _)⁻¹,
  --     refine whisker_right _ !ap_con ⬝ !con.assoc ⬝ _ ⬝ ap02 _ !functor_gluer⁻¹,
  --     refine (!ap_compose'⁻¹ ⬝ !ap_compose') ◾ proof !functor_gluer⁻¹ qed ⬝ !ap_con⁻¹ end end }
  -- end

  -- definition smash_functor_pcompose [constructor] (f' : C →* E) (f : A →* C) (g' : D →* F) (g : B →* D) :
  --   (f' ∘* f) ∧→ (g' ∘* g) ~* f' ∧→ g' ∘* f ∧→ g :=
  -- begin
  --   fapply phomotopy.mk,
  --   { exact smash_functor_pcompose_homotopy f' f g' g },
  --   { exact abstract begin induction C, induction D, induction E, induction F,
  --     induction f with f f₀, induction f' with f' f'₀, induction g with g g₀,
  --     induction g' with g' g'₀, esimp at *,
  --     induction f₀, induction f'₀, induction g₀, induction g'₀, reflexivity end end }
  -- end


  definition smash_functor_pid_pcompose [constructor] (A : Type*) (g' : C →* D) (g : B →* C)
    : pid A ∧→ (g' ∘* g) ~* pid A ∧→ g' ∘* pid A ∧→ g :=
  smash_functor_phomotopy !pid_pcompose⁻¹* phomotopy.rfl ⬝* !smash_functor_pcompose

  definition smash_functor_pcompose_pid [constructor] (B : Type*) (f' : C →* D) (f : A →* C)
    : (f' ∘* f) ∧→ pid B ~* f' ∧→ (pid B) ∘* f ∧→ (pid B) :=
  smash_functor_phomotopy phomotopy.rfl !pid_pcompose⁻¹* ⬝* !smash_functor_pcompose

  /- composing commutes with applying homotopies -/
  definition smash_functor_pcompose_phomotopy {f₂ f₂' : C →* E} {f f' : A →* C} {g₂ g₂' : D →* F}
    {g g' : B →* D} (h₂ : f₂ ~* f₂') (h₁ : f ~* f') (k₂ : g₂ ~* g₂') (k₁ : g ~* g') :
    phsquare (smash_functor_pcompose f₂ f g₂ g)
             (smash_functor_pcompose f₂' f' g₂' g')
             (smash_functor_phomotopy (h₂ ◾* h₁) (k₂ ◾* k₁))
             (smash_functor_phomotopy h₂ k₂ ◾* smash_functor_phomotopy h₁ k₁) :=
  begin
    induction h₁ using phomotopy_rec_on_idp, induction h₂ using phomotopy_rec_on_idp,
    induction k₁ using phomotopy_rec_on_idp, induction k₂ using phomotopy_rec_on_idp,
    refine (ap011 smash_functor_phomotopy !pcompose2_refl !pcompose2_refl ⬝
      !smash_functor_phomotopy_refl) ⬝ph** phvrfl ⬝hp**
      (ap011 pcompose2 !smash_functor_phomotopy_refl !smash_functor_phomotopy_refl ⬝
      !pcompose2_refl)⁻¹,
  end

  definition smash_functor_pid_pcompose_phomotopy_right (g₂ : D →* E) {g g' : B →* D}
    (k : g ~* g') :
    phsquare (smash_functor_pid_pcompose A g₂ g)
             (smash_functor_pid_pcompose A g₂ g')
             (smash_functor_phomotopy phomotopy.rfl (pwhisker_left g₂ k))
             (pwhisker_left (pid A ∧→ g₂) (smash_functor_phomotopy phomotopy.rfl k)) :=
  begin
    refine smash_functor_phomotopy_phsquare _ _ ⬝h** !smash_functor_pcompose_phomotopy ⬝hp**
      ((ap (pwhisker_right _) !smash_functor_phomotopy_refl) ◾** idp ⬝ !pcompose2_refl_left),
      exact (!pcompose2_refl ⬝ph** phvrfl)⁻¹ʰ**,
      exact (phhrfl ⬝hp** !pcompose2_refl_left⁻¹)
  end

  section
  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type*} {B₀₀ B₂₀ B₀₂ B₂₂ : Type*}
            {f₁₀ : A₀₀ →* A₂₀} {f₀₁ : A₀₀ →* A₀₂} {f₂₁ : A₂₀ →* A₂₂} {f₁₂ : A₀₂ →* A₂₂}
            {g₁₀ : B₀₀ →* B₂₀} {g₀₁ : B₀₀ →* B₀₂} {g₂₁ : B₂₀ →* B₂₂} {g₁₂ : B₀₂ →* B₂₂}

  /- applying the functorial action of smash to squares of pointed maps -/
  definition smash_functor_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare g₁₀ g₁₂ g₀₁ g₂₁) :
    psquare (f₁₀ ∧→ g₁₀) (f₁₂ ∧→ g₁₂) (f₀₁ ∧→ g₀₁) (f₂₁ ∧→ g₂₁) :=
  !smash_functor_pcompose⁻¹* ⬝* smash_functor_phomotopy p q ⬝* !smash_functor_pcompose
  end

  /- f ∧ g is constant if g is constant -/
  definition smash_functor_pconst_right_homotopy [unfold 6] {C : Type} (f : A → C) (x : A ∧ B) :
    (pmap_of_map f pt ∧→ pconst B D) x = pt :=
  begin
    induction x with a b a b,
    { exact gluel' (f a) pt },
    { exact (gluel pt)⁻¹ },
    { exact (gluer pt)⁻¹ },
    { apply eq_pathover, note x := functor_gluel2 f (λx : B, Point D) a, esimp [pconst] at *,
      refine x ⬝ph _, refine _ ⬝hp !ap_constant⁻¹, apply square_of_eq, reflexivity },
    { apply eq_pathover, note x := functor_gluer2 f (λx : B, Point D) b, esimp [pconst] at *,
      refine x ⬝ph _, refine _ ⬝hp !ap_constant⁻¹, apply square_of_eq,
      rexact con.right_inv (gluel (f pt)) ⬝ (con.right_inv (gluer pt))⁻¹ }
  end

  definition smash_functor_pconst_right (f : A →* C) :
    f ∧→ (pconst B D) ~* pconst (A ∧ B) (C ∧ D) :=
  begin
    induction C with C, induction f with f f₀, esimp at *, induction f₀,
    fapply phomotopy.mk,
    { exact smash_functor_pconst_right_homotopy f },
    { rexact con.right_inv (gluel (f pt)) }
  end

  definition smash_functor_pconst_right_phomotopy {f f' : A →* C} (p : f ~* f') :
    smash_functor_phomotopy p (phomotopy.refl (pconst B D)) ⬝* smash_functor_pconst_right f' =
    smash_functor_pconst_right f :=
  begin
    induction p using phomotopy_rec_on_idp,
    exact !smash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans
  end

  /- This makes smash_functor into a pointed map (B →* B') →* (A ∧ B →* A ∧ B') -/

  definition smash_functor_right [constructor] (A B C : Type*) :
    ppmap B C →* ppmap (A ∧ B) (A ∧ C) :=
  pmap.mk (smash_functor (pid A)) (eq_of_phomotopy (smash_functor_pconst_right (pid A)))

  /- We want to show that smash_functor_right is natural in A, B and C.

     For this we need two coherence rules. Given the function h := (f' ∘ f) ∧→ (g' ∘ g) and suppose
     that either g' or g is constant. There are two ways to show that h is constant: either by using
     exchange, or directly. We need to show that these two proofs result in the same pointed
     homotopy. First we do the case where g is constant -/

  private definition my_squarel {A : Type} {a₁ a₂ a₃ : A} (p₁ : a₁ = a₃) (p₂ : a₂ = a₃) :
    square (p₁ ⬝ p₂⁻¹) p₂⁻¹ p₁ idp :=
  proof square_of_eq idp qed

  private definition my_squarer {A : Type} {a₁ a₂ a₃ : A} (p₁ : a₁ = a₃) (p₂ : a₁ = a₂) :
    square (p₁ ⬝ p₁⁻¹) p₂⁻¹ p₂ idp :=
  proof square_of_eq (con.right_inv p₁ ⬝ (con.right_inv p₂)⁻¹) qed

  private definition my_cube_fillerl {A B C : Type} {g : B → C} {f : A → B} {a₁ a₂ : A} {b₀ : B}
    {p : f ~ λa, b₀} {q : Πa, g (f a) = g b₀} (r : (λa, ap g (p a)) ~ q) :
    cube (hrfl ⬝hp (r a₁)⁻¹) hrfl
         (my_squarel (q a₁) (q a₂)) (aps g (my_squarel (p a₁) (p a₂)))
         (hrfl ⬝hp (!ap_con ⬝ whisker_left _ !ap_inv ⬝ (r a₁) ◾ (r a₂)⁻²)⁻¹)
           (hrfl ⬝hp (r a₂)⁻²⁻¹ ⬝hp !ap_inv⁻¹) :=
  begin
    induction r using homotopy.rec_on_idp, induction p using homotopy.rec_on_idp_left, exact idc
  end

  private definition my_cube_fillerr {B C : Type} {g : B → C} {b₀ bl br : B}
    {pl : b₀ = bl} {pr : b₀ = br} {ql : g b₀ = g bl} {qr : g b₀ = g br}
    (sl : ap g pl = ql) (sr : ap g pr = qr) :
    cube (hrfl ⬝hp sr⁻¹) hrfl
         (my_squarer ql qr) (aps g (my_squarer pl pr))
         (hrfl ⬝hp (!ap_con ⬝ whisker_left _ !ap_inv ⬝ sl ◾ sl⁻²)⁻¹)
         (hrfl ⬝hp sr⁻²⁻¹ ⬝hp !ap_inv⁻¹) :=
  begin
    induction sr, induction sl, induction pr, induction pl, exact idc
  end

  definition smash_functor_pcompose_pconst_homotopy {A B C D E F : Type}
    (a₀ : A) (b₀ : B) (d₀ : D) (f' : C → E) (f : A → C) (g : D → F)
    (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
    square (smash_functor_pcompose_homotopy f' f g (λ a, d₀) x)
    idp
    (smash_functor_pconst_right_homotopy (λ a, f' (f a)) x)
    (ap (smash_functor' (pmap.mk f' (refl (f' (f a₀)))) (pmap.mk g (refl (g d₀))))
      (smash_functor_pconst_right_homotopy f x)) :=
  begin
    induction x with a b a b,
    { refine _ ⬝hp (functor_gluel'2 f' g (f a) (f a₀))⁻¹, exact hrfl },
    { refine _ ⬝hp !ap_inv⁻¹, refine _ ⬝hp !functor_gluel2⁻²⁻¹, exact hrfl },
    { refine _ ⬝hp !ap_inv⁻¹, refine _ ⬝hp !functor_gluer2⁻²⁻¹, exact hrfl },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluel ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
      refine !rec_eq_gluel ⬝p2 _ ⬝2p !natural_square_ap_fn⁻¹,
      apply whisker001, apply whisker021,
      apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (ap (aps _) !rec_eq_gluel ⬝ !aps_eq_hconcat)⁻¹,
      apply whisker021, refine _ ⬝2p !aps_hconcat_eq⁻¹, apply move221,
      refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
      apply my_cube_fillerl end end },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluer ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
      refine !rec_eq_gluer ⬝p2 _ ⬝2p !natural_square_ap_fn⁻¹,
      apply whisker001, apply whisker021,
      apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (ap (aps _) !rec_eq_gluer ⬝ !aps_eq_hconcat)⁻¹,
      apply whisker021, refine _ ⬝2p !aps_hconcat_eq⁻¹, apply move221,
      refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
      apply my_cube_fillerr end end }
  end

  definition smash_functor_pcompose_pconst (f' : C →* E) (f : A →* C) (g : D →* F) :
    phsquare (smash_functor_pcompose f' f g (pconst B D))
             (smash_functor_pconst_right (f' ∘* f))
             (smash_functor_phomotopy phomotopy.rfl (pcompose_pconst g))
             (pwhisker_left (f' ∧→ g) (smash_functor_pconst_right f) ⬝*
               pcompose_pconst (f' ∧→ g)) :=
  begin
    induction A with A a₀, induction B with B b₀,
    induction E with E e₀, induction C with C c₀, induction F with F x₀, induction D with D d₀,
    induction f' with f' f'₀, induction f with f f₀, induction g with g g₀,
    esimp at *, induction f'₀, induction f₀, induction g₀,
    refine !smash_functor_phomotopy_refl ⬝ph** _, refine _ ⬝ !refl_trans⁻¹,
    fapply phomotopy_eq,
    { intro x, refine eq_of_square _ ⬝ !con_idp,
      exact smash_functor_pcompose_pconst_homotopy a₀ b₀ d₀ f' f g x, },
    { refine _ ⬝ !idp_con⁻¹,
      refine whisker_right _ (!whisker_right_idp ⬝ !eq_of_square_hrfl_hconcat_eq) ⬝ _,
      refine !con.assoc ⬝ _, apply con_eq_of_eq_inv_con, esimp,
      refine whisker_right _ !functor_gluel'2_same ⬝ _,
      refine !inv_con_cancel_right ⬝ _,
      refine _ ⬝ idp ◾ ap (whisker_left _) (!idp_con ⬝ !idp_con ⬝ !whisker_right_idp ⬝ !idp_con)⁻¹,
      symmetry, apply whisker_left_idp }
  end

  /- a version where the left maps are identities -/
  definition smash_functor_pid_pcompose_pconst (g : D →* F) :
    phsquare (smash_functor_pid_pcompose A g (pconst B D))
             (smash_functor_pconst_right (pid A))
             (smash_functor_phomotopy phomotopy.rfl (pcompose_pconst g))
             (pwhisker_left (pid A ∧→ g) (smash_functor_pconst_right (pid A)) ⬝*
               pcompose_pconst (pid A ∧→ g)) :=
  (!smash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans) ⬝pv**
  smash_functor_pcompose_pconst (pid A) (pid A) g

  /- a small rewrite of the previous -/
  definition smash_functor_pid_pcompose_pconst' (g : D →* F) :
    pwhisker_left (pid A ∧→ g) (smash_functor_pconst_right (pid A)) ⬝*
    pcompose_pconst (pid A ∧→ g) =
    (smash_functor_pid_pcompose A g (pconst B D))⁻¹* ⬝*
    (smash_functor_phomotopy phomotopy.rfl (pcompose_pconst g) ⬝*
    smash_functor_pconst_right (pid A)) :=
  begin
    apply eq_symm_trans_of_trans_eq,
    exact smash_functor_pid_pcompose_pconst g
  end

  /- if g' is constant -/
  definition smash_functor_pconst_pcompose_homotopy [unfold 13] {A B C D E F : Type}
    (a₀ : A) (b₀ : B) (x₀ : F) (f' : C → E) (f : A → C) (g : B → D)
    (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
    square (smash_functor_pcompose_homotopy f' f (λ a, x₀) g x)
    idp
    (smash_functor_pconst_right_homotopy (λ a, f' (f a)) x)
    (smash_functor_pconst_right_homotopy f'
      (smash_functor (pmap_of_map f a₀) (pmap_of_map g b₀) x)) :=
  begin
    induction x with a b a b,
    { exact hrfl },
    { exact hrfl },
    { exact hrfl },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluel ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
      refine !rec_eq_gluel ⬝p2 _ ⬝2p
        (natural_square_compose (smash_functor_pconst_right_homotopy f') _ _)⁻¹ᵖ,
      apply whisker001, apply whisker021,
      apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (natural_square_eq2 _ !functor_gluel2)⁻¹ᵖ,
      apply whisker021,
      refine _ ⬝1p ap hdeg_square (eq_of_square (!ap_constant_compose⁻¹ʰ) ⬝ !idp_con)⁻¹,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine _ ⬝2p !rec_eq_gluel⁻¹, apply whisker021,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
      exact rfl2 end end },
    { exact abstract begin apply square_pathover,
      refine !rec_eq_gluer ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
      refine !rec_eq_gluer ⬝p2 _ ⬝2p
        (natural_square_compose (smash_functor_pconst_right_homotopy f') _ _)⁻¹ᵖ,
      apply whisker001, apply whisker021,
      apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (natural_square_eq2 _ !functor_gluer2)⁻¹ᵖ,
      apply whisker021,
      refine _ ⬝1p ap hdeg_square (eq_of_square (!ap_constant_compose⁻¹ʰ) ⬝ !idp_con)⁻¹,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine _ ⬝2p !rec_eq_gluer⁻¹, apply whisker021,
      apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
      refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
      exact rfl2 end end },
  end

  definition smash_functor_pconst_pcompose (f' : C →* E) (f : A →* C) (g : B →* D) :
    phsquare (smash_functor_pcompose f' f (pconst D F) g)
             (smash_functor_pconst_right (f' ∘* f))
             (smash_functor_phomotopy phomotopy.rfl (pconst_pcompose g))
             (pwhisker_right (f ∧→ g) (smash_functor_pconst_right f') ⬝*
               pconst_pcompose (f ∧→ g)) :=
  begin
    induction A with A a₀, induction B with B b₀,
    induction E with E e₀, induction C with C c₀, induction F with F x₀, induction D with D d₀,
    induction f' with f' f'₀, induction f with f f₀, induction g with g g₀,
    esimp at *, induction f'₀, induction f₀, induction g₀,
    refine !smash_functor_phomotopy_refl ⬝ph** _, refine _ ⬝ !refl_trans⁻¹,
    fapply phomotopy_eq,
    { intro x, refine eq_of_square (smash_functor_pconst_pcompose_homotopy a₀ b₀ x₀ f' f g x) },
    { refine whisker_right _ (!whisker_right_idp ⬝ !eq_of_square_hrfl) ⬝ _,
      have H : Π{A : Type} {a a' : A} (p : a = a'),
               idp_con (p ⬝ p⁻¹) ⬝ con.right_inv p = idp ⬝
               whisker_left idp (idp ⬝ (idp ⬝ proof whisker_right idp (idp_con (p ⬝ p⁻¹ᵖ))⁻¹ᵖ qed ⬝
                 whisker_left idp (con.right_inv p))), by intros; induction p; reflexivity,
      rexact H (gluel (f' (f a₀))) }
  end

  /- a version where the left maps are identities -/
  definition smash_functor_pid_pconst_pcompose (g : B →* D) :
    phsquare (smash_functor_pid_pcompose A (pconst D F) g)
             (smash_functor_pconst_right (pid A))
             (smash_functor_phomotopy phomotopy.rfl (pconst_pcompose g))
             (pwhisker_right (pid A ∧→ g) (smash_functor_pconst_right (pid A)) ⬝*
               pconst_pcompose (pid A ∧→ g)) :=
  (!smash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans) ⬝pv**
  smash_functor_pconst_pcompose (pid A) (pid A) g

  /- these lemmas are use to show that smash_functor_right is natural in all arguments -/
  definition smash_functor_right_natural_right (f : C →* C') :
    psquare (smash_functor_right A B C) (smash_functor_right A B C')
            (ppcompose_left f) (ppcompose_left (pid A ∧→ f)) :=
  begin
    refine _⁻¹*,
    fapply phomotopy_mk_ppmap,
    { exact smash_functor_pid_pcompose A f },
    { refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !smash_functor_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply smash_functor_pid_pcompose_pconst }
  end

  definition smash_functor_right_natural_middle (f : B' →* B) :
    psquare (smash_functor_right A B C) (smash_functor_right A B' C)
            (ppcompose_right f) (ppcompose_right (pid A ∧→ f)) :=
  begin
    refine _⁻¹*,
    fapply phomotopy_mk_ppmap,
    { intro g, exact smash_functor_pid_pcompose A g f },
    { refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !smash_functor_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply smash_functor_pid_pconst_pcompose }
  end

  definition smash_functor_right_natural_left (f : A →* A') :
    psquare (smash_functor_right A B C) (ppcompose_right (f ∧→ (pid B)))
            (smash_functor_right A' B C) (ppcompose_left (f ∧→ (pid C))) :=
  begin
    refine _⁻¹*,
    fapply phomotopy_mk_ppmap,
    { intro g, exact smash_functor_psquare proof phomotopy.rfl qed proof phomotopy.rfl qed },
    { esimp,
      refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply eq_of_phsquare,
      refine (phmove_bot_of_left _ !smash_functor_pconst_pcompose⁻¹ʰ**) ⬝h**
        (!smash_functor_phomotopy_refl ⬝pv** !phhrfl) ⬝h** !smash_functor_pcompose_pconst ⬝vp** _,
      refine !trans_assoc ⬝ !trans_assoc ⬝ idp ◾** _ ⬝ !trans_refl,
      refine idp ◾** !refl_trans ⬝ !trans_left_inv }
  end

  /- f ∧ g is a pointed equivalence if f and g are -/
  definition smash_functor_using_pushout [unfold 7] (f : A →* C) (g : B →* D) : A ∧ B → C ∧ D :=
  begin
    fapply pushout.functor (sum_functor f g) (prod_functor f g) id,
    { intro v, induction v with a b,
      exact prod_eq idp (respect_pt g),
      exact prod_eq (respect_pt f) idp },
    { intro v, induction v with a b: reflexivity }
  end

  definition smash_functor_homotopy_pushout_functor (f : A →* C) (g : B →* D) :
    f ∧→ g ~ smash_functor_using_pushout f g :=
  begin
    intro x, induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, refine !elim_gluel ⬝ph _ ⬝hp !pushout.elim_glue⁻¹,
      apply hdeg_square, esimp, apply whisker_right, exact !ap_ap011⁻¹ },
    { apply eq_pathover, refine !elim_gluer ⬝ph _ ⬝hp !pushout.elim_glue⁻¹,
      apply hdeg_square, esimp, apply whisker_right, exact !ap_ap011⁻¹ }
  end

  local attribute is_equiv_sum_functor [instance]
  definition smash_pequiv [constructor] (f : A ≃* C) (g : B ≃* D) : A ∧ B ≃* C ∧ D :=
  begin
    fapply pequiv_of_pmap (f ∧→ g),
    refine @homotopy_closed _ _ _ _ _ (smash_functor_homotopy_pushout_functor f g)⁻¹ʰᵗʸ,
    apply pushout.is_equiv_functor
  end

  definition smash_pequiv_left [constructor] (B : Type*) (f : A ≃* C) : A ∧ B ≃* C ∧ B :=
  smash_pequiv f pequiv.rfl

  definition smash_pequiv_right [constructor] (A : Type*) (g : B ≃* D) : A ∧ B ≃* A ∧ D :=
  smash_pequiv pequiv.rfl g

  /- A ∧ B ≃* pcofiber (pprod_of_pwedge A B) -/

  definition prod_of_wedge [unfold 3] (v : pwedge A B) : A × B :=
  begin
    induction v with a b ,
    { exact (a, pt) },
    { exact (pt, b) },
    { reflexivity }
  end

  definition wedge_of_sum [unfold 3] (v : A + B) : pwedge A B :=
  begin
    induction v with a b,
    { exact pushout.inl a },
    { exact pushout.inr b }
  end

  definition prod_of_wedge_of_sum [unfold 3] (v : A + B) : prod_of_wedge (wedge_of_sum v) = prod_of_sum v :=
  begin
    induction v with a b,
    { reflexivity },
    { reflexivity }
  end

end smash open smash

namespace pushout

  definition eq_inl_pushout_wedge_of_sum [unfold 3] (v : pwedge A B) :
    inl pt = inl v :> pushout wedge_of_sum bool_of_sum :=
  begin
    induction v with a b,
    { exact glue (sum.inl pt) ⬝ (glue (sum.inl a))⁻¹, },
    { exact ap inl (glue ⋆) ⬝ glue (sum.inr pt) ⬝ (glue (sum.inr b))⁻¹, },
    { apply eq_pathover_constant_left,
      refine !con.right_inv ⬝pv _ ⬝vp !con_inv_cancel_right⁻¹, exact square_of_eq idp }
  end

  variables (A B)
  definition eq_inr_pushout_wedge_of_sum [unfold 3] (b : bool) :
    inl pt = inr b :> pushout (@wedge_of_sum A B) bool_of_sum :=
  begin
    induction b,
    { exact glue (sum.inl pt) },
    { exact ap inl (glue ⋆) ⬝ glue (sum.inr pt) }
  end

  definition is_contr_pushout_wedge_of_sum : is_contr (pushout (@wedge_of_sum A B) bool_of_sum) :=
  begin
    apply is_contr.mk (pushout.inl pt),
    intro x, induction x with v b w,
    { apply eq_inl_pushout_wedge_of_sum },
    { apply eq_inr_pushout_wedge_of_sum },
    { apply eq_pathover_constant_left_id_right,
      induction w with a b,
      { apply whisker_rt, exact vrfl },
      { apply whisker_rt, exact vrfl }}
  end

  definition bool_of_sum_of_bool {A B : Type*} (b : bool) : bool_of_sum (sum_of_bool A B b) = b :=
  by induction b: reflexivity

  /- a different proof, using pushout lemmas, and the fact that the wedge is the pushout of
     A + B <-- 2 --> 1 -/
  definition pushout_wedge_of_sum_equiv_unit : pushout (@wedge_of_sum A B) bool_of_sum ≃ unit :=
  begin
    refine pushout_hcompose_equiv (sum_of_bool A B) (wedge_equiv_pushout_sum A B ⬝e !pushout.symm)
             _ _ ⬝e _,
      exact erfl,
      intro x, induction x,
      reflexivity, reflexivity,
      exact bool_of_sum_of_bool,
    apply pushout_of_equiv_right
  end

end pushout open pushout

namespace smash

  variables (A B)

  definition smash_equiv_cofiber : smash A B ≃ cofiber (@prod_of_wedge A B) :=
  begin
    unfold [smash, cofiber, smash'], symmetry,
    fapply pushout_vcompose_equiv wedge_of_sum,
    { symmetry, apply equiv_unit_of_is_contr, apply is_contr_pushout_wedge_of_sum },
    { intro x, reflexivity },
    { apply prod_of_wedge_of_sum }
  end

  definition smash_punit_pequiv [constructor] : smash A punit ≃* punit :=
  begin
    apply pequiv_punit_of_is_contr,
    apply is_contr.mk (smash.mk pt ⋆), intro x,
    induction x,
    { induction b, exact gluel' pt a },
    { exact gluel pt },
    { exact gluer pt },
    { apply eq_pathover_constant_left_id_right, apply square_of_eq_top,
      exact whisker_right _ !idp_con⁻¹ },
    { apply eq_pathover_constant_left_id_right, induction b,
      refine !con.right_inv ⬝pv _, exact square_of_eq idp },
  end

  definition pprod_of_pwedge [constructor] : pwedge A B →* A ×* B :=
  begin
    fconstructor,
    { exact prod_of_wedge },
    { reflexivity }
  end

  definition smash_pequiv_pcofiber [constructor] : smash A B ≃* pcofiber (pprod_of_pwedge A B) :=
  begin
    apply pequiv_of_equiv (smash_equiv_cofiber A B),
    exact cofiber.glue pt
  end

  variables {A B}

  /- commutativity -/

  definition smash_flip' [unfold 3] (x : smash A B) : smash B A :=
  begin
    induction x,
    { exact smash.mk b a },
    { exact auxr },
    { exact auxl },
    { exact gluer a },
    { exact gluel b }
  end

  definition smash_flip_smash_flip' [unfold 3] (x : smash A B) : smash_flip' (smash_flip' x) = x :=
  begin
    induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose' smash_flip' _ _ ⬝ ap02 _ !elim_gluel ⬝ !elim_gluer ⬝ph _,
      apply hrfl },
    { apply eq_pathover_id_right,
      refine ap_compose' smash_flip' _ _ ⬝ ap02 _ !elim_gluer ⬝ !elim_gluel ⬝ph _,
      apply hrfl }
  end

  variables (A B)

  definition smash_flip [constructor] : smash A B →* smash B A :=
  pmap.mk smash_flip' idp

  definition smash_flip_smash_flip [constructor] :
    smash_flip B A ∘* smash_flip A B ~* pid (A ∧ B) :=
  phomotopy.mk smash_flip_smash_flip' idp

  definition smash_comm [constructor] : smash A B ≃* smash B A :=
  begin
    apply pequiv.MK2, do 2 apply smash_flip_smash_flip
  end

  variables {A B}
  definition smash_flip_smash_functor' [unfold 7] (f : A →* C) (g : B →* D) : hsquare
    smash_flip' smash_flip' (smash_functor' f g) (smash_functor' g f) :=
  begin
    intro x, induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover,
      refine ap_compose' (smash_functor' _ _)  _ _ ⬝ ap02 _ !elim_gluel ⬝ !functor_gluer ⬝ph _
        ⬝hp (ap_compose' smash_flip' _ _ ⬝ ap02 _ !functor_gluel)⁻¹ᵖ,
      refine _ ⬝hp (!ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_gluel)⁻¹, exact hrfl },
    { apply eq_pathover,
      refine ap_compose' (smash_functor' _ _)  _ _ ⬝ ap02 _ !elim_gluer ⬝ !functor_gluel ⬝ph _
        ⬝hp (ap_compose' smash_flip' _ _ ⬝ ap02 _ !functor_gluer)⁻¹ᵖ,
      refine _ ⬝hp (!ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_gluer)⁻¹, exact hrfl },
  end

  definition smash_flip_smash_functor (f : A →* C) (g : B →* D) : psquare
    (smash_flip A B) (smash_flip C D) (f ∧→ g) (g ∧→ f) :=
  begin
    apply phomotopy.mk (smash_flip_smash_functor' f g), refine !idp_con ⬝ _ ⬝ !idp_con⁻¹,
    refine !ap_ap011 ⬝ _, apply ap011_flip,
  end

end smash
