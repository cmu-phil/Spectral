-- Authors: Floris van Doorn

/-

The "dependent" smash product.

Given A : Type* and B : A → Type* it is the cofiber of
A ∨ B pt → Σ(a : A), B a
However, we define it (equivalently) as the pushout of 2 ← A + B pt → Σ(a : A), B a.
-/

import .smash_adjoint ..pointed_binary

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber sigma.ops wedge sigma function prod.ops

namespace dsmash

  variables {A : Type*} {B : A → Type*}

  definition sigma_of_sum [unfold 3] (u : A + B pt) : Σa, B a :=
  by induction u with a b; exact ⟨a, pt⟩; exact ⟨pt, b⟩

  definition dsmash' (B : A → Type*) : Type := pushout.pushout (@sigma_of_sum A B) (@smash.bool_of_sum A (B pt))
  protected definition mk' (a : A) (b : B a) : dsmash' B := pushout.inl ⟨a, b⟩

  definition dsmash [constructor] (B : A → Type*) : Type* :=
  pointed.MK (dsmash' B) (dsmash.mk' pt pt)

  notation `⋀` := dsmash

  protected definition mk (a : A) (b : B a) : ⋀ B := pushout.inl ⟨a, b⟩
  definition auxl : ⋀ B := pushout.inr ff
  definition auxr : ⋀ B := pushout.inr tt
  definition gluel (a : A) : dsmash.mk a pt = auxl :> ⋀ B := pushout.glue (sum.inl a)
  definition gluer (b : B pt) : dsmash.mk pt b = auxr :> ⋀ B := pushout.glue (sum.inr b)

  definition gluel' (a a' : A) : dsmash.mk a pt = dsmash.mk a' pt :> ⋀ B :=
  gluel a ⬝ (gluel a')⁻¹
  definition gluer' (b b' : B pt) : dsmash.mk pt b = dsmash.mk pt b' :> ⋀ B :=
  gluer b ⬝ (gluer b')⁻¹
  definition glue (a : A) (b : B pt) : dsmash.mk a pt = dsmash.mk pt b :> ⋀ B :=
  gluel' a pt ⬝ gluer' pt b

  definition glue_pt_left (b : B pt) : glue (Point A) b = gluer' pt b :=
  whisker_right _ !con.right_inv ⬝ !idp_con

  definition glue_pt_right (a : A) : glue a (Point (B a)) = gluel' a pt :=
  proof whisker_left _ !con.right_inv qed

  definition ap_mk_left {a a' : A} (p : a = a') : ap (λa, dsmash.mk a (Point (B a))) p = gluel' a a' :=
  !ap_is_constant

  definition ap_mk_right {b b' : B pt} (p : b = b') : ap (dsmash.mk (Point A)) p = gluer' b b' :=
  !ap_is_constant

  protected definition rec {P : ⋀ B → Type} (Pmk : Πa b, P (dsmash.mk a b))
    (Pl : P auxl) (Pr : P auxr) (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (x : dsmash' B) : P x :=
  begin
    induction x with x b u,
    { induction x with a b, exact Pmk a b },
    { induction b, exact Pl, exact Pr },
    { induction u,
      { apply Pgl },
      { apply Pgr }}
  end

  theorem rec_gluel {P : ⋀ B → Type} {Pmk : Πa b, P (dsmash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (a : A) :
    apd (dsmash.rec Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  !pushout.rec_glue

  theorem rec_gluer {P : ⋀ B → Type} {Pmk : Πa b, P (dsmash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (b : B pt) :
    apd (dsmash.rec Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  !pushout.rec_glue

  theorem rec_glue {P : ⋀ B → Type} {Pmk : Πa b, P (dsmash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Π(b : B pt), Pmk pt b =[gluer b] Pr) (a : A) (b : B pt) :
    apd (dsmash.rec Pmk Pl Pr Pgl Pgr) (dsmash.glue a b) =
      (Pgl a ⬝o (Pgl pt)⁻¹ᵒ) ⬝o (Pgr pt ⬝o (Pgr b)⁻¹ᵒ) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +apd_con, +apd_inv, +rec_gluel, +rec_gluer]

  protected definition elim {P : Type} (Pmk : Πa b, P) (Pl Pr : P)
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (x : dsmash' B) : P :=
  dsmash.rec Pmk Pl Pr (λa, pathover_of_eq _ (Pgl a)) (λb, pathover_of_eq _ (Pgr b)) x

  -- an elim where you are forced to make (Pgl pt) and (Pgl pt) to be reflexivity
  protected definition elim' [reducible] {P : Type} (Pmk : Πa b, P)
    (Pgl : Πa : A, Pmk a pt = Pmk pt pt) (Pgr : Πb : B pt, Pmk pt b = Pmk pt pt)
    (ql : Pgl pt = idp) (qr : Pgr pt = idp) (x : dsmash' B) : P :=
  dsmash.elim Pmk (Pmk pt pt) (Pmk pt pt) Pgl Pgr x

  theorem elim_gluel {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (a : A) :
    ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  begin
    apply inj_inv !(pathover_constant (@gluel A B a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑dsmash.elim,rec_gluel],
  end

  theorem elim_gluer {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (b : B pt) :
    ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  begin
    apply inj_inv !(pathover_constant (@gluer A B b)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑dsmash.elim,rec_gluer],
  end

  theorem elim_glue {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (a : A) (b : B pt) :
    ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (glue a b) = (Pgl a ⬝ (Pgl pt)⁻¹) ⬝ (Pgr pt ⬝ (Pgr b)⁻¹) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +ap_con, +ap_inv, +elim_gluel, +elim_gluer]

end dsmash
open dsmash
attribute dsmash.mk dsmash.mk' dsmash.auxl dsmash.auxr [constructor]
attribute dsmash.elim' dsmash.rec dsmash.elim [unfold 9] [recursor 9]

namespace dsmash

  variables {A A' C : Type*} {B : A → Type*} {D : C → Type*} {a a' : A} {b : B a} {b' : B a'}

  definition mk_eq_mk (p : a = a') (q : b =[p] b') : dsmash.mk a b = dsmash.mk a' b' :=
  ap pushout.inl (dpair_eq_dpair p q)

  definition gluer2 (b : B a) (p : a = pt) : dsmash.mk a b = auxr :=
  mk_eq_mk p !pathover_tr ⬝ gluer _

  definition elim_gluel' {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (a a' : A) :
    ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluel' a a') = Pgl a ⬝ (Pgl a')⁻¹ :=
  !ap_con ⬝ whisker_left _ !ap_inv ⬝ !elim_gluel ◾ !elim_gluel⁻²

  definition elim_gluer' {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (b b' : B pt) :
    ap (dsmash.elim Pmk Pl Pr Pgl Pgr) (gluer' b b') = Pgr b ⬝ (Pgr b')⁻¹ :=
  !ap_con ⬝ whisker_left _ !ap_inv ⬝ !elim_gluer ◾ !elim_gluer⁻²

  definition elim_gluel'_same {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (a : A) :
    elim_gluel' Pgl Pgr a a =
      ap02 (dsmash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluel a)) ⬝ (con.right_inv (Pgl a))⁻¹ :=
  begin
    refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
    refine _ ⬝ whisker_right _ !con_idp⁻¹,
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
  end

  definition elim_gluer'_same {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B pt, Pmk pt b = Pr) (b : B pt) :
    elim_gluer' Pgl Pgr b b =
      ap02 (dsmash.elim Pmk Pl Pr Pgl Pgr) (con.right_inv (gluer b)) ⬝ (con.right_inv (Pgr b))⁻¹ :=
  begin
    refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
    refine _ ⬝ whisker_right _ !con_idp⁻¹,
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    apply eq_con_inv_of_con_eq, symmetry,
    apply con_right_inv_natural
  end

  definition elim'_gluel'_pt {P : Type} {Pmk : Πa b, P}
    (Pgl : Πa : A, Pmk a pt = Pmk pt pt) (Pgr : Πb : B pt, Pmk pt b = Pmk pt pt)
    (a : A) (ql : Pgl pt = idp) (qr : Pgr pt = idp) :
    ap (dsmash.elim' Pmk Pgl Pgr ql qr) (gluel' a pt) = Pgl a :=
  !elim_gluel' ⬝ whisker_left _ ql⁻²

  definition elim'_gluer'_pt {P : Type} {Pmk : Πa b, P}
    (Pgl : Πa : A, Pmk a pt = Pmk pt pt) (Pgr : Πb : B pt, Pmk pt b = Pmk pt pt)
    (b : B pt) (ql : Pgl pt = idp) (qr : Pgr pt = idp) :
    ap (dsmash.elim' Pmk Pgl Pgr ql qr) (gluer' b pt) = Pgr b :=
  !elim_gluer' ⬝ whisker_left _ qr⁻²

  protected definition rec_eq {C : Type} {f g : ⋀ B → C}
    (Pmk : Πa b, f (dsmash.mk a b) = g (dsmash.mk a b))
    (Pl : f auxl = g auxl) (Pr : f auxr = g auxr)
    (Pgl : Πa, square (Pmk a pt) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : Πb, square (Pmk pt b) Pr (ap f (gluer b)) (ap g (gluer b))) (x : dsmash' B) : f x = g x :=
  begin
    induction x with a b a b,
    { exact Pmk a b },
    { exact Pl },
    { exact Pr },
    { apply eq_pathover, apply Pgl },
    { apply eq_pathover, apply Pgr }
  end

  definition rec_eq_gluel {C : Type} {f g : ⋀ B → C}
    {Pmk : Πa b, f (dsmash.mk a b) = g (dsmash.mk a b)}
    {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
    (Pgl : Πa, square (Pmk a pt) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : Πb, square (Pmk pt b) Pr (ap f (gluer b)) (ap g (gluer b))) (a : A) :
      natural_square (dsmash.rec_eq Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  begin
    refine ap square_of_pathover !rec_gluel ⬝ _,
    apply to_right_inv !eq_pathover_equiv_square
  end

  definition rec_eq_gluer {C : Type} {f g : ⋀ B → C}
    {Pmk : Πa b, f (dsmash.mk a b) = g (dsmash.mk a b)}
    {Pl : f auxl = g auxl} {Pr : f auxr = g auxr}
    (Pgl : Πa, square (Pmk a pt) Pl (ap f (gluel a)) (ap g (gluel a)))
    (Pgr : Πb, square (Pmk pt b) Pr (ap f (gluer b)) (ap g (gluer b))) (b : B pt) :
      natural_square (dsmash.rec_eq Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  begin
    refine ap square_of_pathover !rec_gluer ⬝ _,
    apply to_right_inv !eq_pathover_equiv_square
  end

  /- the functorial action of the dependent smash product -/
  definition dsmash_functor' [unfold 7] (f : A →* C) (g : Πa, B a →* D (f a)) : ⋀ B → ⋀ D :=
  begin
    intro x, induction x,
    { exact dsmash.mk (f a) (g a b) },
    { exact auxl },
    { exact auxr },
    { exact ap (dsmash.mk (f a)) (respect_pt (g a)) ⬝ gluel (f a) },
    { exact gluer2 (g pt b) (respect_pt f) }
  end

  definition dsmash_functor [constructor] (f : A →* C) (g : Πa, B a →* D (f a)) : ⋀ B →* ⋀ D :=
  begin
    fapply pmap.mk,
    { exact dsmash_functor' f g },
    { exact mk_eq_mk (respect_pt f) (respect_pt (g pt) ⬝po apd (λa, Point (D a)) (respect_pt f)) },
  end

  infixr ` ⋀→ `:65 := dsmash_functor

  definition pmap_of_map' [constructor] (A : Type*) {B : Type} (f : A → B) :
    A →* pointed.MK B (f pt) :=
  pmap.mk f idp

  definition functor_gluel (f : A →* C) (g : Πa, B a →* D (f a)) (a : A) :
    ap (f ⋀→ g) (gluel a) = ap (dsmash.mk (f a)) (respect_pt (g a)) ⬝ gluel (f a) :=
  !elim_gluel

  definition functor_gluer (f : A →* C) (g : Πa, B a →* D (f a)) (b : B pt) :
    ap (f ⋀→ g) (gluer b) = gluer2 (g pt b) (respect_pt f) :=
  !elim_gluer

  -- definition functor_gluel2 {C : Type} {D : C → Type} (f : A → C) (g : Πa, B a → D (f a)) (a : A) :
  --   ap (@dsmash_functor A (pointed.MK C (f pt)) B (λc, pointed.MK (D c) _) (pmap_of_map' A f) (λa, pmap_of_map' (B a) (g a))) _ = _ :=
  -- begin
  --   refine !elim_gluel ⬝ !idp_con
  -- end

  -- definition functor_gluer2 {C D : Type} (f : A → C) (g : B → D) (b : B) :
  --   ap (pmap_of_map f pt ⋀→ pmap_of_map g pt) (gluer b) = gluer (g b) :=
  -- begin
  --   refine !elim_gluer ⬝ !idp_con
  -- end

  -- definition functor_gluel' (f : A →* C) (g : Πa, B a →* D (f a)) (a a' : A) :
  --   ap (f ⋀→ g) (gluel' a a') = ap (dsmash.mk (f a)) (respect_pt g) ⬝
  --     gluel' (f a) (f a') ⬝ (ap (dsmash.mk (f a')) (respect_pt g))⁻¹ :=
  -- begin
  --   refine !elim_gluel' ⬝ _,
  --   refine whisker_left _ !con_inv ⬝ _,
  --   refine !con.assoc⁻¹ ⬝ _, apply whisker_right,
  --   apply con.assoc
  -- end

  -- definition functor_gluer' (f : A →* C) (g : Πa, B a →* D (f a)) (b b' : B) :
  --   ap (f ⋀→ g) (gluer' b b') = ap (λc, dsmash.mk c (g b)) (respect_pt f) ⬝
  --     gluer' (g b) (g b') ⬝ (ap (λc, dsmash.mk c (g b')) (respect_pt f))⁻¹ :=
  -- begin
  --   refine !elim_gluer' ⬝ _,
  --   refine whisker_left _ !con_inv ⬝ _,
  --   refine !con.assoc⁻¹ ⬝ _, apply whisker_right,
  --   apply con.assoc
  -- end

  /- the statements of the above rules becomes easier if one of the functions respects the basepoint
     by reflexivity -/
  -- definition functor_gluel'2 {D : Type} (f : A →* C) (g : B → D) (a a' : A) :
  --   ap (f ⋀→ (pmap_of_map g pt)) (gluel' a a') = gluel' (f a) (f a') :=
  -- begin
  --   refine !ap_con ⬝ whisker_left _ !ap_inv ⬝ _,
  --   refine (!functor_gluel ⬝ !idp_con) ◾  (!functor_gluel ⬝ !idp_con)⁻²
  -- end

  -- definition functor_gluer'2 {C : Type} (f : A → C) (g : Πa, B a →* D (f a)) (b b' : B) :
  --   ap (pmap_of_map f pt ⋀→ g) (gluer' b b') = gluer' (g b) (g b') :=
  -- begin
  --   refine !ap_con ⬝ whisker_left _ !ap_inv ⬝ _,
  --   refine (!functor_gluer ⬝ !idp_con) ◾  (!functor_gluer ⬝ !idp_con)⁻²
  -- end

  -- definition functor_gluel'2 {C D : Type} (f : A → C) (g : B → D) (a a' : A) :
  --   ap (pmap_of_map f pt ⋀→ pmap_of_map g pt) (gluel' a a') = gluel' (f a) (f a') :=
  -- !ap_con ⬝ whisker_left _ !ap_inv ⬝ !functor_gluel2 ◾ !functor_gluel2⁻²

  -- definition functor_gluer'2 {C D : Type} (f : A → C) (g : B → D) (b b' : B) :
  --   ap (pmap_of_map f pt ⋀→ pmap_of_map g pt) (gluer' b b') = gluer' (g b) (g b') :=
  -- !ap_con ⬝ whisker_left _ !ap_inv ⬝ !functor_gluer2 ◾ !functor_gluer2⁻²

  -- lemma functor_gluel'2_same {C D : Type} (f : A → C) (g : B → D) (a : A) :
  --   functor_gluel'2 f g a a =
  --   ap02 (pmap_of_map f pt ⋀→ pmap_of_map g pt) (con.right_inv (gluel a)) ⬝
  --   (con.right_inv (gluel (f a)))⁻¹ :=
  -- begin
  --   refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
  --   refine _ ⬝ whisker_right _ !con_idp⁻¹,
  --   refine _ ⬝ !con.assoc⁻¹,
  --   apply whisker_left,
  --   apply eq_con_inv_of_con_eq, symmetry,
  --   apply con_right_inv_natural
  -- end

  -- lemma functor_gluer'2_same {C D : Type} (f : A → C) (g : B → D) (b : B) :
  --   functor_gluer'2 (pmap_of_map f pt) g b b =
  --   ap02 (pmap_of_map f pt ⋀→ pmap_of_map g pt) (con.right_inv (gluer b)) ⬝
  --   (con.right_inv (gluer (g b)))⁻¹ :=
  -- begin
  --   refine _ ⬝ whisker_right _ (eq_top_of_square (!ap_con_right_inv_sq))⁻¹,
  --   refine _ ⬝ whisker_right _ !con_idp⁻¹,
  --   refine _ ⬝ !con.assoc⁻¹,
  --   apply whisker_left,
  --   apply eq_con_inv_of_con_eq, symmetry,
  --   apply con_right_inv_natural
  -- end

  definition dsmash_functor_pid [constructor] (B : A → Type*) :
    pid A ⋀→ (λa, pid (B a)) ~* pid (⋀ B) :=
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

  /- the functorial action of the dependent smash product respects pointed homotopies, and some computation rules for this pointed homotopy -/
  definition dsmash_functor_phomotopy {f f' : A →* C} {g : Πa, B a →* D (f a)} {g' : Πa, B a →* D (f' a)}
    (h₁ : f ~* f') (h₂ : Πa, ptransport D (h₁ a) ∘* g a ~* g' a) : f ⋀→ g ~* f' ⋀→ g' :=
  begin
    induction h₁ using phomotopy_rec_idp,
    --induction h₂ using phomotopy_rec_idp,
    exact sorry --reflexivity
  end

  infixr ` ⋀~ `:78 := dsmash_functor_phomotopy

  /- a more explicit proof, if we ever need it -/
  -- definition dsmash_functor_homotopy [unfold 11] {f f' : A →* C} {g g' : Πa, B a →* D (f a)}
  --   (h₁ : f ~* f') (h₂ : g ~* g') : f ⋀→ g ~ f' ⋀→ g' :=
  -- begin
  --   intro x, induction x with a b a b,
  --   { exact ap011 dsmash.mk (h₁ a) (h₂ b) },
  --   { reflexivity },
  --   { reflexivity },
  --   { apply eq_pathover,
  --     refine !functor_gluel ⬝ph _ ⬝hp !functor_gluel⁻¹,
  --     refine _ ⬝v square_of_eq_top (ap_mk_left (h₁ a)),
  --     exact ap011_ap_square_right dsmash.mk (h₁ a) (to_homotopy_pt h₂) },
  --   { apply eq_pathover,
  --     refine !functor_gluer ⬝ph _ ⬝hp !functor_gluer⁻¹,
  --     refine _ ⬝v square_of_eq_top (ap_mk_right (h₂ b)),
  --     exact ap011_ap_square_left dsmash.mk (h₂ b) (to_homotopy_pt h₁) },
  -- end

  -- definition dsmash_functor_phomotopy [constructor] {f f' : A →* C} {g g' : Πa, B a →* D (f a)}
  --   (h₁ : f ~* f') (h₂ : g ~* g') : f ⋀→ g ~* f' ⋀→ g' :=
  -- begin
  --   apply phomotopy.mk (dsmash_functor_homotopy h₁ h₂),
  --   induction h₁ with h₁ h₁₀, induction h₂ with h₂ h₂₀,
  --   induction f with f f₀, induction g with g g₀,
  --   induction f' with f' f'₀, induction g' with g' g'₀,
  --   induction C with C c₀, induction D with D d₀, esimp at *,
  --   induction h₁₀, induction h₂₀, induction f'₀, induction g'₀,
  --   exact !ap_ap011⁻¹
  -- end

  -- definition dsmash_functor_phomotopy_refl (f : A →* C) (g : Πa, B a →* D (f a)) :
  --   dsmash_functor_phomotopy (phomotopy.refl f) (phomotopy.refl g) = phomotopy.rfl :=
  -- !phomotopy_rec_idp_refl ⬝ !phomotopy_rec_idp_refl

  -- definition dsmash_functor_phomotopy_symm {f₁ f₂ : A →* C} {g₁ g₂ : Πa, B a →* D (f a)}
  --   (h : f₁ ~* f₂) (k : g₁ ~* g₂) :
  --   dsmash_functor_phomotopy h⁻¹* k⁻¹* = (dsmash_functor_phomotopy h k)⁻¹* :=
  -- begin
  --   induction h using phomotopy_rec_idp, induction k using phomotopy_rec_idp,
  --   exact ap011 dsmash_functor_phomotopy !refl_symm !refl_symm ⬝ !dsmash_functor_phomotopy_refl ⬝
  --     !refl_symm⁻¹ ⬝ !dsmash_functor_phomotopy_refl⁻¹⁻²**
  -- end

  -- definition dsmash_functor_phomotopy_trans {f₁ f₂ f₃ : A →* C} {g₁ g₂ g₃ : Πa, B a →* D (f a)}
  --   (h₁ : f₁ ~* f₂) (h₂ : f₂ ~* f₃) (k₁ : g₁ ~* g₂) (k₂ : g₂ ~* g₃) :
  --   dsmash_functor_phomotopy (h₁ ⬝* h₂) (k₁ ⬝* k₂) =
  --   dsmash_functor_phomotopy h₁ k₁ ⬝* dsmash_functor_phomotopy h₂ k₂ :=
  -- begin
  --   induction h₁ using phomotopy_rec_idp, induction h₂ using phomotopy_rec_idp,
  --   induction k₁ using phomotopy_rec_idp, induction k₂ using phomotopy_rec_idp,
  --   refine ap011 dsmash_functor_phomotopy !trans_refl !trans_refl ⬝ !trans_refl⁻¹ ⬝ idp ◾** _,
  --   exact !dsmash_functor_phomotopy_refl⁻¹
  -- end

  -- definition dsmash_functor_phomotopy_trans_right {f₁ f₂ : A →* C} {g₁ g₂ g₃ : Πa, B a →* D (f a)}
  --   (h₁ : f₁ ~* f₂) (k₁ : g₁ ~* g₂) (k₂ : g₂ ~* g₃) :
  --   dsmash_functor_phomotopy h₁ (k₁ ⬝* k₂) =
  --   dsmash_functor_phomotopy h₁ k₁ ⬝* dsmash_functor_phomotopy phomotopy.rfl k₂ :=
  -- begin
  --   refine ap (λx, dsmash_functor_phomotopy x _) !trans_refl⁻¹ ⬝ !dsmash_functor_phomotopy_trans,
  -- end

  -- definition dsmash_functor_phomotopy_phsquare {f₁ f₂ f₃ f₄ : A →* C} {g₁ g₂ g₃ g₄ : Πa, B a →* D (f a)}
  --   {h₁ : f₁ ~* f₂} {h₂ : f₃ ~* f₄} {h₃ : f₁ ~* f₃} {h₄ : f₂ ~* f₄}
  --   {k₁ : g₁ ~* g₂} {k₂ : g₃ ~* g₄} {k₃ : g₁ ~* g₃} {k₄ : g₂ ~* g₄}
  --   (p : phsquare h₁ h₂ h₃ h₄) (q : phsquare k₁ k₂ k₃ k₄) :
  --   phsquare (dsmash_functor_phomotopy h₁ k₁)
  --            (dsmash_functor_phomotopy h₂ k₂)
  --            (dsmash_functor_phomotopy h₃ k₃)
  --            (dsmash_functor_phomotopy h₄ k₄) :=
  -- !dsmash_functor_phomotopy_trans⁻¹ ⬝ ap011 dsmash_functor_phomotopy p q ⬝
  -- !dsmash_functor_phomotopy_trans

  -- definition dsmash_functor_eq_of_phomotopy (f : A →* C) {g g' : Πa, B a →* D (f a)}
  --   (p : g ~* g') : ap (dsmash_functor f) (eq_of_phomotopy p) =
  --   eq_of_phomotopy (dsmash_functor_phomotopy phomotopy.rfl p) :=
  -- begin
  --   induction p using phomotopy_rec_idp,
  --   refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
  --   refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
  --   apply ap eq_of_phomotopy,
  --   exact !dsmash_functor_phomotopy_refl⁻¹
  -- end

  -- definition dsmash_functor_eq_of_phomotopy_left (g : Πa, B a →* D (f a)) {f f' : A →* C}
  --   (p : f ~* f') : ap (λf, dsmash_functor f g) (eq_of_phomotopy p) =
  --   eq_of_phomotopy (dsmash_functor_phomotopy p phomotopy.rfl) :=
  -- begin
  --   induction p using phomotopy_rec_idp,
  --   refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
  --   refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
  --   apply ap eq_of_phomotopy,
  --   exact !dsmash_functor_phomotopy_refl⁻¹
  -- end

  /- the functorial action preserves compositions, the interchange law -/
  -- definition dsmash_functor_pcompose_homotopy [unfold 11] {C D E F : Type}
  --   (f' : C → E) (f : A → C) (g' : D → F) (g : B → D) :
  --   (pmap_of_map f' (f pt) ∘* pmap_of_map f pt) ⋀→ (pmap_of_map g' (g pt) ∘* pmap_of_map g pt) ~
  --   (pmap_of_map f' (f pt) ⋀→ pmap_of_map g' (g pt)) ∘* (pmap_of_map f pt ⋀→ pmap_of_map g pt) :=
  -- begin
  --   intro x, induction x with a b a b,
  --   { reflexivity },
  --   { reflexivity },
  --   { reflexivity },
  --   { apply eq_pathover, refine !functor_gluel2 ⬝ph _, esimp,
  --     refine _ ⬝hp (ap_compose (_ ⋀→  _) _ _)⁻¹,
  --     refine _ ⬝hp ap02 _ !functor_gluel2⁻¹, refine _ ⬝hp !functor_gluel2⁻¹, exact hrfl },
  --   { apply eq_pathover, refine !functor_gluer2 ⬝ph _, esimp,
  --     refine _ ⬝hp (ap_compose (_ ⋀→ _) _ _)⁻¹,
  --     refine _ ⬝hp ap02 _ !functor_gluer2⁻¹, refine _ ⬝hp !functor_gluer2⁻¹, exact hrfl }
  -- end

  -- definition dsmash_functor_pcompose (f' : C →* E) (f : A →* C) (g' : D →* F) (g : Πa, B a →* D (f a)) :
  --   (f' ∘* f) ⋀→ (g' ∘* g) ~* f' ⋀→ g' ∘* f ⋀→ g :=
  -- begin
  --   induction C with C, induction D with D, induction E with E, induction F with F,
  --   induction f with f f₀, induction f' with f' f'₀, induction g with g g₀,
  --   induction g' with g' g'₀, esimp at *,
  --   induction f₀, induction f'₀, induction g₀, induction g'₀,
  --   fapply phomotopy.mk,
  --   { rexact dsmash_functor_pcompose_homotopy f' f g' g },
  --   { reflexivity }
  -- end

  -- definition dsmash_functor_split (f : A →* C) (g : Πa, B a →* D (f a)) :
  --   f ⋀→ g ~* f ⋀→ pid D ∘* pid A ⋀→ g :=
  -- dsmash_functor_phomotopy !pcompose_pid⁻¹* !pid_pcompose⁻¹* ⬝* !dsmash_functor_pcompose

  -- definition dsmash_functor_split_rev (f : A →* C) (g : Πa, B a →* D (f a)) :
  --   f ⋀→ g ~* pid C ⋀→ g ∘* f ⋀→ pid B :=
  -- dsmash_functor_phomotopy !pid_pcompose⁻¹* !pcompose_pid⁻¹* ⬝* !dsmash_functor_pcompose

  /- An alternative proof which doesn't start by applying inductions, so which is more explicit -/
  -- definition dsmash_functor_pcompose_homotopy [unfold 11] (f' : C →* E) (f : A →* C) (g' : D →* F)
  --   (g : Πa, B a →* D (f a)) : (f' ∘* f) ⋀→ (g' ∘* g) ~ (f' ⋀→ g') ∘* (f ⋀→ g) :=
  -- begin
  --   intro x, induction x with a b a b,
  --   { reflexivity },
  --   { reflexivity },
  --   { reflexivity },
  --   { apply eq_pathover, exact abstract begin apply hdeg_square,
  --     refine !functor_gluel ⬝ _ ⬝ (ap_compose (f' ⋀→ g') _ _)⁻¹,
  --     refine whisker_right _ !ap_con ⬝ !con.assoc ⬝ _ ⬝ ap02 _ !functor_gluel⁻¹,
  --     refine (!ap_compose'⁻¹ ⬝ !ap_compose') ◾ proof !functor_gluel⁻¹ qed ⬝ !ap_con⁻¹ end end },
  --   { apply eq_pathover, exact abstract begin apply hdeg_square,
  --     refine !functor_gluer ⬝ _ ⬝ (ap_compose (f' ⋀→ g') _ _)⁻¹,
  --     refine whisker_right _ !ap_con ⬝ !con.assoc ⬝ _ ⬝ ap02 _ !functor_gluer⁻¹,
  --     refine (!ap_compose'⁻¹ ⬝ !ap_compose') ◾ proof !functor_gluer⁻¹ qed ⬝ !ap_con⁻¹ end end }
  -- end

  -- definition dsmash_functor_pcompose [constructor] (f' : C →* E) (f : A →* C) (g' : D →* F) (g : Πa, B a →* D (f a)) :
  --   (f' ∘* f) ⋀→ (g' ∘* g) ~* f' ⋀→ g' ∘* f ⋀→ g :=
  -- begin
  --   fapply phomotopy.mk,
  --   { exact dsmash_functor_pcompose_homotopy f' f g' g },
  --   { exact abstract begin induction C, induction D, induction E, induction F,
  --     induction f with f f₀, induction f' with f' f'₀, induction g with g g₀,
  --     induction g' with g' g'₀, esimp at *,
  --     induction f₀, induction f'₀, induction g₀, induction g'₀, reflexivity end end }
  -- end


  -- definition dsmash_functor_pid_pcompose [constructor] (A : Type*) (g' : C →* D) (g : B →* C)
  --   : pid A ⋀→ (g' ∘* g) ~* pid A ⋀→ g' ∘* pid A ⋀→ g :=
  -- dsmash_functor_phomotopy !pid_pcompose⁻¹* phomotopy.rfl ⬝* !dsmash_functor_pcompose

  -- definition dsmash_functor_pcompose_pid [constructor] (B : Type*) (f' : C →* D) (f : A →* C)
  --   : (f' ∘* f) ⋀→ pid B ~* f' ⋀→ (pid B) ∘* f ⋀→ (pid B) :=
  -- dsmash_functor_phomotopy phomotopy.rfl !pid_pcompose⁻¹* ⬝* !dsmash_functor_pcompose

  /- composing commutes with applying homotopies -/
  -- definition dsmash_functor_pcompose_phomotopy {f₂ f₂' : C →* E} {f f' : A →* C} {g₂ g₂' : D →* F}
  --   {g g' : Πa, B a →* D (f a)} (h₂ : f₂ ~* f₂') (h₁ : f ~* f') (k₂ : g₂ ~* g₂') (k₁ : g ~* g') :
  --   phsquare (dsmash_functor_pcompose f₂ f g₂ g)
  --            (dsmash_functor_pcompose f₂' f' g₂' g')
  --            (dsmash_functor_phomotopy (h₂ ◾* h₁) (k₂ ◾* k₁))
  --            (dsmash_functor_phomotopy h₂ k₂ ◾* dsmash_functor_phomotopy h₁ k₁) :=
  -- begin
  --   induction h₁ using phomotopy_rec_idp, induction h₂ using phomotopy_rec_idp,
  --   induction k₁ using phomotopy_rec_idp, induction k₂ using phomotopy_rec_idp,
  --   refine (ap011 dsmash_functor_phomotopy !pcompose2_refl !pcompose2_refl ⬝
  --     !dsmash_functor_phomotopy_refl) ⬝ph** phvrfl ⬝hp**
  --     (ap011 pcompose2 !dsmash_functor_phomotopy_refl !dsmash_functor_phomotopy_refl ⬝
  --     !pcompose2_refl)⁻¹,
  -- end

  -- definition dsmash_functor_pid_pcompose_phomotopy_right (g₂ : D →* E) {g g' : Πa, B a →* D (f a)}
  --   (k : g ~* g') :
  --   phsquare (dsmash_functor_pid_pcompose A g₂ g)
  --            (dsmash_functor_pid_pcompose A g₂ g')
  --            (dsmash_functor_phomotopy phomotopy.rfl (pwhisker_left g₂ k))
  --            (pwhisker_left (pid A ⋀→ g₂) (dsmash_functor_phomotopy phomotopy.rfl k)) :=
  -- begin
  --   refine dsmash_functor_phomotopy_phsquare _ _ ⬝h** !dsmash_functor_pcompose_phomotopy ⬝hp**
  --     ((ap (pwhisker_right _) !dsmash_functor_phomotopy_refl) ◾** idp ⬝ !pcompose2_refl_left),
  --     exact (!pcompose2_refl ⬝ph** phvrfl)⁻¹ʰ**,
  --     exact (phhrfl ⬝hp** !pcompose2_refl_left⁻¹)
  -- end

  section
  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type*} {B₀₀ B₂₀ B₀₂ B₂₂ : Type*}
            {f₁₀ : A₀₀ →* A₂₀} {f₀₁ : A₀₀ →* A₀₂} {f₂₁ : A₂₀ →* A₂₂} {f₁₂ : A₀₂ →* A₂₂}
            {g₁₀ : B₀₀ →* B₂₀} {g₀₁ : B₀₀ →* B₀₂} {g₂₁ : B₂₀ →* B₂₂} {g₁₂ : B₀₂ →* B₂₂}

  /- applying the functorial action of dsmash to squares of pointed maps -/
  -- definition dsmash_functor_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare g₁₀ g₁₂ g₀₁ g₂₁) :
  --   psquare (f₁₀ ⋀→ g₁₀) (f₁₂ ⋀→ g₁₂) (f₀₁ ⋀→ g₀₁) (f₂₁ ⋀→ g₂₁) :=
  -- !dsmash_functor_pcompose⁻¹* ⬝* dsmash_functor_phomotopy p q ⬝* !dsmash_functor_pcompose
  end

  /- f ∧ g is a pointed equivalence if f and g are -/
  definition dsmash_functor_using_pushout [unfold 7] (f : A →* C) (g : Πa, B a →* D (f a)) :
    ⋀ B → ⋀ D :=
  begin
    refine pushout.functor (f +→ (transport D (respect_pt f) ∘ g pt)) (sigma_functor f g) id _ _,
    { intro v, induction v with a b,
      exact ap (dpair _) (respect_pt (g a)),
      exact sigma_eq (respect_pt f) !pathover_tr },
    { intro v, induction v with a b: reflexivity }
  end

  definition dsmash_functor_homotopy_pushout_functor (f : A →* C) (g : Πa, B a →* D (f a)) :
    f ⋀→ g ~ dsmash_functor_using_pushout f g :=
  begin
    intro x, induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, refine !elim_gluel ⬝ph _ ⬝hp !pushout.elim_glue⁻¹,
      apply hdeg_square, esimp, apply whisker_right, apply ap_compose },
    { apply eq_pathover, refine !elim_gluer ⬝ph _ ⬝hp !pushout.elim_glue⁻¹,
      apply hdeg_square, reflexivity }
  end

  definition dsmash_pequiv [constructor] (f : A ≃* C) (g : Πa, B a ≃* D (f a)) : ⋀ B ≃* ⋀ D :=
  begin
    fapply pequiv_of_pmap (f ⋀→ g),
    refine homotopy_closed _ (dsmash_functor_homotopy_pushout_functor f g)⁻¹ʰᵗʸ _,
    apply pushout.is_equiv_functor,
    { apply is_equiv_sum_functor, apply is_equiv_compose, apply pequiv.to_is_equiv,
      exact to_is_equiv (equiv_ap _ _) },
    apply is_equiv_sigma_functor, intro a, apply pequiv.to_is_equiv
  end

  infixr ` ⋀≃ `:80 := dsmash_pequiv

  definition dsmash_pequiv_left [constructor] (B : C → Type*) (f : A ≃* C) :
    ⋀ (B ∘ f) ≃* ⋀ B :=
  f ⋀≃ λa, pequiv.rfl

  definition dsmash_pequiv_right [constructor] {D : A → Type*} (g : Πa, B a ≃* D a) : ⋀ B ≃* ⋀ D :=
  pequiv.rfl ⋀≃ g

  /- f ∧ g is constant if f is constant -/
  -- definition dsmash_functor_pconst_left_homotopy [unfold 6] {B' : Type} (f : B → B') (x : ⋀ B) :
  --   (pconst A C ⋀→ pmap_of_map f pt) x = pt :=
  -- begin
  --   induction x with a b a b,
  --   { exact gluer' (f b) pt },
  --   { exact (gluel pt)⁻¹ },
  --   { exact (gluer pt)⁻¹ᵖ },
  --   { apply eq_pathover, note x := functor_gluel2 (λx : A, Point A') f a,
  --     refine x ⬝ph _, refine _ ⬝hp !ap_constant⁻¹, apply square_of_eq,
  --     rexact con.right_inv (gluer (f pt)) ⬝ (con.right_inv (gluel pt))⁻¹ },
  --   { apply eq_pathover, note x := functor_gluer2 (λx : A, Point A') f b,
  --     refine x ⬝ph _, refine _ ⬝hp !ap_constant⁻¹, apply square_of_eq, reflexivity }
  -- end

  -- definition dsmash_functor_pconst_left (f : B →* B') : pconst A A' ⋀→ f ~* pconst (⋀ B) (A' ∧ B') :=
  -- begin
  --   induction B' with B', induction f with f f₀, esimp at *, induction f₀,
  --   fapply phomotopy.mk,
  --   { exact dsmash_functor_pconst_left_homotopy f },
  --   { rexact con.right_inv (gluer (f pt)) }
  -- end

  -- definition dsmash_functor_pconst_left_phomotopy {f f' : B →* B'} (p : f ~* f') :
  --   phomotopy.refl (pconst A A') ⋀~ p ⬝* dsmash_functor_pconst_left f' = dsmash_functor_pconst_left f :=
  -- begin
  --   induction p using phomotopy_rec_idp,
  --   exact !dsmash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans
  -- end

  -- /- This makes dsmash_functor into a pointed map (B →* B') →* (⋀ B →* ⋀ B') -/

  -- definition dsmash_functor_left [constructor] (A A' B : Type*) :
  --   ppmap A A' →* ppmap (⋀ B) (A' ∧ B) :=
  -- pmap.mk (λf, f ⋀→ pid B) (eq_of_phomotopy (dsmash_functor_pconst_left (pid B)))

  /- We want to show that dsmash_functor_left is natural in A, B and C.

     For this we need two coherence rules. Given the function h := (f' ∘ f) ⋀→ (g' ∘ g) and suppose
     that either f' or f is constant. There are two ways to show that h is constant: either by using
     exchange, or directly. We need to show that these two proofs result in the same pointed
     homotopy. First we do the case where f is constant -/

  -- private definition my_squarel {A : Type} {a₁ a₂ a₃ : A} (p₁ : a₁ = a₃) (p₂ : a₂ = a₃) :
  --   square (p₁ ⬝ p₂⁻¹) p₂⁻¹ p₁ idp :=
  -- proof square_of_eq idp qed

  -- private definition my_squarer {A : Type} {a₁ a₂ a₃ : A} (p₁ : a₁ = a₃) (p₂ : a₁ = a₂) :
  --   square (p₁ ⬝ p₁⁻¹) p₂⁻¹ p₂ idp :=
  -- proof square_of_eq (con.right_inv p₁ ⬝ (con.right_inv p₂)⁻¹) qed

  -- private definition my_cube_fillerl {B C : Type} {g : B → C} {fa₁ fa₂ b₀ : B}
  --   {pa₁ : fa₁ = b₀} {pa₂ : fa₂ = b₀} {qa₁ : g (fa₁) = g b₀} {qa₂ : g (fa₂) = g b₀}
  --   (ra₁ : ap g (pa₁) = qa₁) (ra₂ : ap g (pa₂) = qa₂) :
  --   cube (hrfl ⬝hp (ra₁)⁻¹) hrfl
  --        (my_squarel (qa₁) (qa₂)) (aps g (my_squarel (pa₁) (pa₂)))
  --        (hrfl ⬝hp (!ap_con ⬝ whisker_left _ !ap_inv ⬝ (ra₁) ◾ (ra₂)⁻²)⁻¹)
  --          (hrfl ⬝hp (ra₂)⁻²⁻¹ ⬝hp !ap_inv⁻¹) :=
  -- begin
  --   induction ra₂, induction ra₁, induction pa₂, induction pa₁, exact idc
  -- end

  -- private definition my_cube_fillerr {B C : Type} {g : B → C} {b₀ bl br : B}
  --   {pl : b₀ = bl} {pr : b₀ = br} {ql : g b₀ = g bl} {qr : g b₀ = g br}
  --   (sl : ap g pl = ql) (sr : ap g pr = qr) :
  --   cube (hrfl ⬝hp sr⁻¹) hrfl
  --        (my_squarer ql qr) (aps g (my_squarer pl pr))
  --        (hrfl ⬝hp (!ap_con ⬝ whisker_left _ !ap_inv ⬝ sl ◾ sl⁻²)⁻¹)
  --        (hrfl ⬝hp sr⁻²⁻¹ ⬝hp !ap_inv⁻¹) :=
  -- begin
  --   induction sr, induction sl, induction pr, induction pl, exact idc
  -- end

  -- definition dsmash_functor_pcompose_pconst2_homotopy {A A' A'' B B' B'' : Type}
  --   (a₀ : A) (b₀ : B) (a₀' : A') (f' : A' → A'') (g' : B' → B'') (g : B → B')
  --   (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
  --   square (dsmash_functor_pcompose_homotopy f' (λ a, a₀') g' g x)
  --   idp
  --   (dsmash_functor_pconst_left_homotopy (λ a, g' (g a)) x)
  --   (ap (dsmash_functor' (pmap.mk f' (refl (f' a₀'))) (pmap.mk g' (refl (g' (g b₀)))))
  --     (dsmash_functor_pconst_left_homotopy g x)) :=
  -- begin
  --   induction x with a b a b,
  --   { refine _ ⬝hp (functor_gluer'2 f' g' (g b) (g b₀))⁻¹, exact hrfl },
  --   { refine _ ⬝hp !ap_inv⁻¹, refine _ ⬝hp !functor_gluel2⁻²⁻¹, exact hrfl },
  --   { refine _ ⬝hp !ap_inv⁻¹, refine _ ⬝hp !functor_gluer2⁻²⁻¹, exact hrfl },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluel ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluel ⬝p2 _ ⬝2p !natural_square_ap_fn⁻¹,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (ap (aps _) !rec_eq_gluel ⬝ !aps_eq_hconcat)⁻¹,
  --     apply whisker021, refine _ ⬝2p !aps_hconcat_eq⁻¹, apply move221,
  --     refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
  --     apply my_cube_fillerr end end },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluer ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluer ⬝p2 _ ⬝2p !natural_square_ap_fn⁻¹,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (ap (aps _) !rec_eq_gluer ⬝ !aps_eq_hconcat)⁻¹,
  --     apply whisker021, refine _ ⬝2p !aps_hconcat_eq⁻¹, apply move221,
  --     refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
  --     apply my_cube_fillerl end end }
  -- end

  -- definition dsmash_functor_pcompose_pconst2 (f' : A' →* A'') (g' : B' →* B'') (g : B →* B') :
  --   phsquare (dsmash_functor_pcompose f' (pconst A A') g' g)
  --            (dsmash_functor_pconst_left (g' ∘* g))
  --            (dsmash_functor_phomotopy (pcompose_pconst f') phomotopy.rfl)
  --            (pwhisker_left (f' ⋀→ g') (dsmash_functor_pconst_left g) ⬝*
  --              pcompose_pconst (f' ⋀→ g')) :=
  -- begin
  --   induction A with A a₀, induction B with B b₀,
  --   induction A' with A' a₀', induction B' with B' b₀',
  --   induction A'' with A'' a₀'', induction B'' with B'' b₀'',
  --   induction f' with f' f'₀, induction g' with g' g₀', induction g with g g₀,
  --   esimp at *, induction f'₀, induction g₀', induction g₀,
  --   refine !dsmash_functor_phomotopy_refl ⬝ph** _, refine _ ⬝ !refl_trans⁻¹,
  --   fapply phomotopy_eq,
  --   { intro x, refine eq_of_square _ ⬝ !con_idp,
  --     exact dsmash_functor_pcompose_pconst2_homotopy a₀ b₀ a₀' f' g' g x },
  --   { refine _ ⬝ !idp_con⁻¹,
  --     refine whisker_right _ (!whisker_right_idp ⬝ !eq_of_square_hrfl_hconcat_eq) ⬝ _,
  --     refine !con.assoc ⬝ _, apply con_eq_of_eq_inv_con,
  --     refine whisker_right _ _ ⬝ _, rotate 1, rexact functor_gluer'2_same f' g' (g b₀),
  --     refine !inv_con_cancel_right ⬝ _,
  --     refine !whisker_left_idp⁻¹ ⬝ _,
  --     refine !con_idp ⬝ _,
  --     apply whisker_left,
  --     apply ap (whisker_left idp),
  --     exact (!idp_con ⬝ !idp_con ⬝ !whisker_right_idp ⬝ !idp_con)⁻¹ }
  -- end

  -- /- a version where the left maps are identities -/
  -- definition dsmash_functor_pcompose_pconst2_pid (f' : A' →* A'') :
  --   phsquare (dsmash_functor_pcompose_pid B f' (pconst A A'))
  --            (dsmash_functor_pconst_left (pid B))
  --            (pcompose_pconst f' ⋀~ phomotopy.rfl)
  --            (pwhisker_left (f' ⋀→ pid B) (dsmash_functor_pconst_left (pid B)) ⬝*
  --              pcompose_pconst (f' ⋀→ pid B)) :=
  -- (!dsmash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans) ⬝pv**
  -- dsmash_functor_pcompose_pconst2 f' (pid B) (pid B)

  -- /- a small rewrite of the previous -/
  -- -- definition dsmash_functor_pcompose_pid_pconst' (f' : A' →* A'') :
  -- --   pwhisker_left (f' ⋀→ pid B) (dsmash_functor_pconst_left (pid B)) ⬝*
  -- --   pcompose_pconst (f' ⋀→ pid B) =
  -- --   (dsmash_functor_pcompose_pid B f' (pconst A A'))⁻¹* ⬝*
  -- --   (pcompose_pconst f' ⋀~ phomotopy.rfl ⬝*
  -- --   dsmash_functor_pconst_left (pid B)) :=
  -- -- begin
  -- --   apply eq_symm_trans_of_trans_eq,
  -- --   exact dsmash_functor_pcompose_pid_pconst f'
  -- -- end

  -- /- if f' is constant -/
  -- definition dsmash_functor_pcompose_pconst1_homotopy [unfold 13] {A A' A'' B B' B'' : Type}
  --   (a₀ : A) (b₀ : B) (a₀'' : A'') (f : A → A') (g' : B' → B'') (g : B → B')
  --   (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
  --   square (dsmash_functor_pcompose_homotopy (λa', a₀'') f g' g x)
  --   idp
  --   (dsmash_functor_pconst_left_homotopy (λ a, g' (g a)) x)
  --   (dsmash_functor_pconst_left_homotopy g'
  --     ((pmap_of_map f a₀ ⋀→ pmap_of_map g b₀) x)) :=
  -- begin
  --   induction x with a b a b,
  --   { exact hrfl },
  --   { exact hrfl },
  --   { exact hrfl },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluel ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluel ⬝p2 _ ⬝2p
  --       (natural_square_compose (dsmash_functor_pconst_left_homotopy g') _ _)⁻¹ᵖ,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (natural_square_eq2 _ !functor_gluel2)⁻¹ᵖ,
  --     apply whisker021,
  --     refine _ ⬝1p ap hdeg_square (eq_of_square (!ap_constant_compose⁻¹ʰ) ⬝ !idp_con)⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝2p !rec_eq_gluel⁻¹, apply whisker021,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
  --     exact rfl2 end end },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluer ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluer ⬝p2 _ ⬝2p
  --       (natural_square_compose (dsmash_functor_pconst_left_homotopy g') _ _)⁻¹ᵖ,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (natural_square_eq2 _ !functor_gluer2)⁻¹ᵖ,
  --     apply whisker021,
  --     refine _ ⬝1p ap hdeg_square (eq_of_square (!ap_constant_compose⁻¹ʰ) ⬝ !idp_con)⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝2p !rec_eq_gluer⁻¹, apply whisker021,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
  --     exact rfl2 end end },
  -- end

  -- definition dsmash_functor_pcompose_pconst1 (f : A →* A') (g' : B' →* B'') (g : B →* B') :
  --   phsquare (dsmash_functor_pcompose (pconst A' A'') f g' g)
  --            (dsmash_functor_pconst_left (g' ∘* g))
  --            (pconst_pcompose f ⋀~ phomotopy.rfl)
  --            (pwhisker_right (f ⋀→ g) (dsmash_functor_pconst_left g') ⬝*
  --              pconst_pcompose (f ⋀→ g)) :=
  -- begin
  --   induction A with A a₀, induction B with B b₀,
  --   induction A' with A' a₀', induction B' with B' b₀',
  --   induction A'' with A'' a₀'', induction B'' with B'' b₀'',
  --   induction f with f f₀, induction g' with g' g₀', induction g with g g₀,
  --   esimp at *, induction f₀, induction g₀', induction g₀,
  --   refine !dsmash_functor_phomotopy_refl ⬝ph** _, refine _ ⬝ !refl_trans⁻¹,
  --   fapply phomotopy_eq,
  --   { intro x, refine eq_of_square (dsmash_functor_pcompose_pconst1_homotopy a₀ b₀ a₀'' f g' g x) },
  --   { refine whisker_right _ (!whisker_right_idp ⬝ !eq_of_square_hrfl) ⬝ _,
  --     have H : Π{A : Type} {a a' : A} (p : a = a'),
  --              idp_con (p ⬝ p⁻¹) ⬝ con.right_inv p = idp ⬝
  --              whisker_left idp (idp ⬝ (idp ⬝ proof whisker_right idp (idp_con (p ⬝ p⁻¹ᵖ))⁻¹ᵖ qed ⬝
  --                whisker_left idp (con.right_inv p))), by intros; induction p; reflexivity,
  --     rexact H (gluer (g' (g b₀))) }
  -- end

  -- /- a version where the left maps are identities -/
  -- definition dsmash_functor_pcompose_pconst1_pid (f : A →* A') :
  --   phsquare (dsmash_functor_pcompose_pid B (pconst A' A'') f)
  --            (dsmash_functor_pconst_left (pid B))
  --            (pconst_pcompose f ⋀~ phomotopy.rfl)
  --            (pwhisker_right (f ⋀→ pid B) (dsmash_functor_pconst_left (pid B)) ⬝*
  --              pconst_pcompose (f ⋀→ pid B)) :=
  -- (!dsmash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans) ⬝pv**
  -- dsmash_functor_pcompose_pconst1 f (pid B) (pid B)

  -- /- Using these lemmas we show that dsmash_functor_left is natural in all arguments -/

  -- definition dsmash_functor_left_natural_left (B C : Type*) (f : A' →* A) :
  --   psquare (dsmash_functor_left A B C) (dsmash_functor_left A' B C)
  --           (ppcompose_right f) (ppcompose_right (f ⋀→ pid C)) :=
  -- begin
  --   refine _⁻¹*,
  --   fapply phomotopy_mk_ppmap,
  --   { intro g, exact dsmash_functor_pcompose_pid C g f },
  --   { refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !dsmash_functor_eq_of_phomotopy_left ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
  --     apply dsmash_functor_pcompose_pconst1_pid }
  -- end

  -- definition dsmash_functor_left_natural_middle (A C : Type*) (f : B →* B') :
  --   psquare (dsmash_functor_left A B C) (dsmash_functor_left A B' C)
  --           (ppcompose_left f) (ppcompose_left (f ⋀→ pid C)) :=
  -- begin
  --   refine _⁻¹*,
  --   fapply phomotopy_mk_ppmap,
  --   { exact dsmash_functor_pcompose_pid C f },
  --   { refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !dsmash_functor_eq_of_phomotopy_left ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
  --     apply dsmash_functor_pcompose_pconst2_pid }
  -- end

  -- definition dsmash_functor_left_natural_right (A B : Type*) (f : C →* C') :
  --   psquare (dsmash_functor_left A B C) (ppcompose_right (pid A ⋀→ f))
  --           (dsmash_functor_left A B C') (ppcompose_left (pid B ⋀→ f)) :=
  -- begin
  --   refine _⁻¹*,
  --   fapply phomotopy_mk_ppmap,
  --   { intro g, exact dsmash_functor_psquare proof phomotopy.rfl qed proof phomotopy.rfl qed },
  --   { esimp,
  --     refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
  --     apply eq_of_phsquare,
  --     refine (phmove_bot_of_left _ !dsmash_functor_pcompose_pconst1⁻¹ʰ**) ⬝h**
  --       (!dsmash_functor_phomotopy_refl ⬝pv** !phhrfl) ⬝h** !dsmash_functor_pcompose_pconst2 ⬝vp** _,
  --     refine !trans_assoc ⬝ !trans_assoc ⬝ idp ◾** _ ⬝ !trans_refl,
  --     refine idp ◾** !refl_trans ⬝ !trans_left_inv }
  -- end

  -- definition dsmash_functor_left_natural_middle_phomotopy (A C : Type*) {f f' : B →* B'}
  --   (p : f ~* f') : dsmash_functor_left_natural_middle A C f =
  --   ppcompose_left_phomotopy p ⬝ph* dsmash_functor_left_natural_middle A C f' ⬝hp*
  --   ppcompose_left_phomotopy (p ⋀~ phomotopy.rfl) :=
  -- begin
  --   induction p using phomotopy_rec_idp,
  --   symmetry,
  --   refine !ppcompose_left_phomotopy_refl ◾ph* idp ◾hp*
  --    (ap ppcompose_left_phomotopy !dsmash_functor_phomotopy_refl ⬝
  --    !ppcompose_left_phomotopy_refl) ⬝ _,
  --   exact !rfl_phomotopy_hconcat ⬝ !hconcat_phomotopy_rfl
  -- end

  -- /- the following is not really used, but a symmetric version of the natural equivalence
  --    dsmash_functor_left -/
  -- /- f ∧ g is constant if g is constant -/
  -- definition dsmash_functor_pconst_right_homotopy [unfold 6] {C : Type} (f : A → C) (x : ⋀ B) :
  --   (pmap_of_map f pt ⋀→ pconst B D) x = pt :=
  -- begin
  --   induction x with a b a b,
  --   { exact gluel' (f a) pt },
  --   { exact (gluel pt)⁻¹ },
  --   { exact (gluer pt)⁻¹ },
  --   { apply eq_pathover, note x := functor_gluel2 f (λx : B, Point D) a, esimp [pconst] at *,
  --     refine x ⬝ph _, refine _ ⬝hp !ap_constant⁻¹, apply square_of_eq, reflexivity },
  --   { apply eq_pathover, note x := functor_gluer2 f (λx : B, Point D) b, esimp [pconst] at *,
  --     refine x ⬝ph _, refine _ ⬝hp !ap_constant⁻¹, apply square_of_eq,
  --     rexact con.right_inv (gluel (f pt)) ⬝ (con.right_inv (gluer pt))⁻¹ }
  -- end

  -- definition dsmash_functor_pconst_right (f : A →* C) :
  --   f ⋀→ (pconst B D) ~* pconst (⋀ B) (⋀ D) :=
  -- begin
  --   induction C with C, induction f with f f₀, esimp at *, induction f₀,
  --   fapply phomotopy.mk,
  --   { exact dsmash_functor_pconst_right_homotopy f },
  --   { rexact con.right_inv (gluel (f pt)) }
  -- end

  -- definition dsmash_functor_pconst_right_phomotopy {f f' : A →* C} (p : f ~* f') :
  --   dsmash_functor_phomotopy p (phomotopy.refl (pconst B D)) ⬝* dsmash_functor_pconst_right f' =
  --   dsmash_functor_pconst_right f :=
  -- begin
  --   induction p using phomotopy_rec_idp,
  --   exact !dsmash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans
  -- end

  -- /- This makes dsmash_functor into a pointed map (B →* B') →* (⋀ B →* ⋀ B') -/

  -- definition dsmash_functor_right [constructor] (B : A → Type*) (C : Type*) :
  --   ppmap B C →* ppmap (⋀ B) (A ∧ C) :=
  -- pmap.mk (dsmash_functor (pid A)) (eq_of_phomotopy (dsmash_functor_pconst_right (pid A)))

  -- /- We want to show that dsmash_functor_right is natural in A, B and C.

  --    For this we need two coherence rules. Given the function h := (f' ∘ f) ⋀→ (g' ∘ g) and suppose
  --    that either g' or g is constant. There are two ways to show that h is constant: either by using
  --    exchange, or directly. We need to show that these two proofs result in the same pointed
  --    homotopy. First we do the case where g is constant -/

  -- definition dsmash_functor_pcompose_pconst4_homotopy {A B C D E F : Type}
  --   (a₀ : A) (b₀ : B) (d₀ : D) (f' : C → E) (f : A → C) (g : D → F)
  --   (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
  --   square (dsmash_functor_pcompose_homotopy f' f g (λ a, d₀) x)
  --   idp
  --   (dsmash_functor_pconst_right_homotopy (λ a, f' (f a)) x)
  --   (ap (dsmash_functor' (pmap.mk f' (refl (f' (f a₀)))) (pmap.mk g (refl (g d₀))))
  --     (dsmash_functor_pconst_right_homotopy f x)) :=
  -- begin
  --   induction x with a b a b,
  --   { refine _ ⬝hp (functor_gluel'2 f' g (f a) (f a₀))⁻¹, exact hrfl },
  --   { refine _ ⬝hp !ap_inv⁻¹, refine _ ⬝hp !functor_gluel2⁻²⁻¹, exact hrfl },
  --   { refine _ ⬝hp !ap_inv⁻¹, refine _ ⬝hp !functor_gluer2⁻²⁻¹, exact hrfl },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluel ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluel ⬝p2 _ ⬝2p !natural_square_ap_fn⁻¹,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (ap (aps _) !rec_eq_gluel ⬝ !aps_eq_hconcat)⁻¹,
  --     apply whisker021, refine _ ⬝2p !aps_hconcat_eq⁻¹, apply move221,
  --     refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
  --     apply my_cube_fillerl end end },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluer ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluer ⬝p2 _ ⬝2p !natural_square_ap_fn⁻¹,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (ap (aps _) !rec_eq_gluer ⬝ !aps_eq_hconcat)⁻¹,
  --     apply whisker021, refine _ ⬝2p !aps_hconcat_eq⁻¹, apply move221,
  --     refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_ap_constant)),
  --     apply my_cube_fillerr end end }
  -- end

  -- definition dsmash_functor_pcompose_pconst4 (f' : C →* E) (f : A →* C) (g : D →* F) :
  --   phsquare (dsmash_functor_pcompose f' f g (pconst B D))
  --            (dsmash_functor_pconst_right (f' ∘* f))
  --            (dsmash_functor_phomotopy phomotopy.rfl (pcompose_pconst g))
  --            (pwhisker_left (f' ⋀→ g) (dsmash_functor_pconst_right f) ⬝*
  --              pcompose_pconst (f' ⋀→ g)) :=
  -- begin
  --   induction A with A a₀, induction B with B b₀,
  --   induction E with E e₀, induction C with C c₀, induction F with F x₀, induction D with D d₀,
  --   induction f' with f' f'₀, induction f with f f₀, induction g with g g₀,
  --   esimp at *, induction f'₀, induction f₀, induction g₀,
  --   refine !dsmash_functor_phomotopy_refl ⬝ph** _, refine _ ⬝ !refl_trans⁻¹,
  --   fapply phomotopy_eq,
  --   { intro x, refine eq_of_square _ ⬝ !con_idp,
  --     exact dsmash_functor_pcompose_pconst4_homotopy a₀ b₀ d₀ f' f g x, },
  --   { refine _ ⬝ !idp_con⁻¹,
  --     refine whisker_right _ (!whisker_right_idp ⬝ !eq_of_square_hrfl_hconcat_eq) ⬝ _,
  --     refine !con.assoc ⬝ _, apply con_eq_of_eq_inv_con,
  --     refine whisker_right _ _ ⬝ _, rotate 1, rexact functor_gluel'2_same f' g (f a₀),
  --     refine !inv_con_cancel_right ⬝ _,
  --     refine !whisker_left_idp⁻¹ ⬝ _,
  --     refine !con_idp ⬝ _,
  --     apply whisker_left,
  --     apply ap (whisker_left idp),
  --     exact (!idp_con ⬝ !idp_con ⬝ !whisker_right_idp ⬝ !idp_con)⁻¹ }
  -- end

  -- /- a version where the left maps are identities -/
  -- definition dsmash_functor_pcompose_pconst4_pid (g : D →* F) :
  --   phsquare (dsmash_functor_pid_pcompose A g (pconst B D))
  --            (dsmash_functor_pconst_right (pid A))
  --            (dsmash_functor_phomotopy phomotopy.rfl (pcompose_pconst g))
  --            (pwhisker_left (pid A ⋀→ g) (dsmash_functor_pconst_right (pid A)) ⬝*
  --              pcompose_pconst (pid A ⋀→ g)) :=
  -- (!dsmash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans) ⬝pv**
  -- dsmash_functor_pcompose_pconst4 (pid A) (pid A) g

  -- /- a small rewrite of the previous -/
  -- -- definition dsmash_functor_pid_pcompose_pconst' (g : D →* F) :
  -- --   pwhisker_left (pid A ⋀→ g) (dsmash_functor_pconst_right (pid A)) ⬝*
  -- --   pcompose_pconst (pid A ⋀→ g) =
  -- --   (dsmash_functor_pid_pcompose A g (pconst B D))⁻¹* ⬝*
  -- --   (dsmash_functor_phomotopy phomotopy.rfl (pcompose_pconst g) ⬝*
  -- --   dsmash_functor_pconst_right (pid A)) :=
  -- -- begin
  -- --   apply eq_symm_trans_of_trans_eq,
  -- --   exact dsmash_functor_pid_pcompose_pconst g
  -- -- end

  -- /- if g' is constant -/
  -- definition dsmash_functor_pcompose_pconst3_homotopy [unfold 13] {A B C D E F : Type}
  --   (a₀ : A) (b₀ : B) (x₀ : F) (f' : C → E) (f : A → C) (g : B → D)
  --   (x : pointed.MK A a₀ ∧ pointed.MK B b₀) :
  --   square (dsmash_functor_pcompose_homotopy f' f (λ a, x₀) g x)
  --   idp
  --   (dsmash_functor_pconst_right_homotopy (λ a, f' (f a)) x)
  --   (dsmash_functor_pconst_right_homotopy f'
  --     (dsmash_functor (pmap_of_map f a₀) (pmap_of_map g b₀) x)) :=
  -- begin
  --   induction x with a b a b,
  --   { exact hrfl },
  --   { exact hrfl },
  --   { exact hrfl },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluel ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluel ⬝p2 _ ⬝2p
  --       (natural_square_compose (dsmash_functor_pconst_right_homotopy f') _ _)⁻¹ᵖ,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (natural_square_eq2 _ !functor_gluel2)⁻¹ᵖ,
  --     apply whisker021,
  --     refine _ ⬝1p ap hdeg_square (eq_of_square (!ap_constant_compose⁻¹ʰ) ⬝ !idp_con)⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝2p !rec_eq_gluel⁻¹, apply whisker021,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
  --     exact rfl2 end end },
  --   { exact abstract begin apply square_pathover,
  --     refine !rec_eq_gluer ⬝p1 _ ⬝1p !natural_square_refl⁻¹,
  --     refine !rec_eq_gluer ⬝p2 _ ⬝2p
  --       (natural_square_compose (dsmash_functor_pconst_right_homotopy f') _ _)⁻¹ᵖ,
  --     apply whisker001, apply whisker021,
  --     apply move201, refine _ ⬝1p !eq_hconcat_hdeg_square⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine ap (hconcat_eq _) !ap_inv ⬝p1 _ ⬝2p (natural_square_eq2 _ !functor_gluer2)⁻¹ᵖ,
  --     apply whisker021,
  --     refine _ ⬝1p ap hdeg_square (eq_of_square (!ap_constant_compose⁻¹ʰ) ⬝ !idp_con)⁻¹,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝2p !rec_eq_gluer⁻¹, apply whisker021,
  --     apply move221, refine _ ⬝1p !hdeg_square_hconcat_eq⁻¹,
  --     refine _ ⬝1p ap hdeg_square (eq_bot_of_square (transpose !ap02_constant)),
  --     exact rfl2 end end },
  -- end

  -- definition dsmash_functor_pcompose_pconst3 (f' : C →* E) (f : A →* C) (g : Πa, B a →* D (f a)) :
  --   phsquare (dsmash_functor_pcompose f' f (pconst D F) g)
  --            (dsmash_functor_pconst_right (f' ∘* f))
  --            (dsmash_functor_phomotopy phomotopy.rfl (pconst_pcompose g))
  --            (pwhisker_right (f ⋀→ g) (dsmash_functor_pconst_right f') ⬝*
  --              pconst_pcompose (f ⋀→ g)) :=
  -- begin
  --   induction A with A a₀, induction B with B b₀,
  --   induction E with E e₀, induction C with C c₀, induction F with F x₀, induction D with D d₀,
  --   induction f' with f' f'₀, induction f with f f₀, induction g with g g₀,
  --   esimp at *, induction f'₀, induction f₀, induction g₀,
  --   refine !dsmash_functor_phomotopy_refl ⬝ph** _, refine _ ⬝ !refl_trans⁻¹,
  --   fapply phomotopy_eq,
  --   { intro x, refine eq_of_square (dsmash_functor_pcompose_pconst3_homotopy a₀ b₀ x₀ f' f g x) },
  --   { refine whisker_right _ (!whisker_right_idp ⬝ !eq_of_square_hrfl) ⬝ _,
  --     have H : Π{A : Type} {a a' : A} (p : a = a'),
  --              idp_con (p ⬝ p⁻¹) ⬝ con.right_inv p = idp ⬝
  --              whisker_left idp (idp ⬝ (idp ⬝ proof whisker_right idp (idp_con (p ⬝ p⁻¹ᵖ))⁻¹ᵖ qed ⬝
  --                whisker_left idp (con.right_inv p))), by intros; induction p; reflexivity,
  --     rexact H (gluel (f' (f a₀))) }
  -- end

  -- /- a version where the left maps are identities -/
  -- definition dsmash_functor_pcompose_pconst3_pid (g : Πa, B a →* D (f a)) :
  --   phsquare (dsmash_functor_pid_pcompose A (pconst D F) g)
  --            (dsmash_functor_pconst_right (pid A))
  --            (dsmash_functor_phomotopy phomotopy.rfl (pconst_pcompose g))
  --            (pwhisker_right (pid A ⋀→ g) (dsmash_functor_pconst_right (pid A)) ⬝*
  --              pconst_pcompose (pid A ⋀→ g)) :=
  -- (!dsmash_functor_phomotopy_refl ◾** idp ⬝ !refl_trans) ⬝pv**
  -- dsmash_functor_pcompose_pconst3 (pid A) (pid A) g

  -- /- Using these lemmas we show that dsmash_functor_right is natural in all arguments -/
  -- definition dsmash_functor_right_natural_right (A B : Type*) (f : C →* C') :
  --   psquare (dsmash_functor_right A B C) (dsmash_functor_right A B C')
  --           (ppcompose_left f) (ppcompose_left (pid A ⋀→ f)) :=
  -- begin
  --   refine _⁻¹*,
  --   fapply phomotopy_mk_ppmap,
  --   { exact dsmash_functor_pid_pcompose A f },
  --   { refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !dsmash_functor_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
  --     apply dsmash_functor_pcompose_pconst4_pid }
  -- end

  -- definition dsmash_functor_right_natural_middle (A C : Type*) (f : B' →* B) :
  --   psquare (dsmash_functor_right A B C) (dsmash_functor_right A B' C)
  --           (ppcompose_right f) (ppcompose_right (pid A ⋀→ f)) :=
  -- begin
  --   refine _⁻¹*,
  --   fapply phomotopy_mk_ppmap,
  --   { intro g, exact dsmash_functor_pid_pcompose A g f },
  --   { refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !dsmash_functor_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
  --     apply dsmash_functor_pcompose_pconst3_pid }
  -- end

  -- definition dsmash_functor_right_natural_left (B C : Type*) (f : A →* A') :
  --   psquare (dsmash_functor_right A B C) (ppcompose_right (f ⋀→ (pid B)))
  --           (dsmash_functor_right A' B C) (ppcompose_left (f ⋀→ (pid C))) :=
  -- begin
  --   refine _⁻¹*,
  --   fapply phomotopy_mk_ppmap,
  --   { intro g, exact dsmash_functor_psquare proof phomotopy.rfl qed proof phomotopy.rfl qed },
  --   { esimp,
  --     refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
  --     apply eq_of_phsquare,
  --     refine (phmove_bot_of_left _ !dsmash_functor_pcompose_pconst3⁻¹ʰ**) ⬝h**
  --       (!dsmash_functor_phomotopy_refl ⬝pv** !phhrfl) ⬝h** !dsmash_functor_pcompose_pconst4 ⬝vp** _,
  --     refine !trans_assoc ⬝ !trans_assoc ⬝ idp ◾** _ ⬝ !trans_refl,
  --     refine idp ◾** !refl_trans ⬝ !trans_left_inv }
  -- end

  -- /- ⋀ B ≃* pcofiber (pprod_of_wedge A B) -/

  -- variables (A B)
  -- open pushout

  -- definition dsmash_equiv_cofiber : ⋀ B ≃ cofiber (@prod_of_wedge A B) :=
  -- begin
  --   unfold [dsmash, cofiber, dsmash'], symmetry,
  --   fapply pushout_vcompose_equiv wedge_of_sum,
  --   { symmetry, refine equiv_unit_of_is_contr _ _, apply is_contr_pushout_wedge_of_sum },
  --   { intro x, reflexivity },
  --   { apply prod_of_wedge_of_sum }
  -- end

  -- definition dsmash_punit_pequiv [constructor] : dsmash A punit ≃* punit :=
  -- begin
  --   apply pequiv_punit_of_is_contr,
  --   apply is_contr.mk (dsmash.mk pt ⋆), intro x,
  --   induction x,
  --   { induction b, exact gluel' pt a },
  --   { exact gluel pt },
  --   { exact gluer pt },
  --   { apply eq_pathover_constant_left_id_right, apply square_of_eq_top,
  --     exact whisker_right _ !idp_con⁻¹ },
  --   { apply eq_pathover_constant_left_id_right, induction b,
  --     refine !con.right_inv ⬝pv _, exact square_of_eq idp },
  -- end

  -- definition pprod_of_wedge [constructor] : wedge A B →* A ×* B :=
  -- begin
  --   fconstructor,
  --   { exact prod_of_wedge },
  --   { reflexivity }
  -- end

  -- definition dsmash_pequiv_pcofiber [constructor] : ⋀ B ≃* pcofiber (pprod_of_wedge A B) :=
  -- begin
  --   apply pequiv_of_equiv (dsmash_equiv_cofiber A B),
  --   exact cofiber.glue pt
  -- end

  -- variables {A B}

  -- /- commutativity -/

  -- definition dsmash_flip' [unfold 3] (x : ⋀ B) : dsmash B A :=
  -- begin
  --   induction x,
  --   { exact dsmash.mk b a },
  --   { exact auxr },
  --   { exact auxl },
  --   { exact gluer a },
  --   { exact gluel b }
  -- end

  -- definition dsmash_flip_dsmash_flip' [unfold 3] (x : ⋀ B) : dsmash_flip' (dsmash_flip' x) = x :=
  -- begin
  --   induction x,
  --   { reflexivity },
  --   { reflexivity },
  --   { reflexivity },
  --   { apply eq_pathover_id_right,
  --     refine ap_compose dsmash_flip' _ _ ⬝ ap02 _ !elim_gluel ⬝ !elim_gluer ⬝ph _,
  --     apply hrfl },
  --   { apply eq_pathover_id_right,
  --     refine ap_compose dsmash_flip' _ _ ⬝ ap02 _ !elim_gluer ⬝ !elim_gluel ⬝ph _,
  --     apply hrfl }
  -- end

  -- variables (A B)

  -- definition dsmash_flip [constructor] : ⋀ B →* dsmash B A :=
  -- pmap.mk dsmash_flip' idp

  -- definition dsmash_flip_dsmash_flip [constructor] :
  --   dsmash_flip B A ∘* dsmash_flip A B ~* pid (⋀ B) :=
  -- phomotopy.mk dsmash_flip_dsmash_flip' idp

  -- definition dsmash_comm [constructor] : ⋀ B ≃* dsmash B A :=
  -- begin
  --   apply pequiv.MK, do 2 apply dsmash_flip_dsmash_flip
  -- end

  -- variables {A B}
  -- definition dsmash_flip_dsmash_functor' [unfold 7] (f : A →* C) (g : Πa, B a →* D (f a)) : hsquare
  --   dsmash_flip' dsmash_flip' (dsmash_functor' f g) (dsmash_functor' g f) :=
  -- begin
  --   intro x, induction x,
  --   { reflexivity },
  --   { reflexivity },
  --   { reflexivity },
  --   { apply eq_pathover,
  --     refine ap_compose (dsmash_functor' _ _)  _ _ ⬝ ap02 _ !elim_gluel ⬝ !functor_gluer ⬝ph _
  --       ⬝hp (ap_compose dsmash_flip' _ _ ⬝ ap02 _ !functor_gluel)⁻¹ᵖ,
  --     refine _ ⬝hp (!ap_con ⬝ !ap_compose' ◾ !elim_gluel)⁻¹, exact hrfl },
  --   { apply eq_pathover,
  --     refine ap_compose (dsmash_functor' _ _)  _ _ ⬝ ap02 _ !elim_gluer ⬝ !functor_gluel ⬝ph _
  --       ⬝hp (ap_compose dsmash_flip' _ _ ⬝ ap02 _ !functor_gluer)⁻¹ᵖ,
  --     refine _ ⬝hp (!ap_con ⬝ !ap_compose' ◾ !elim_gluer)⁻¹, exact hrfl },
  -- end

  -- definition dsmash_flip_dsmash_functor (f : A →* C) (g : Πa, B a →* D (f a)) :
  --   psquare (dsmash_flip A B) (dsmash_flip C D) (f ⋀→ g) (g ⋀→ f) :=
  -- begin
  --   apply phomotopy.mk (dsmash_flip_dsmash_functor' f g), refine !idp_con ⬝ _ ⬝ !idp_con⁻¹,
  --   refine !ap_ap011 ⬝ _, apply ap011_flip,
  -- end

  definition pinr [constructor] (B : A → Type*) (a : A) : B a →* ⋀ B :=
  begin
    fapply pmap.mk,
    { intro b, exact dsmash.mk a b },
    { exact gluel' a pt }
  end

  definition pinl [constructor] (b : Πa, B a) : A →* ⋀ B :=
  begin
    fapply pmap.mk,
    { intro a, exact dsmash.mk a (b a) },
    { exact gluer' (b pt) pt }
  end

  -- definition pinr_phomotopy {a a' : A} (p : a = a') : pinr B a ~* pinr B a' :=
  -- begin
  --   fapply phomotopy.mk,
  --   { exact ap010 (pmap.to_fun ∘ pinr B) p },
  --   { induction p, apply idp_con }
  -- end

  definition dsmash_pmap_unit_pt [constructor] (B : A → Type*) : pinr B pt ~* pconst (B pt) (⋀ B) :=
  begin
    fapply phomotopy.mk,
    { intro b, exact gluer' b pt },
    { rexact con.right_inv (gluer pt) ⬝ (con.right_inv (gluel pt))⁻¹ }
  end

  definition dsmash_pmap_unit [constructor] (B : A → Type*) : Π*(a : A), B a →** ⋀ B :=
  begin
    fapply ppi.mk,
    { exact pinr B },
    { apply eq_of_phomotopy, exact dsmash_pmap_unit_pt B }
  end

  /- The unit is natural in the first argument -/
  definition dsmash_functor_pid_pinr' [constructor] (B : A' → Type*) (f : A →* A') (a : A) :
    pinr B (f a) ~* (f ⋀→ λa, !pid) ∘* pinr (B ∘ f) a :=
  begin
    fapply phomotopy.mk,
    { intro b, reflexivity },
    { refine !idp_con ⬝ _,
      induction A' with A' a₀', induction f with f f₀, esimp at *,
      induction f₀, exact sorry }
  end

  -- definition dsmash_pmap_unit_pt_natural [constructor] (B : A → Type*) (f : A →* A') :
  --   dsmash_functor_pid_pinr' B f pt ⬝*
  --   pwhisker_left (f ⋀→ λa, !pid) (dsmash_pmap_unit_pt A B) ⬝*
  --   pcompose_pconst (f ⋀→ λa, !pid) =
  --   _ /-pinr_phomotopy (respect_pt f)-/ ⬝* dsmash_pmap_unit_pt A' B :=
  -- begin
  --   induction f with f f₀, induction A' with A' a₀', esimp at *,
  --   induction f₀, refine _ ⬝ !refl_trans⁻¹,
  --   refine !trans_refl ⬝ _,
  --   fapply phomotopy_eq',
  --   { intro b, refine !idp_con ⬝ _,
  --     rexact functor_gluer'2 f (pid B) b pt },
  --   { refine whisker_right_idp _ ⬝ph _,
  --     refine ap (λx, _ ⬝ x) _ ⬝ph _,
  --     rotate 1, rexact (functor_gluer'2_same f (pid B) pt),
  --     refine whisker_right _ !idp_con ⬝pv _,
  --     refine !con.assoc⁻¹ ⬝ph _, apply whisker_bl,
  --     refine whisker_left _ !to_homotopy_pt_mk ⬝pv _,
  --     refine !con.assoc⁻¹ ⬝ whisker_right _ _ ⬝pv _,
  --     rotate 1, esimp, apply whisker_left_idp_con,
  --     refine !con.assoc ⬝pv _, apply whisker_tl,
  --     refine whisker_right _ !idp_con ⬝pv _,
  --     refine whisker_right _ !whisker_right_idp ⬝pv _,
  --     refine whisker_right _ (!idp_con ⬝ !ap02_con) ⬝ !con.assoc ⬝pv _,
  --     apply whisker_tl,
  --     apply vdeg_square,
  --     refine whisker_right _ !ap_inv ⬝ _, apply inv_con_eq_of_eq_con,
  --     rexact functor_gluel'2_same (pmap_of_map f pt) (pmap_of_map id (Point B)) pt }
  -- end

  -- definition dsmash_pmap_unit_natural (B : A' → Type*) (f : A →* A') :
  --   psquare (dsmash_pmap_unit (B ∘ f)) (dsmash_pmap_unit B) f _ := --(ppcompose_left (f ⋀→ pid B))
  -- begin
  --   apply ptranspose,
  --   induction A with A a₀, induction B with B b₀, induction A' with A' a₀',
  --   induction f with f f₀, esimp at *, induction f₀, fapply phomotopy_mk_ppmap,
  --   { intro a, exact dsmash_functor_pid_pinr' _ (pmap_of_map f a₀) a },
  --   { refine ap (λx, _ ⬝* phomotopy_of_eq x) !respect_pt_pcompose ⬝ _
  --          ⬝ ap phomotopy_of_eq !respect_pt_pcompose⁻¹,
  --     esimp, refine _ ⬝ ap phomotopy_of_eq !idp_con⁻¹,
  --     refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
  --     refine ap (λx, _ ⬝* phomotopy_of_eq (x ⬝ _)) !pcompose_left_eq_of_phomotopy ⬝ _,
  --     refine ap (λx, _ ⬝* x) (!phomotopy_of_eq_con ⬝
  --              !phomotopy_of_eq_of_phomotopy ◾** !phomotopy_of_eq_of_phomotopy ⬝ !trans_refl) ⬝ _,
  --     refine _ ⬝ dsmash_pmap_unit_pt_natural _ (pmap_of_map f a₀) ⬝ _,
  --     { exact !trans_refl⁻¹ },
  --     { exact !refl_trans }}
  -- end


  /- The unit is also dinatural in the first argument, but that's easier to prove after the adjunction.
     We don't need it for the adjunction -/

  /- The unit-counit laws -/
  -- definition dsmash_pmap_unit_counit (B : A → Type*) :
  --   dsmash_pmap_counit B (⋀ B) ∘* dsmash_pmap_unit A B ⋀→ pid B ~* pid (⋀ B) :=
  -- begin
  --   fapply phomotopy.mk,
  --   { intro x,
  --     induction x with a b a b,
  --     { reflexivity },
  --     { exact gluel pt },
  --     { exact gluer pt },
  --     { apply eq_pathover_id_right,
  --       refine ap_compose dsmash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluel ⬝ph _,
  --       refine !ap_con ⬝ !ap_compose' ◾ !elim_gluel ⬝ph _,
  --       refine !idp_con ⬝ph _,
  --       apply square_of_eq, refine !idp_con ⬝ !inv_con_cancel_right⁻¹ },
  --     { apply eq_pathover_id_right,
  --       refine ap_compose dsmash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluer ⬝ph _,
  --       refine !ap_con ⬝ !ap_compose' ◾ !elim_gluer ⬝ph _,
  --       refine !ap_eq_of_phomotopy ⬝ph _,
  --       apply square_of_eq, refine !idp_con ⬝ !inv_con_cancel_right⁻¹ }},
  --   { refine _ ⬝ !ap_compose, refine _ ⬝ (ap_is_constant respect_pt _)⁻¹,
  --        rexact (con.right_inv (gluel pt))⁻¹ }
  -- end

  -- definition dsmash_pmap_counit_unit_pt [constructor] (f : A →* B) :
  --   dsmash_pmap_counit A B ∘* pinr A f ~* f :=
  -- begin
  --   fapply phomotopy.mk,
  --   { intro a, reflexivity },
  --   { refine !idp_con ⬝ !elim_gluel'⁻¹ }
  -- end

  -- definition dsmash_pmap_counit_unit (B : A → Type*) :
  --   ppcompose_left (dsmash_pmap_counit A B) ∘* dsmash_pmap_unit (ppmap A B) A ~* pid (ppmap A B) :=
  -- begin
  --   fapply phomotopy_mk_ppmap,
  --   { intro f, exact dsmash_pmap_counit_unit_pt f },
  --   { refine !trans_refl ⬝ _,
  --     refine _ ⬝ ap (λx, phomotopy_of_eq (x ⬝ _)) !pcompose_left_eq_of_phomotopy⁻¹,
  --     refine _ ⬝ !phomotopy_of_eq_con⁻¹,
  --     refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹ ◾** !phomotopy_of_eq_of_phomotopy⁻¹,
  --     refine _ ⬝ !trans_refl⁻¹,
  --     fapply phomotopy_eq,
  --     { intro a, esimp, refine !elim_gluer'⁻¹ },
  --     { esimp, refine whisker_right _ !whisker_right_idp ⬝ _ ⬝ !idp_con⁻¹,
  --       refine whisker_right _ !elim_gluer'_same⁻² ⬝ _ ⬝ !elim_gluel'_same⁻¹⁻²,
  --       apply inv_con_eq_of_eq_con, refine !idp_con ⬝ _, esimp,
  --       refine _ ⬝ !ap02_con ⬝ whisker_left _ !ap_inv,
  --       refine !whisker_right_idp ⬝ _,
  --       exact !idp_con }}
  -- end

  /- The underlying (unpointed) functions of the equivalence A →* (B →* C) ≃* ⋀ B →* C) -/
  -- definition dsmash_elim [constructor] (f : Π*(a : A), ppmap (B a) C) : ⋀ B →* C :=
  -- smash.smash_pmap_counit _ C ∘* _ /-f ⋀→ pid B_-/

  -- definition dsmash_elim_inv [constructor] (g : ⋀ B →* C) : A →* ppmap B C :=
  -- ppcompose_left g ∘* dsmash_pmap_unit A B

  -- /- They are inverses, constant on the constant function and natural -/
  -- definition dsmash_elim_left_inv (f : A →* ppmap B C) : dsmash_elim_inv (dsmash_elim f) ~* f :=
  -- begin
  --   refine !pwhisker_right !ppcompose_left_pcompose ⬝* _,
  --   refine !passoc ⬝* _,
  --   refine !pwhisker_left !dsmash_pmap_unit_natural ⬝* _,
  --   refine !passoc⁻¹* ⬝* _,
  --   refine !pwhisker_right !dsmash_pmap_counit_unit ⬝* _,
  --   apply pid_pcompose
  -- end

  -- definition dsmash_elim_right_inv (g : ⋀ B →* C) : dsmash_elim (dsmash_elim_inv g) ~* g :=
  -- begin
  --   refine !pwhisker_left !dsmash_functor_pcompose_pid ⬝* _,
  --   refine !passoc⁻¹* ⬝* _,
  --   refine !pwhisker_right !dsmash_pmap_counit_natural_right⁻¹* ⬝* _,
  --   refine !passoc ⬝* _,
  --   refine !pwhisker_left !dsmash_pmap_unit_counit ⬝* _,
  --   apply pcompose_pid
  -- end

  -- definition dsmash_elim_pconst (B : A → Type*) (C : Type*) :
  --   dsmash_elim (pconst A (ppmap B C)) ~* pconst (⋀ B) C :=
  -- begin
  --   refine pwhisker_left _ (dsmash_functor_pconst_left (pid B)) ⬝* !pcompose_pconst
  -- end

  -- definition dsmash_elim_inv_pconst (B : A → Type*) (C : Type*) :
  --   dsmash_elim_inv (pconst (⋀ B) C) ~* pconst A (ppmap B C) :=
  -- begin
  --   fapply phomotopy_mk_ppmap,
  --   { intro f, apply pconst_pcompose },
  --   { esimp, refine !trans_refl ⬝ _,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
  --       !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
  --     apply pconst_pcompose_phomotopy_pconst }
  -- end

  -- definition dsmash_elim_natural_right (f : C →* C') (g : A →* ppmap B C) :
  --   f ∘* dsmash_elim g ~* dsmash_elim (ppcompose_left f ∘* g) :=
  -- begin
  --   refine _ ⬝* pwhisker_left _ !dsmash_functor_pcompose_pid⁻¹*,
  --   refine !passoc⁻¹* ⬝* pwhisker_right _ _ ⬝* !passoc,
  --   apply dsmash_pmap_counit_natural_right
  -- end

  -- definition dsmash_elim_inv_natural_right {A B C C' : Type*} (f : C →* C')
  --   (g : ⋀ B →* C) : ppcompose_left f ∘* dsmash_elim_inv g ~* dsmash_elim_inv (f ∘* g) :=
  -- begin
  --   refine !passoc⁻¹* ⬝* pwhisker_right _ _,
  --   exact !ppcompose_left_pcompose⁻¹*
  -- end

  -- definition dsmash_elim_natural_left (f : A →* A') (g : B →* B') (h : A' →* ppmap B' C) :
  --   dsmash_elim h ∘* (f ⋀→ g) ~* dsmash_elim (ppcompose_right g ∘* h ∘* f) :=
  -- begin
  --   refine !dsmash_functor_pcompose_pid ⬝ph* _,
  --   refine _ ⬝v* !dsmash_pmap_counit_natural_left,
  --   refine dsmash_functor_psquare !pid_pcompose⁻¹* (phrefl g)
  -- end

  -- definition dsmash_elim_phomotopy {f f' : A →* ppmap B C} (p : f ~* f') :
  --   dsmash_elim f ~* dsmash_elim f' :=
  -- begin
  --   apply pwhisker_left,
  --   exact dsmash_functor_phomotopy p phomotopy.rfl
  -- end

  -- definition dsmash_elim_inv_phomotopy {f f' : ⋀ B →* C} (p : f ~* f') :
  --   dsmash_elim_inv f ~* dsmash_elim_inv f' :=
  -- pwhisker_right _ (ppcompose_left_phomotopy p)

  -- definition dsmash_elim_eq_of_phomotopy {f f' : A →* ppmap B C} (p : f ~* f') :
  --   ap dsmash_elim (eq_of_phomotopy p) = eq_of_phomotopy (dsmash_elim_phomotopy p) :=
  -- begin
  --   induction p using phomotopy_rec_idp,
  --   refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
  --   refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
  --   apply ap eq_of_phomotopy,
  --   refine _ ⬝ ap (pwhisker_left _) !dsmash_functor_phomotopy_refl⁻¹,
  --   refine !pwhisker_left_refl⁻¹
  -- end

  -- definition dsmash_elim_inv_eq_of_phomotopy {f f' : ⋀ B →* C} (p : f ~* f') :
  --   ap dsmash_elim_inv (eq_of_phomotopy p) = eq_of_phomotopy (dsmash_elim_inv_phomotopy p) :=
  -- begin
  --   induction p using phomotopy_rec_idp,
  --   refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
  --   refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
  --   apply ap eq_of_phomotopy,
  --   refine _ ⬝ ap (pwhisker_right _) !ppcompose_left_phomotopy_refl⁻¹,
  --   refine !pwhisker_right_refl⁻¹
  -- end

  /- The pointed maps of the equivalence A →* (B →* C) ≃* ⋀ B →* C -/
--   definition dsmash_pelim : (Π*(a : A), ppmap (B a) C) →* ppmap (⋀ B) C :=
--   ppcompose_left (smash.smash_pmap_counit (B pt) C) ∘* sorry
-- --  ppcompose_left (smash_pmap_counit B C) ∘* dsmash_functor_left A (ppmap B C) B

--   open smash
--   definition smash_pelim_inv (B : A → Type*) (C : Type*) :
--     ppmap (A ∧ B) C →* ppmap A (ppmap B C) :=
--   ppcompose_right (smash_pmap_unit A B) ∘* pppcompose B (A ∧ B) C

--   -- definition smash_pelim_inv : ppmap (⋀ B) C →* Π*a, ppmap (B a) C :=
--   -- _ ∘* pppcompose _ (⋀ B) C --ppcompose_right (smash_pmap_unit A B) ∘* pppcompose B (A ∧ B) C

--   /- The forward function is natural in all three arguments -/
--   definition dsmash_pelim_natural_left (B C : Type*) (f : A' →* A) :
--     psquare (dsmash_pelim A B C) (dsmash_pelim A' B C)
--             (ppcompose_right f) (ppcompose_right (f ⋀→ pid B)) :=
--   dsmash_functor_left_natural_left (ppmap B C) B f ⬝h* !ppcompose_left_ppcompose_right

--   definition dsmash_pelim_natural_middle (A C : Type*) (f : B' →* B) :
--     psquare (dsmash_pelim A B C) (dsmash_pelim A B' C)
--             (ppcompose_left (ppcompose_right f)) (ppcompose_right (pid A ⋀→ f)) :=
--   pwhisker_tl _ !ppcompose_left_ppcompose_right ⬝*
--   (!dsmash_functor_left_natural_right⁻¹* ⬝pv*
--   dsmash_functor_left_natural_middle _ _ (ppcompose_right f) ⬝h*
--   ppcompose_left_psquare !dsmash_pmap_counit_natural_left)

--   definition dsmash_pelim_natural_right (B : A → Type*) (f : C →* C') :
--     psquare (dsmash_pelim A B C) (dsmash_pelim A B C')
--             (ppcompose_left (ppcompose_left f)) (ppcompose_left f) :=
--   dsmash_functor_left_natural_middle _ _ (ppcompose_left f) ⬝h*
--   ppcompose_left_psquare (dsmash_pmap_counit_natural_right _ f)

--   definition dsmash_pelim_natural_lm (C : Type*) (f : A' →* A) (g : B' →* B) :
--     psquare (dsmash_pelim A B C) (dsmash_pelim A' B' C)
--             (ppcompose_left (ppcompose_right g) ∘* ppcompose_right f) (ppcompose_right (f ⋀→ g)) :=
--   dsmash_pelim_natural_left B C f ⬝v* dsmash_pelim_natural_middle A' C g ⬝hp*
--   ppcompose_right_phomotopy (dsmash_functor_split f g) ⬝* !ppcompose_right_pcompose

--   definition dsmash_pelim_pid (B C : Type*) :
--     dsmash_pelim (ppmap B C) B C !pid ~* dsmash_pmap_counit B C :=
--   pwhisker_left _ !dsmash_functor_pid ⬝* !pcompose_pid

--   definition dsmash_pelim_inv_pid (B : A → Type*) :
--     dsmash_pelim_inv A B (⋀ B) !pid ~* dsmash_pmap_unit A B :=
--   pwhisker_right _ !ppcompose_left_pid ⬝* !pid_pcompose

--   /- The equivalence (note: the forward function of dsmash_adjoint_pmap is dsmash_pelim_inv) -/
--   definition is_equiv_dsmash_elim [constructor] (B : A → Type*) (C : Type*) : is_equiv (@dsmash_elim A B C) :=
--   begin
--     fapply adjointify,
--     { exact dsmash_elim_inv },
--     { intro g, apply eq_of_phomotopy, exact dsmash_elim_right_inv g },
--     { intro f, apply eq_of_phomotopy, exact dsmash_elim_left_inv f }
--   end

--   definition dsmash_adjoint_pmap_inv [constructor] (B : A → Type*) (C : Type*) :
--     ppmap A (ppmap B C) ≃* ppmap (⋀ B) C :=
--   pequiv_of_pmap (dsmash_pelim A B C) (is_equiv_dsmash_elim A B C)

  definition dsmash_pelim_fn_fn [constructor] (f : ⋀ B →* C) (a : A) : B a →* C :=
  pmap.mk (λb, f (dsmash.mk a b)) (ap f (gluel' a pt) ⬝ respect_pt f)

  definition dsmash_pelim_fn [constructor] (f : ⋀ B →* C) : dbpmap B (λa, C) :=
  begin
    fapply dbpmap.mk (dsmash_pelim_fn_fn f),
    { intro b, exact ap f (gluer' b pt) ⬝ respect_pt f },
    { apply whisker_right, apply ap02, exact !con.right_inv ⬝ !con.right_inv⁻¹ }
  end

  definition dsmash_pelim_pmap [constructor] (B : A → Type*) (C : Type*) :
    ppmap (⋀ B) C →* dbppmap B (λa, C) :=
  begin
    apply pmap.mk dsmash_pelim_fn,
    fapply dbpmap_eq,
    { intro a, exact phomotopy.mk homotopy.rfl !ap_constant⁻¹ },
    { intro b, exact !ap_constant ⬝pv ids },
    { esimp, esimp [whisker_right], exact sorry }
  end

  definition dsmash_pelim_pequiv [constructor] (B : A → Type*) (C : Type*) :
    ppmap (⋀ B) C ≃* dbppmap B (λa, C) :=
  sorry

set_option pp.binder_types true
open is_trunc

  /- we could also use pushout_arrow_equiv -/
  definition dsmash_arrow_equiv [constructor] (B : A → Type*) (C : Type) :
    (⋀ B → C) ≃ Σ(f : Πa, B a → C) (c₁ : C) (c₀ : C), (Πa, f a pt = c₀) × (Πb, f pt b = c₁) :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λa b, f (dsmash.mk a b), f auxr, f auxl, (λa, ap f (gluel a), λb, ap f (gluer b))⟩ },
    { intro x, exact dsmash.elim x.1 x.2.2.1 x.2.1 x.2.2.2.1 x.2.2.2.2 },
    { intro x, induction x with f x, induction x with c₁ x, induction x with c₀ x, induction x with p₁ p₂,
      apply ap (dpair _), apply ap (dpair _), apply ap (dpair _), esimp,
      exact pair_eq (eq_of_homotopy (elim_gluel _ _)) (eq_of_homotopy (elim_gluer _ _)) },
    { intro f, apply eq_of_homotopy, intro x, induction x, reflexivity, reflexivity, reflexivity,
      apply eq_pathover, apply hdeg_square, apply elim_gluel,
      apply eq_pathover, apply hdeg_square, apply elim_gluer }
  end

  definition dsmash_arrow_equiv_inv_pt [constructor]
    (x : Σ(f : Πa, B a → C) (c₁ : C) (c₀ : C), (Πa, f a pt = c₀) × (Πb, f pt b = c₁)) :
    to_inv (dsmash_arrow_equiv B C) x pt = x.1 pt pt :=
  by reflexivity

  open pi

  definition dsmash_pelim_equiv (B : A → Type*) (C : Type*) :
    ppmap (⋀ B) C ≃ dbppmap B (λa, C) :=
  begin
    refine !pmap.sigma_char ⬝e _,
    refine sigma_equiv_sigma_left !dsmash_arrow_equiv ⬝e _,
    refine sigma_equiv_sigma_right (λx, equiv_eq_closed_left _ (dsmash_arrow_equiv_inv_pt x)) ⬝e _,
    refine !sigma_assoc_equiv ⬝e _,
    refine sigma_equiv_sigma_right (λf, !sigma_assoc_equiv ⬝e
      sigma_equiv_sigma_right (λc₁, !sigma_assoc_equiv ⬝e
        sigma_equiv_sigma_right (λc₂, sigma_equiv_sigma_left !sigma.equiv_prod⁻¹ᵉ ⬝e
          !sigma_assoc_equiv) ⬝e
        sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv pt (λa, f a pt))⁻¹ᵉ ⬝e
        sigma_equiv_sigma_right (λh₁, !sigma_comm_equiv) ⬝e !sigma_comm_equiv) ⬝e
      sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv pt (f pt))⁻¹ᵉ ⬝e
      sigma_equiv_sigma_right (λh₂,
        sigma_equiv_sigma_right (λr₂,
          sigma_equiv_sigma_right (λh₁, !comm_equiv_nondep) ⬝e !sigma_comm_equiv) ⬝e
        !sigma_comm_equiv) ⬝e
      !sigma_comm_equiv ⬝e
      sigma_equiv_sigma_right (λr,
        sigma_equiv_sigma_left (pi_equiv_pi_right (λb, equiv_eq_closed_right _ r)) ⬝e
        sigma_equiv_sigma_right (λh₂,
          sigma_equiv_sigma !eq_equiv_con_inv_eq_idp⁻¹ᵉ (λr₂,
            sigma_equiv_sigma_left (pi_equiv_pi_right (λa, equiv_eq_closed_right _ r)) ⬝e
            sigma_equiv_sigma_right (λh₁, !eq_equiv_con_inv_eq_idp⁻¹ᵉ)) ⬝e
          !sigma_comm_equiv ⬝e
          sigma_equiv_sigma_right (λh₁, !comm_equiv_nondep)) ⬝e
        !sigma_comm_equiv) ⬝e
      !sigma_comm_equiv ⬝e sigma_equiv_sigma_right (λh₁,
        !sigma_comm_equiv ⬝e sigma_equiv_sigma_right (λh₂,
          !sigma_sigma_eq_right))) ⬝e _,
    refine !sigma_assoc_equiv' ⬝e _,
    refine sigma_equiv_sigma_left (@sigma_pi_equiv_pi_sigma _ _ (λa f, f pt = pt) ⬝e
      pi_equiv_pi_right (λa, !pmap.sigma_char⁻¹ᵉ)) ⬝e _,
    exact !dbpmap.sigma_char⁻¹ᵉ
  end

  definition dsmash_pelim_equiv' (B : A → Type*) (C : Type*) :
    ppmap (⋀ B) C ≃ Π*a, B a →** C :=
  dsmash_pelim_equiv B C ⬝e (ppi_equiv_dbpmap B (λa, C))⁻¹ᵉ
exit
  definition dsmash_arrow_equiv2 [constructor] (B : A → Type*) (C : Type) :
    (⋀ B → C) ≃ Σ(f : Πa, B a → C) (c₀ : C) (p : Πa, f a pt = c₀) (q : Πb, f pt b = c₀), p pt = q pt :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λa b, f (dsmash.mk a b), f auxr, f auxl, (λa, ap f (gluel a), λb, ap f (gluer b))⟩ },
    { intro x, exact dsmash.elim x.1 x.2.2.1 x.2.1 x.2.2.2.1 x.2.2.2.2 },
    { intro x, induction x with f x, induction x with c₁ x, induction x with c₀ x, induction x with p₁ p₂,
      apply ap (dpair _), apply ap (dpair _), apply ap (dpair _), esimp,
      exact pair_eq (eq_of_homotopy (elim_gluel _ _)) (eq_of_homotopy (elim_gluer _ _)) },
    { intro f, apply eq_of_homotopy, intro x, induction x, reflexivity, reflexivity, reflexivity,
      apply eq_pathover, apply hdeg_square, apply elim_gluel,
      apply eq_pathover, apply hdeg_square, apply elim_gluer }
  end

  definition dsmash_arrow_equiv2_inv_pt [constructor]
    (x : Σ(f : Πa, B a → C) (c₁ : C) (c₀ : C), (Πa, f a pt = c₀) × (Πb, f pt b = c₁)) :
    to_inv (dsmash_arrow_equiv B C) x pt = x.1 pt pt :=
  by reflexivity

  open pi

  definition dsmash_pmap_equiv2 (B : A → Type*) (C : Type*) :
    (⋀ B →* C) ≃ dbppmap B (λa, C) :=
  begin
    refine !pmap.sigma_char ⬝e _,
    refine sigma_equiv_sigma_left !dsmash_arrow_equiv ⬝e _,
    refine sigma_equiv_sigma_right (λx, equiv_eq_closed_left _ (dsmash_arrow_equiv_inv_pt x)) ⬝e _,
    refine !sigma_assoc_equiv ⬝e _,
    refine sigma_equiv_sigma_right (λf, !sigma_assoc_equiv ⬝e
      sigma_equiv_sigma_right (λc₁, !sigma_assoc_equiv ⬝e
        sigma_equiv_sigma_right (λc₂, sigma_equiv_sigma_left !sigma.equiv_prod⁻¹ᵉ ⬝e
          !sigma_assoc_equiv) ⬝e
        sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv pt (λa, f a pt))⁻¹ᵉ ⬝e
        sigma_equiv_sigma_right (λh₁, !sigma_comm_equiv) ⬝e !sigma_comm_equiv) ⬝e
      sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv pt (f pt))⁻¹ᵉ ⬝e
      sigma_equiv_sigma_right (λh₂,
        sigma_equiv_sigma_right (λr₂,
          sigma_equiv_sigma_right (λh₁, !comm_equiv_nondep) ⬝e !sigma_comm_equiv) ⬝e
        !sigma_comm_equiv) ⬝e
      !sigma_comm_equiv ⬝e
      sigma_equiv_sigma_right (λr,
        sigma_equiv_sigma_left (pi_equiv_pi_right (λb, equiv_eq_closed_right _ r)) ⬝e
        sigma_equiv_sigma_right (λh₂,
          sigma_equiv_sigma !eq_equiv_con_inv_eq_idp⁻¹ᵉ (λr₂,
            sigma_equiv_sigma_left (pi_equiv_pi_right (λa, equiv_eq_closed_right _ r)) ⬝e
            sigma_equiv_sigma_right (λh₁, !eq_equiv_con_inv_eq_idp⁻¹ᵉ)) ⬝e
          !sigma_comm_equiv ⬝e
          sigma_equiv_sigma_right (λh₁, !comm_equiv_nondep)) ⬝e
        !sigma_comm_equiv) ⬝e
      !sigma_comm_equiv ⬝e sigma_equiv_sigma_right (λh₁,
        !sigma_comm_equiv ⬝e sigma_equiv_sigma_right (λh₂,
          !sigma_sigma_eq_right))) ⬝e _,
    refine !sigma_assoc_equiv' ⬝e _,
    refine sigma_equiv_sigma_left (@sigma_pi_equiv_pi_sigma _ _ (λa f, f pt = pt) ⬝e
      pi_equiv_pi_right (λa, !pmap.sigma_char⁻¹ᵉ)) ⬝e _,
    exact !dbpmap.sigma_char⁻¹ᵉ
  end

end dsmash
