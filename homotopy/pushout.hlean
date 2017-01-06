

import ..move_to_lib

open eq function is_trunc sigma prod lift is_equiv equiv pointed sum unit bool

namespace pushout

  universe variables u₁ u₂ u₃ u₄
  variables {A : Type.{u₁}} {B : Type.{u₂}} {C : Type.{u₃}} {D D' : Type.{u₄}}
            {f : A → B} {g : A → C} {h : B → D} {k : C → D} (p : h ∘ f ~ k ∘ g)
            {h' : B → D'} {k' : C → D'} (p' : h' ∘ f ~ k' ∘ g)
            -- (f : A → B) (g : A → C) (h : B → D) (k : C → D)

  include p
  definition is_pushout : Type :=
  Π⦃X : Type.{max u₁ u₂ u₃ u₄}⦄ (h' : B → X) (k' : C → X) (p' : h' ∘ f ~ k' ∘ g),
    is_contr (Σ(l : D → X) (v : l ∘ h ~ h' × l ∘ k ~ k'),
                 Πa, square (prod.pr1 v (f a)) (prod.pr2 v (g a)) (ap l (p a)) (p' a))

  definition cocone [reducible] (X : Type) : Type :=
  Σ(v : (B → X) × (C → X)), prod.pr1 v ∘ f ~ prod.pr2 v ∘ g

  definition cocone_of_map [constructor] (X : Type) (l : D → X) : cocone p X :=
  ⟨(l ∘ h, l ∘ k), λa, ap l (p a)⟩

  -- definition cocone_of_map (X : Type) (l : D → X) : Σ(h' : B → X) (k' : C → X),
  --   h' ∘ f ~ k' ∘ g :=
  -- ⟨l ∘ h, l ∘ k, λa, ap l (p a)⟩

  omit p

  definition is_pushout2 [reducible] : Type :=
  Π(X : Type.{max u₁ u₂ u₃ u₄}), is_equiv (cocone_of_map p X)

  section
  open sigma.ops
  protected definition inv_left (H : is_pushout2 p) {X : Type} (v : cocone p X) :
    (cocone_of_map p X)⁻¹ᶠ v ∘ h ~ prod.pr1 v.1 :=
  ap10 (ap prod.pr1 (right_inv (cocone_of_map p X) v)..1)

  protected definition inv_right (H : is_pushout2 p) {X : Type} (v : cocone p X) :
    (cocone_of_map p X)⁻¹ᶠ v ∘ k ~ prod.pr2 v.1 :=
  ap10 (ap prod.pr2 (right_inv (cocone_of_map p X) v)..1)
  end

  section
    local attribute is_pushout [reducible]
    definition is_prop_is_pushout : is_prop (is_pushout p) :=
    _

    local attribute is_pushout2 [reducible]
    definition is_prop_is_pushout2 : is_prop (is_pushout2 p) :=
    _
  end

  definition ap_eq_apd10_ap {A B : Type} {C : B → Type} (f : A → Πb, C b) {a a' : A} (p : a = a') (b : B)
    : ap (λa, f a b) p = apd10 (ap f p) b :=
  by induction p; reflexivity

  variables (f g)
  definition is_pushout2_pushout : @is_pushout2 _ _ _ _ f g inl inr glue :=
  λX, to_is_equiv (pushout_arrow_equiv f g X ⬝e assoc_equiv_prod _)

  definition is_equiv_of_is_pushout2_simple [constructor] {A B C D : Type.{u₁}}
            {f : A → B} {g : A → C} {h : B → D} {k : C → D} (p : h ∘ f ~ k ∘ g)
            {h' : B → D'} {k' : C → D'} (p' : h' ∘ f ~ k' ∘ g)
 (H : is_pushout2 p) : D ≃ pushout f g :=
  begin
    fapply equiv.MK,
    { exact (cocone_of_map p _)⁻¹ᶠ ⟨(inl, inr), glue⟩ },
    { exact pushout.elim h k p },
    { intro x, exact sorry

},
    { apply ap10,
      apply eq_of_fn_eq_fn (equiv.mk _ (H D)),
      fapply sigma_eq,
      { esimp, fapply prod_eq,
          apply eq_of_homotopy, intro b,
          exact ap (pushout.elim h k p) (pushout.inv_left p H ⟨(inl, inr), glue⟩ b),
          apply eq_of_homotopy, intro c,
          exact ap (pushout.elim h k p) (pushout.inv_right p H ⟨(inl, inr), glue⟩ c) },
      { apply pi.pi_pathover_constant, intro a,
        apply eq_pathover,
        refine !ap_eq_apd10_ap ⬝ph _ ⬝hp !ap_eq_apd10_ap⁻¹,
        refine ap (λx, apd10 x _) (ap_compose (λx, x ∘ f) pr1 _ ⬝ ap02 _ !prod_eq_pr1) ⬝ph _
               ⬝hp ap (λx, apd10 x _) (ap_compose (λx, x ∘ g) pr2 _ ⬝ ap02 _ !prod_eq_pr2)⁻¹,
        refine apd10 !apd10_ap_precompose_dependent a ⬝ph _ ⬝hp apd10 !apd10_ap_precompose_dependent⁻¹ a,
        refine apd10 !apd10_eq_of_homotopy (f a) ⬝ph _ ⬝hp apd10 !apd10_eq_of_homotopy⁻¹ (g a),
        refine ap_compose (pushout.elim h k p) _ _ ⬝pv _,
        refine aps (pushout.elim h k p) _ ⬝vp (!elim_glue ⬝ !ap_id⁻¹),
        esimp,   exact sorry
        },
      }
  end


--   definition is_equiv_of_is_pushout2 [constructor] (H : is_pushout2 p) : D ≃ pushout f g :=
--   begin
--     fapply equiv.MK,
--     { exact down.{_ u₄} ∘ (cocone_of_map p _)⁻¹ᶠ ⟨(up ∘ inl, up ∘ inr), λa, ap up (glue a)⟩ },
--     { exact pushout.elim h k p },
--     { intro x, exact sorry

-- },
--     { intro d, apply eq_of_fn_eq_fn (equiv_lift D), esimp, revert d,
--       apply ap10,
--       apply eq_of_fn_eq_fn (equiv.mk _ (H (lift.{_ (max u₁ u₂ u₃)} D))),
--       fapply sigma_eq,
--       { esimp, fapply prod_eq,
--           apply eq_of_homotopy, intro b, apply ap up, esimp,
--         exact ap (pushout.elim h k p ∘ down.{_ u₄})
--                    (pushout.inv_left p H ⟨(up ∘ inl, up ∘ inr), λa, ap up (glue a)⟩ b),

--         exact sorry },
--       { exact sorry },

--       -- note q := @eq_of_is_contr _ H''
--       --   ⟨up ∘ pushout.elim h k p ∘ down ∘ (center' H').1,
--       --    (λb, ap (up ∘ pushout.elim h k p ∘ down) (prod.pr1 (center' H').2 b),
--       --     λc, ap (up ∘ pushout.elim h k p ∘ down) (prod.pr2 (center' H').2 c))⟩
--       --   ⟨up, (λx, idp, λx, idp)⟩,
--       -- exact ap down (ap10 q..1 d)
--       }
--   end

  definition pushout_vcompose_to [unfold 8] {A B C D : Type} {f : A → B} {g : A → C} {h : B → D}
    (x : pushout h (@inl _ _ _ f g)) : pushout (h ∘ f) g :=
  begin
    induction x with d y b,
    { exact inl d },
    { induction y with b c a,
      { exact inl (h b) },
      { exact inr c },
      { exact glue a }},
    { reflexivity }
  end

  definition pushout_vcompose_from [unfold 8] {A B C D : Type} {f : A → B} {g : A → C} {h : B → D}
    (x : pushout (h ∘ f) g) : pushout h (@inl _ _ _ f g) :=
  begin
    induction x with d c a,
    { exact inl d },
    { exact inr (inr c) },
    { exact glue (f a) ⬝ ap inr (glue a) }
  end

  definition pushout_vcompose [constructor] {A B C D : Type} (f : A → B) (g : A → C) (h : B → D) :
    pushout h (@inl _ _ _ f g) ≃ pushout (h ∘ f) g :=
  begin
    fapply equiv.MK,
    { exact pushout_vcompose_to },
    { exact pushout_vcompose_from },
    { intro x, induction x with d c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_vcompose_to _ _ ⬝ ap02 _ !elim_glue ⬝ _,
        refine !ap_con ⬝ !elim_glue ◾ !ap_compose'⁻¹ ⬝ !idp_con ⬝ _, esimp, apply elim_glue }},
    { intro x, induction x with d y b,
      { reflexivity },
      { induction y with b c a,
        { exact glue b },
        { reflexivity },
        { apply eq_pathover, refine ap_compose pushout_vcompose_from _ _ ⬝ph _,
          esimp, refine ap02 _ !elim_glue ⬝ !elim_glue ⬝ph _, apply square_of_eq, reflexivity }},
      { apply eq_pathover_id_right, esimp,
        refine ap_compose pushout_vcompose_from _ _ ⬝ ap02 _ !elim_glue ⬝ph _, apply square_of_eq,
        reflexivity }}
  end

  definition pushout_hcompose {A B C D : Type} (f : A → B) (g : A → C) (h : C → D) :
    pushout (@inr _ _ _ f g) h ≃ pushout f (h ∘ g) :=
  calc
    pushout (@inr _ _ _ f g) h ≃ pushout h (@inr _ _ _ f g) : pushout.symm
      ... ≃ pushout h (@inl _ _ _ g f) :
              pushout.equiv _ _ _ _ erfl erfl (pushout.symm f g) (λa, idp) (λa, idp)
      ... ≃ pushout (h ∘ g) f : pushout_vcompose
      ... ≃ pushout f (h ∘ g) : pushout.symm


  definition pushout_vcompose_equiv {A B C D E : Type} (f : A → B) {g : A → C} {h : B → D}
    {hf : A → D} {k : B → E} (e : E ≃ pushout f g) (p : k ~ e⁻¹ᵉ ∘ inl) (q : h ∘ f ~ hf) :
    pushout h k ≃ pushout hf g :=
  begin
    refine _ ⬝e pushout_vcompose f g h ⬝e _,
    { fapply pushout.equiv,
        reflexivity,
        reflexivity,
        exact e,
        reflexivity,
        exact homotopy_of_homotopy_inv_post e _ _ p },
    { fapply pushout.equiv,
        reflexivity,
        reflexivity,
        reflexivity,
        exact q,
        reflexivity },
  end

  definition pushout_hcompose_equiv {A B C D E : Type} {f : A → B} (g : A → C) {h : C → E}
    {hg : A → E} {k : C → D} (e : D ≃ pushout f g) (p : k ~ e⁻¹ᵉ ∘ inr) (q : h ∘ g ~ hg) :
    pushout k h ≃ pushout f hg :=
  calc
    pushout k h ≃ pushout h k : pushout.symm
      ... ≃ pushout hg f : by exact pushout_vcompose_equiv _ (e ⬝e pushout.symm f g) p q
      ... ≃ pushout f hg : pushout.symm

  -- is the following even true?
  -- definition pushout_vcancel_right [constructor] {A B C D E : Type} {f : A → B} {g : A → C}
  --   (h : B → D) (k : B → E) (e : pushout h k ≃ pushout (h ∘ f) g)
  --   (p : e ∘ inl ~ inl) : E ≃ pushout f g :=
  -- begin
  --   fapply equiv.MK,
  --   { intro x, note aux := refl (e (inr x)), revert aux,
  --     refine pushout.rec (λy (p : e (inr x) = inl y), _) _ _ (e (inr x)),
  --       intro d q, note r := eq_of_fn_eq_fn e (q ⬝ (p d)⁻¹), exact sorry,
  --       intro c q, exact inr c,
  --       intro a, exact sorry },
  --   { intro x, induction x with b c a,
  --     { exact k b },
  --     { },
  --     { }},
  --   { },
  --   { }
  -- end

  definition pushout_of_equiv_left_to [unfold 6] {A B C : Type} {f : A ≃ B} {g : A → C}
    (x : pushout f g) : C :=
  begin
    induction x with b c a,
    { exact g (f⁻¹ b) },
    { exact c },
    { exact ap g (left_inv f a) }
  end

  definition pushout_of_equiv_left [constructor] {A B C : Type} (f : A ≃ B) (g : A → C) :
    pushout f g ≃ C :=
  begin
    fapply equiv.MK,
    { exact pushout_of_equiv_left_to },
    { exact inr },
    { intro c, reflexivity },
    { intro x, induction x with b c a,
      { exact (glue (f⁻¹ b))⁻¹ ⬝ ap inl (right_inv f b) },
      { reflexivity },
      { apply eq_pathover_id_right, refine ap_compose inr _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
        apply move_top_of_left, apply move_left_of_bot,
        refine ap02 _ (adj f _) ⬝ !ap_compose⁻¹ ⬝pv _ ⬝vp !ap_compose,
        apply natural_square_tr }}
  end

  definition pushout_of_equiv_right [constructor] {A B C : Type} (f : A → B) (g : A ≃ C) :
    pushout f g ≃ B :=
  calc
    pushout f g ≃ pushout g f : pushout.symm f g
            ... ≃ B           : pushout_of_equiv_left g f

  definition pushout_const_equiv_to [unfold 6] {A B C : Type} {f : A → B} {c₀ : C}
    (x : pushout f (const A c₀)) : pushout (sum_functor f (const unit c₀)) (const _ ⋆) :=
  begin
    induction x with b c a,
    { exact inl (sum.inl b) },
    { exact inl (sum.inr c) },
    { exact glue (sum.inl a) ⬝ (glue (sum.inr ⋆))⁻¹ }
  end

  definition pushout_const_equiv_from [unfold 6] {A B C : Type} {f : A → B} {c₀ : C}
    (x : pushout (sum_functor f (const unit c₀)) (const _ ⋆)) : pushout f (const A c₀) :=
  begin
    induction x with v u v,
    { induction v with b c, exact inl b, exact inr c },
    { exact inr c₀ },
    { induction v with a u, exact glue a, reflexivity }
  end

  definition pushout_const_equiv [constructor] {A B C : Type} (f : A → B) (c₀ : C) :
    pushout f (const A c₀) ≃ pushout (sum_functor f (const unit c₀)) (const _ ⋆) :=
  begin
    fapply equiv.MK,
    { exact pushout_const_equiv_to },
    { exact pushout_const_equiv_from },
    { intro x, induction x with v u v,
      { induction v with b c, reflexivity, reflexivity },
      { induction u, exact glue (sum.inr ⋆) },
      { apply eq_pathover_id_right,
        refine ap_compose pushout_const_equiv_to _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
        induction v with a u,
        { refine !elim_glue ⬝ph _, apply whisker_bl, exact hrfl},
        { induction u, exact square_of_eq idp }}},
    { intro x, induction x with b c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_const_equiv_from _ _ ⬝ ap02 _ !elim_glue ⬝ _,
        exact !ap_con ⬝ !elim_glue ◾ (!ap_inv ⬝ !elim_glue⁻²) }}
  end

  -- move to sum
  definition sum_of_bool [unfold 3] (A B : Type*) (b : bool) : A + B :=
  by induction b; exact sum.inl pt; exact sum.inr pt

  definition psum_of_pbool [constructor] (A B : Type*) : pbool →* (A +* B) :=
  pmap.mk (sum_of_bool A B) idp

  -- move to wedge
  definition wedge_equiv_pushout_sum [constructor] (A B : Type*) :
    wedge A B ≃ pushout (sum_of_bool A B) (const bool ⋆) :=
  begin
    refine pushout_const_equiv _ _ ⬝e _,
    fapply pushout.equiv,
      exact bool_equiv_unit_sum_unit⁻¹ᵉ,
      reflexivity,
      reflexivity,
      intro x, induction x: reflexivity,
      reflexivity
  en
d
  open prod.ops
  definition pushout_prod_equiv_to [unfold 7] {A B C D : Type} {f : A → B} {g : A → C}
    (xd : pushout f g × D) : pushout (prod_functor f (@id D)) (prod_functor g id) :=
  begin
    induction xd with x d, induction x with b c a,
    { exact inl (b, d) },
    { exact inr (c, d) },
    { exact glue (a, d) }
  end

  definition pushout_prod_equiv_from [unfold 7] {A B C D : Type} {f : A → B} {g : A → C}
    (x : pushout (prod_functor f (@id D)) (prod_functor g id)) : pushout f g × D :=
  begin
    induction x with bd cd ad,
    { exact (inl bd.1, bd.2) },
    { exact (inr cd.1, cd.2) },
    { exact prod_eq (glue ad.1) idp }
  end

  definition pushout_prod_equiv {A B C D : Type} (f : A → B) (g : A → C) :
    pushout f g × D ≃ pushout (prod_functor f (@id D)) (prod_functor g id) :=
  begin
    fapply equiv.MK,
    { exact pushout_prod_equiv_to },
    { exact pushout_prod_equiv_from },
    { intro x, induction x with bd cd ad,
      { induction bd, reflexivity },
      { induction cd, reflexivity },
      { induction ad with a d, apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_prod_equiv_to _ _ ⬝ ap02 _ !elim_glue ⬝ _, esimp,
        exact !ap_prod_elim ⬝ !idp_con ⬝ !elim_glue }},
    { intro xd, induction xd with x d, induction x with b c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        exact ap_compose pushout_prod_equiv_from _ _ ⬝ ap02 _ !elim_glue ⬝ !elim_glue }}
  end

end pushout
