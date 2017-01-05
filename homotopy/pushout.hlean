

import ..move_to_lib

open eq function is_trunc sigma prod sigma.ops lift is_equiv equiv

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

  protected definition inv_left (H : is_pushout2 p) {X : Type} (v : cocone p X) :
    (cocone_of_map p X)⁻¹ᶠ v ∘ h ~ prod.pr1 v.1 :=
  ap10 (ap prod.pr1 (right_inv (cocone_of_map p X) v)..1)

  protected definition inv_right (H : is_pushout2 p) {X : Type} (v : cocone p X) :
    (cocone_of_map p X)⁻¹ᶠ v ∘ k ~ prod.pr2 v.1 :=
  ap10 (ap prod.pr2 (right_inv (cocone_of_map p X) v)..1)

  section
    local attribute is_pushout [reducible]
    definition is_prop_is_pushout : is_prop (is_pushout p) :=
    _

    local attribute is_pushout2 [reducible]
    definition is_prop_is_pushout2 : is_prop (is_pushout2 p) :=
    _
  end
print ap_ap10
print apd10_ap
print apd10
print ap10
print apd10_ap_precompose_dependent

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

  definition pushout_compose_to [unfold 8] {A B C D : Type} {f : A → B} {g : A → C} {h : B → D}
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

  definition pushout_compose_from [unfold 8] {A B C D : Type} {f : A → B} {g : A → C} {h : B → D}
    (x : pushout (h ∘ f) g) : pushout h (@inl _ _ _ f g) :=
  begin
    induction x with d c a,
    { exact inl d },
    { exact inr (inr c) },
    { exact glue (f a) ⬝ ap inr (glue a) }
  end

  definition pushout_compose [constructor] {A B C D : Type} (f : A → B) (g : A → C) (h : B → D) :
    pushout h (@inl _ _ _ f g) ≃ pushout (h ∘ f) g :=
  begin
    fapply equiv.MK,
    { exact pushout_compose_to },
    { exact pushout_compose_from },
    { intro x, induction x with d c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_compose_to _ _ ⬝ ap02 _ !elim_glue ⬝ _,
        refine !ap_con ⬝ !elim_glue ◾ !ap_compose'⁻¹ ⬝ !idp_con ⬝ _, esimp, apply elim_glue }},
    { intro x, induction x with d y b,
      { reflexivity },
      { induction y with b c a,
        { exact glue b },
        { reflexivity },
        { apply eq_pathover, refine ap_compose pushout_compose_from _ _ ⬝ph _,
          esimp, refine ap02 _ !elim_glue ⬝ !elim_glue ⬝ph _, apply square_of_eq, reflexivity }},
      { apply eq_pathover_id_right, esimp,
        refine ap_compose pushout_compose_from _ _ ⬝ ap02 _ !elim_glue ⬝ph _, apply square_of_eq, reflexivity }}
  end

  definition pushout_compose' {A B C D : Type} (f : A → B) (g : A → C) (h : B → D) :
    pushout (@inl _ _ _ f g) h ≃ pushout g (h ∘ f) :=
  calc
    pushout (@inl _ _ _ f g) h ≃ pushout h (@inl _ _ _ f g) : pushout.symm
      ... ≃ pushout (h ∘ f) g : pushout_compose
      ... ≃ pushout g (h ∘ f) : pushout.symm


  definition pushout_compose_equiv {A B C D E : Type} (f : A → B) {g : A → C} {h : B → D} {hf : A → D}
    {k : B → E} (e : E ≃ pushout f g) (p : k ~ e⁻¹ᵉ ∘ inl) (q : h ∘ f ~ hf) :
    pushout h k ≃ pushout hf g :=
  begin
    refine _ ⬝e pushout_compose f g h ⬝e _,
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

end pushout
