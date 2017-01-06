-- Authors: Floris van Doorn

import homotopy.smash ..move_to_lib .pushout homotopy.red_susp

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function red_susp

  /- smash A (susp B) = susp (smash A B) <- this follows from associativity and smash with S¹ -/

  /- To prove: Σ(X × Y) ≃ ΣX ∨ ΣY ∨ Σ(X ∧ Y) (notation means suspension, wedge, smash),
     and both are equivalent to the reduced join -/

  /- To prove: associative -/

  /- smash A B ≃ pcofiber (pprod_of_pwedge A B) -/

variables {A B : Type*}

namespace smash

  theorem elim_gluel' {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a a' : A) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluel' a a') = Pgl a ⬝ (Pgl a')⁻¹ :=
  !ap_con ⬝ !elim_gluel ◾ (!ap_inv ⬝ !elim_gluel⁻²)

  theorem elim_gluer' {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (b b' : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluer' b b') = Pgr b ⬝ (Pgr b')⁻¹ :=
  !ap_con ⬝ !elim_gluer ◾ (!ap_inv ⬝ !elim_gluer⁻²)

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
      reflexivity,
      exact bool_of_sum_of_bool,
    apply pushout_of_equiv_right
  end

end pushout open pushout

namespace smash

  variables (A B)
  definition smash_equiv_cofiber : smash A B ≃ cofiber (@prod_of_wedge A B) :=
  begin
    unfold [smash, cofiber, smash'], symmetry,
    refine !pushout.symm ⬝e _,
    fapply pushout_vcompose_equiv wedge_of_sum,
    { symmetry, apply equiv_unit_of_is_contr, apply is_contr_pushout_wedge_of_sum },
    { intro x, reflexivity },
    { apply prod_of_wedge_of_sum }
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
    exact (cofiber.glue pt)⁻¹
  end

  variables {A B}

  /- commutativity -/

  definition smash_flip (x : smash A B) : smash B A :=
  begin
    induction x,
    { exact smash.mk b a },
    { exact auxr },
    { exact auxl },
    { exact gluer a },
    { exact gluel b }
  end

  definition smash_flip_smash_flip (x : smash A B) : smash_flip (smash_flip x) = x :=
  begin
    induction x,
    { reflexivity },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose' smash_flip _ _ ⬝ ap02 _ !elim_gluel ⬝ !elim_gluer ⬝ph _,
      apply hrfl },
    { apply eq_pathover_id_right,
      refine ap_compose' smash_flip _ _ ⬝ ap02 _ !elim_gluer ⬝ !elim_gluel ⬝ph _,
      apply hrfl }
  end

  definition smash_comm : smash A B ≃* smash B A :=
  begin
    fapply pequiv_of_equiv,
    { apply equiv.MK, do 2 exact smash_flip_smash_flip },
    { reflexivity }
  end

  /- smash A S¹ = red_susp A -/

  definition circle_elim_constant [unfold 5] {A : Type} {a : A} {p : a = a} (r : p = idp) (x : S¹) :
    circle.elim a p x = a :=
  begin
    induction x,
    { reflexivity },
    { apply eq_pathover_constant_right, apply hdeg_square, exact !elim_loop ⬝ r }
  end


  definition red_susp_of_smash_pcircle [unfold 2] (x : smash A S¹*) : red_susp A :=
  begin
    induction x using smash.elim,
    { induction b, exact base, exact equator a },
    { exact base },
    { exact base },
    { reflexivity },
    { exact circle_elim_constant equator_pt b }
  end

  definition smash_pcircle_of_red_susp [unfold 2] (x : red_susp A) : smash A S¹* :=
  begin
    induction x,
    { exact pt },
    { exact gluel' pt a ⬝ ap (smash.mk a) loop ⬝ gluel' a pt },
    { refine !con.right_inv ◾ _ ◾ !con.right_inv,
      exact ap_is_constant gluer loop ⬝ !con.right_inv }
  end

  definition smash_pcircle_of_psusp_of_smash_pcircle_pt [unfold 3] (a : A) (x : S¹*) :
    smash_pcircle_of_red_susp (red_susp_of_smash_pcircle (smash.mk a x)) = smash.mk a x :=
  begin
    induction x,
    { exact gluel' pt a },
    { exact abstract begin apply eq_pathover,
      refine ap_compose smash_pcircle_of_red_susp _ _ ⬝ph _,
      refine ap02 _ (elim_loop pt (equator a)) ⬝ !elim_equator ⬝ph _,
      -- make everything below this a lemma defined by path induction?
      refine !con_idp⁻¹ ⬝pv _, refine !con.assoc⁻¹ ⬝ph _, apply whisker_bl, apply whisker_lb,
      apply whisker_tl, apply hrfl end end }
  end

  definition concat2o [unfold 10] {A B : Type} {f g h : A → B} {q : f ~ g} {r : g ~ h} {a a' : A}
    {p : a = a'} (s : q a =[p] q a') (t : r a =[p] r a') : q a ⬝ r a =[p] q a' ⬝ r a' :=
  by induction p; exact idpo

  definition apd_con_fn [unfold 10] {A B : Type} {f g h : A → B} {q : f ~ g} {r : g ~ h} {a a' : A}
    (p : a = a') : apd (λa, q a ⬝ r a) p = concat2o (apd q p) (apd r p) :=
  by induction p; reflexivity

  -- definition apd_con_fn_constant [unfold 10] {A B : Type} {f : A → B} {b b' : B} {q : Πa, f a = b}
  --   {r : b = b'} {a a' : A} (p : a = a') :
  --   apd (λa, q a ⬝ r) p = concat2o (apd q p) (pathover_of_eq _ idp) :=
  -- by induction p; reflexivity

  theorem apd_constant' {A A' : Type} {B : A' → Type} {a₁ a₂ : A} {a' : A'} (b : B a')
    (p : a₁ = a₂) : apd (λx, b) p = pathover_of_eq p idp :=
  by induction p; reflexivity

  definition smash_pcircle_pequiv_red [constructor] (A : Type*) : smash A S¹* ≃* red_susp A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact red_susp_of_smash_pcircle },
      { exact smash_pcircle_of_red_susp },
      { exact abstract begin intro x, induction x,
        { reflexivity },
        { apply eq_pathover, apply hdeg_square,
          refine ap_compose red_susp_of_smash_pcircle _ _ ⬝ ap02 _ !elim_equator ⬝ _ ⬝ !ap_id⁻¹,
          refine !ap_con ⬝ (!ap_con ⬝ !elim_gluel' ◾ !ap_compose'⁻¹) ◾ !elim_gluel' ⬝ _,
          esimp, exact !idp_con ⬝ !elim_loop },
        { exact sorry } end end },
      { intro x, induction x,
        { exact smash_pcircle_of_psusp_of_smash_pcircle_pt a b },
        { exact gluel pt },
        { exact gluer pt },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_red_susp _ _ ⬝ph _,
          unfold [red_susp_of_smash_pcircle],
          refine ap02 _ !elim_gluel ⬝ph _,
          esimp, apply whisker_rt, exact vrfl },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_red_susp _ _ ⬝ph _,
          unfold [red_susp_of_smash_pcircle],
          -- not sure why so many implicit arguments are needed here...
          refine ap02 _ (@smash.elim_gluer A S¹* _ (λa, circle.elim red_susp.base (equator a)) red_susp.base red_susp.base (λa, refl red_susp.base) (circle_elim_constant equator_pt) b) ⬝ph _,
          apply square_of_eq, induction b,
          { exact whisker_right _ !con.right_inv },
          { apply eq_pathover_dep, refine !apd_con_fn ⬝pho _ ⬝hop !apd_con_fn⁻¹,
            refine ap (λx, concat2o x _) !rec_loop ⬝pho _ ⬝hop (ap011 concat2o (apd_compose1 (λa b, ap smash_pcircle_of_red_susp b) (circle_elim_constant equator_pt) loop) !apd_constant')⁻¹,
            }

          }}},
    { reflexivity }
  end
print apd_constant
print apd_compose2
print apd_compose1
print apd_con
print eq_pathover_dep
--set_option pp.all true
print smash.elim_gluer
  /- smash A S¹ = susp A -/
  open susp


  definition psusp_of_smash_pcircle [unfold 2] (x : smash A S¹*) : psusp A :=
  begin
    induction x using smash.elim,
    { induction b, exact pt, exact merid a ⬝ (merid pt)⁻¹ },
    { exact pt },
    { exact pt },
    { reflexivity },
    { induction b, reflexivity, apply eq_pathover_constant_right, apply hdeg_square,
      exact !elim_loop ⬝ !con.right_inv }
  end

  definition smash_pcircle_of_psusp [unfold 2] (x : psusp A) : smash A S¹* :=
  begin
    induction x,
    { exact pt },
    { exact pt },
    { exact gluel' pt a ⬝ (ap (smash.mk a) loop ⬝ gluel' a pt) },
  end

 -- the definitions below compile, but take a long time to do so and have sorry's in them
  definition smash_pcircle_of_psusp_of_smash_pcircle_pt [unfold 3] (a : A) (x : S¹*) :
    smash_pcircle_of_psusp (psusp_of_smash_pcircle (smash.mk a x)) = smash.mk a x :=
  begin
    induction x,
    { exact gluel' pt a },
    { exact abstract begin apply eq_pathover,
      refine ap_compose smash_pcircle_of_psusp _ _ ⬝ph _,
      refine ap02 _ (elim_loop north (merid a ⬝ (merid pt)⁻¹)) ⬝ph _,
      refine !ap_con ⬝ (!elim_merid ◾ (!ap_inv ⬝ !elim_merid⁻²)) ⬝ph _,
      -- make everything below this a lemma defined by path induction?
      refine !con_idp⁻¹ ⬝pv _, apply whisker_tl, refine !con.assoc⁻¹ ⬝ph _,
      apply whisker_bl, apply whisker_lb,
      refine !con_idp⁻¹ ⬝pv _, apply whisker_tl, apply hrfl
      refine !con_idp⁻¹ ⬝pv _, apply whisker_tl,
      refine !con.assoc⁻¹ ⬝ph _, apply whisker_bl, apply whisker_lb, apply hrfl
      apply square_of_eq, rewrite [+con.assoc], apply whisker_left, apply whisker_left,
      symmetry, apply con_eq_of_eq_inv_con, esimp, apply con_eq_of_eq_con_inv,
      refine _⁻² ⬝ !con_inv, refine _ ⬝ !con.assoc,
      refine _ ⬝ whisker_right _ !inv_con_cancel_right⁻¹, refine _ ⬝ !con.right_inv⁻¹,
      refine !con.right_inv ◾ _, refine _ ◾ !con.right_inv,
      refine !ap_mk_right ⬝ !con.right_inv end end }
  end

  -- definition smash_pcircle_of_psusp_of_smash_pcircle_gluer_base (b : S¹*)
  --   : square (smash_pcircle_of_psusp_of_smash_pcircle_pt (Point A) b)
  --            (gluer pt)
  --            (ap smash_pcircle_of_psusp (ap (λ a, psusp_of_smash_pcircle a) (gluer b)))
  --            (gluer b) :=
  -- begin
  --   refine ap02 _ !elim_gluer ⬝ph _,
  --   induction b,
  --   { apply square_of_eq, exact whisker_right _ !con.right_inv },
  --   { apply square_pathover', exact sorry }
  -- end

exit
  definition smash_pcircle_pequiv [constructor] (A : Type*) : smash A S¹* ≃* psusp A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact psusp_of_smash_pcircle },
      { exact smash_pcircle_of_psusp },
      { exact abstract begin intro x, induction x,
        { reflexivity },
        { exact merid pt },
        { apply eq_pathover_id_right,
          refine ap_compose psusp_of_smash_pcircle _ _ ⬝ph _,
          refine ap02 _ !elim_merid ⬝ph _,
          rewrite [↑gluel', +ap_con, +ap_inv, -ap_compose'],
          refine (_ ◾ _⁻² ◾ _ ◾ (_ ◾ _⁻²)) ⬝ph _,
          rotate 5, do 2 (unfold [psusp_of_smash_pcircle]; apply elim_gluel),
          esimp, apply elim_loop, do 2 (unfold [psusp_of_smash_pcircle]; apply elim_gluel),
          refine idp_con (merid a ⬝ (merid (Point A))⁻¹) ⬝ph _,
          apply square_of_eq, refine !idp_con ⬝ _⁻¹, apply inv_con_cancel_right } end end },
      { intro x, induction x using smash.rec,
        { exact smash_pcircle_of_psusp_of_smash_pcircle_pt a b },
        { exact gluel pt },
        { exact gluer pt },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_psusp _ _ ⬝ph _,
          unfold [psusp_of_smash_pcircle],
          refine ap02 _ !elim_gluel ⬝ph _,
          esimp, apply whisker_rt, exact vrfl },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_psusp _ _ ⬝ph _,
          unfold [psusp_of_smash_pcircle],
          refine ap02 _ !elim_gluer ⬝ph _,
          induction b,
          { apply square_of_eq, exact whisker_right _ !con.right_inv },
          { exact sorry}
          }}},
    { reflexivity }
  end

end smash
-- (X × A) → Y ≃ X → A → Y
