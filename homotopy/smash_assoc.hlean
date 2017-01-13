-- Authors: Floris van Doorn

import .smash

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function red_susp unit sigma

namespace smash

  variables {A B C : Type*}

  open pushout
  definition prod3_of_sum3 [unfold 4] (A B C : Type*) : A × C ⊎ A × B ⊎ C × B → A × B × C :=
  begin
    intro v, induction v with ac v,
      exact (ac.1, (pt, ac.2)),
      induction v with ab cb,
        exact (ab.1, (ab.2, pt)),
        exact (pt, (cb.2, cb.1))
  end

  definition fin3_of_sum3 [unfold 4] (A B C : Type*) : A × C ⊎ A × B ⊎ C × B → A ⊎ B ⊎ C :=
  sum_functor (λac, ac.1) (sum_functor (λab, ab.2) (λcb, cb.1))

  definition smash3 (A B C : Type*) : Type* :=
  pointed.MK (pushout (prod3_of_sum3 A B C) (fin3_of_sum3 A B C)) (inl (pt, (pt, pt)))

  definition to_image {A B : Type} (f : A → B) (a : A) : sigma (image f) :=
  ⟨f a, image.mk a idp⟩

  definition pushout_image_prod3_of_sum3 (A B C : Type*) : Type :=
  pushout (to_image (prod3_of_sum3 A B C)) (fin3_of_sum3 A B C)

  -- definition pushout_image_prod3_of_sum3_equiv (A B C : Type*) : pushout_image_prod3_of_sum3 A B C ≃ unit :=
  -- begin
  --   apply equiv_unit_of_is_contr,
  --   fapply is_contr.mk,
  --   { exact inr (sum.inl pt) },
  --   { intro x, refine @center _ _,
  --     induction x using pushout.rec_prop,
  --     { induction x with abc p,
  --       induction p with v p, induction p,
  --       induction v with ac v,
  --       { induction ac with a c, esimp [prod3_of_sum3], },
  --       induction v with ab cb,
  --       { },
  --       { }},
  --     { }}
  -- end

  -- definition pushout_wedge_of_sum_equiv_unit : pushout (@wedge_of_sum A B) bool_of_sum ≃ unit :=
  -- begin
  --   refine pushout_hcompose_equiv (sum_of_bool A B) (wedge_equiv_pushout_sum A B)
  --            _ _ ⬝e _,
  --     exact erfl,
  --     intro x, induction x: esimp,
  --     exact bool_of_sum_of_bool,
  --   apply pushout_of_equiv_right
  -- end


  -- definition smash3_comm (A B C : Type*) : smash3 A B C ≃* smash3 C B A :=
  -- begin
  --   fapply pequiv_of_equiv,
  --   { fapply pushout.equiv,
  --     { apply sum_equiv_sum (prod_comm_equiv A C) (sum_comm_equiv (A × B) (C × B)) },
  --     { refine prod_assoc_equiv A B C ⬝e prod_comm_equiv (A × B) C
  --              ⬝e prod_equiv_prod_left (prod_comm_equiv A B) },
  --     { refine sum_assoc_equiv A B C ⬝e sum_comm_equiv (A + B) C ⬝e sum_equiv_sum_left (sum_comm_equiv A B) },
  --     { intro x, induction x with ac x, reflexivity, induction x with ab cb: reflexivity },
  --     { intro x, induction x with ac x, induction ac with a c, esimp, reflexivity, induction x with ab cb: reflexivity }},
  --   { reflexivity }
  -- end


  /- attempt 1, direct proof that A ∧ (B ∧ C) ≃ smash3 A B C -/

  definition glue1 (a : A) (b : B) : inl (a, (b, pt)) = inr (inr (inl b)) :> smash3 A B C :=
  pushout.glue (inr (inl (a, b)))

  definition glue2 (b : B) (c : C) : inl (pt, (b, c)) = inr (inr (inr c)) :> smash3 A B C :=
  pushout.glue (inr (inr (c, b)))

  definition glue3 (c : C) (a : A) : inl (a, (pt, c)) = inr (inl a) :> smash3 A B C :=
  pushout.glue (inl (a, c))

  definition smash3_of_prod_smash [unfold 5] (a : A) (bc : B ∧ C) : smash3 A B C :=
  begin
    induction bc using smash.elim' with b c b c,
    { exact inl (a, (b, c)) },
    { refine glue1 a b ⬝ (glue1 pt b)⁻¹ ⬝ (glue2 b pt ⬝ (glue2 pt pt)⁻¹) ⬝ (glue1 pt pt ⬝ (glue1 a pt)⁻¹) },
    { refine glue3 c a ⬝ (glue3 pt a)⁻¹ ⬝ (glue1 a pt ⬝ (glue1 pt pt)⁻¹) ⬝ (glue1 pt pt ⬝ (glue1 a pt)⁻¹) },
    { exact abstract whisker_right _ (whisker_left _ !con.right_inv ⬝ !con_idp) ⬝ !con.assoc ⬝
             whisker_left _ !inv_con_cancel_left ⬝ !con.right_inv end },
    { exact abstract whisker_right _ (whisker_right _ !con.right_inv ⬝ !idp_con) ⬝ !con.assoc ⬝
             whisker_left _ !inv_con_cancel_left ⬝ !con.right_inv end }
  end

  -- definition smash3_of_prod_smash [unfold 5] (a : A) (bc : B ∧ C) : smash3 A B C :=
  -- begin
  --   induction bc with b c b c,
  --   { exact inl (a, (b, c)) },
  --   { exact pt },
  --   { exact pt },
  --   { refine glue1 a b ⬝ (glue1 pt b)⁻¹ ⬝ (glue2 b pt ⬝ (glue2 pt pt)⁻¹) },
  --   { refine glue3 c a ⬝ (glue3 pt a)⁻¹ ⬝ (glue1 a pt ⬝ (glue1 pt pt)⁻¹) }
  -- end

  definition smash3_of_smash_smash_gluer [unfold 4] (bc : B ∧ C) :
    smash3_of_prod_smash (pt : A) bc = pt :=
  begin
    induction bc with b c b c,
    { exact glue2 b c ⬝ (glue2 pt c)⁻¹ ⬝ (glue3 c pt ⬝ (glue3 pt pt)⁻¹) },
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_constant_right, apply square_of_eq, refine !con_idp ⬝ _ ⬝ !elim_gluel⁻¹,
      refine whisker_right _ !idp_con⁻¹ ⬝ !con.right_inv⁻¹ ◾ idp ◾ (!con.right_inv ⬝ !con.right_inv⁻¹) },
    { apply eq_pathover_constant_right, apply square_of_eq, refine !con_idp ⬝ _ ⬝ !elim_gluer⁻¹,
      refine whisker_right _ !con.right_inv ⬝ !idp_con ⬝ !con_idp⁻¹ ⬝ whisker_left _ !con.right_inv⁻¹ ⬝
             !con_idp⁻¹ ⬝ whisker_left _ !con.right_inv⁻¹ }
  end

  definition smash3_of_smash_smash [unfold 4] (x : A ∧ (B ∧ C)) : smash3 A B C :=
  begin
    induction x using smash.elim' with a bc a bc,
    { exact smash3_of_prod_smash a bc },
    { exact glue1 a pt ⬝ (glue1 pt pt)⁻¹ },
    { exact smash3_of_smash_smash_gluer bc },
    { apply con.right_inv },
    { exact !con.right_inv ◾ !con.right_inv }
  end

  definition smash_smash_of_smash3 [unfold 4] (x : smash3 A B C) : A ∧ (B ∧ C) :=
  begin
    induction x,
    { exact smash.mk a.1 (smash.mk a.2.1 a.2.2) },
    { exact pt },
    { exact abstract begin induction x with ac x,
      { induction ac with a c, exact ap (smash.mk a) (gluer' c pt) ⬝ gluel' a pt },
      induction x with ab cb,
      { induction ab with a b, exact ap (smash.mk a) (gluel' b pt) ⬝ gluel' a pt },
      { induction cb with c b, exact gluer' (smash.mk b c) pt } end end },
  end

  definition smash3_of_smash_smash_of_smash3_inl [unfold 4] (x : A × B × C) :
    smash3_of_smash_smash (smash_smash_of_smash3 (inl x)) = inl x :=
  begin
    induction x with a x, induction x with b c, reflexivity
  end

  definition smash3_of_smash_smash_of_smash3_inr [unfold 4] (x : A ⊎ B ⊎ C) :
    smash3_of_smash_smash (smash_smash_of_smash3 (inr x)) = inr x :=
  begin
    induction x with a x,
    { exact (glue1 pt pt ⬝ (glue1 a pt)⁻¹) ⬝ glue3 pt a},
    induction x with b c,
    { exact (glue2 pt pt ⬝ (glue2 b pt)⁻¹) ⬝ glue1 pt b},
    { exact (glue3 pt pt ⬝ (glue3 c pt)⁻¹) ⬝ glue2 pt c}
  end

  attribute smash_smash_of_smash3_1 [unfold 4]

  definition smash_smash_of_smash3_of_prod_smash [unfold 5] (a : A) (bc : B ∧ C) :
    smash_smash_of_smash3 (smash3_of_prod_smash a bc) = smash.mk a bc :=
  begin
    induction bc with b c b c,
    { reflexivity },
    { exact ap (smash.mk a) (gluel pt) },
    { exact ap (smash.mk a) (gluer pt) },
    { apply eq_pathover, refine ap_compose smash_smash_of_smash3 _ _ ⬝ ap02 _ !elim_gluel ⬝ph _,
      refine !ap_con ⬝ (!ap_con ⬝ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²)) ◾ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²))) ◾ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²)) ⬝ph _, rotate 3, do 3 exact !pushout.elim_glue, esimp,
      exact sorry },
    { apply eq_pathover, refine ap_compose smash_smash_of_smash3 _ _ ⬝ ap02 _ !elim_gluer ⬝ph _,
      refine !ap_con ⬝ (!ap_con ⬝ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²)) ◾ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²))) ◾ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²)) ⬝ph _, rotate 3, do 3 exact !pushout.elim_glue,
      exact sorry }
  end

  -- the commented out is a slow but correct proof
  definition smash_smash_equiv_smash3 (A B C : Type*) : A ∧ (B ∧ C) ≃* smash3 A B C :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact smash3_of_smash_smash },
      { exact smash_smash_of_smash3 },
      { intro x, --induction x,
        -- { exact smash3_of_smash_smash_of_smash3_inl x },
        -- { exact smash3_of_smash_smash_of_smash3_inr x },
        -- { apply eq_pathover_id_right,
        --   refine ap_compose smash3_of_smash_smash _ _ ⬝ ap02 _ !pushout.elim_glue ⬝ph _,
        --   induction x with ac x,
        --   { induction ac with a c,
        --     refine !ap_con ⬝ !ap_compose'⁻¹ ◾ proof !elim'_gluel'_pt qed ⬝ph _,
        --     xrewrite [{ap (smash3_of_smash_smash ∘ smash.mk a)}(idpath (ap (smash3_of_prod_smash a)))],
        --     esimp, refine !elim'_gluer'_pt ◾ idp ⬝ph _,
        --     refine _ ⬝vp whisker_right _ !inv_con_inv_right, apply whisker_lb,
        --     refine whisker_left _ !inv_con_inv_right⁻¹ ⬝ !con_inv_cancel_right ⬝ph _,
        --     apply whisker_bl, exact hrfl },
        --   induction x with ab bc,
        --   { induction ab with a b,
        --     refine !ap_con ⬝ !ap_compose'⁻¹ ◾ proof !elim'_gluel'_pt qed ⬝ph _, esimp,
        --     refine !elim'_gluel'_pt ◾ idp ⬝ph _,
        --     refine whisker_left _ !inv_con_inv_right⁻¹ ⬝ !con.assoc ⬝ whisker_left _ !con.right_inv ⬝ !con_idp ⬝ph _,
        --     refine _ ⬝vp whisker_right _ !inv_con_inv_right, apply whisker_lb, apply whisker_bl, exact hrfl
        --     },
        --   { induction bc with b c, refine !elim'_gluer'_pt ⬝ph _, esimp,
        --     refine whisker_left _ !inv_con_inv_right⁻¹ ⬝ph _, apply whisker_bl, apply whisker_bl, exact hrfl }}
exact sorry
},
      { intro x, induction x with a bc a bc,
        { exact smash_smash_of_smash3_of_prod_smash a bc },
        { apply gluel },
        { apply gluer },
        { apply eq_pathover_id_right, refine ap_compose smash_smash_of_smash3 _ _ ⬝ ap02 _ !elim_gluel ⬝ph _,
          refine !ap_con ⬝ (!pushout.elim_glue ◾ (!ap_inv ⬝ !pushout.elim_glue⁻²)) ⬝ph _, apply sorry, },
        { apply eq_pathover_id_right, refine ap_compose smash_smash_of_smash3 _ _ ⬝ ap02 _ !elim_gluer ⬝ph _,
          induction bc with b c b c,
          { refine !ap_con ⬝ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²)) ◾ (!ap_con ⬝ !pushout.elim_glue ◾ (!ap_inv ⬝ _⁻²)) ⬝ph _, rotate 2, do 2 apply !pushout.elim_glue, exact sorry },
          { exact sorry },
          { exact sorry },
          { exact sorry },
          { exact sorry }}}},
    { reflexivity }
  end

  -- definition smash_assoc (A B C : Type*) : A ∧ (B ∧ C) ≃* (A ∧ B) ∧ C :=
  -- calc
  --   A ∧ (B ∧ C) ≃* smash3 A B C : smash_smash_equiv_smash3
  --           ... ≃* smash3 C B A : smash3_comm
  --           ... ≃* C ∧ (B ∧ A) : smash_smash_equiv_smash3
  --           ... ≃* (B ∧ A) ∧ C : smash_comm C (B ∧ A)
  --           ... ≃* (A ∧ B) ∧ C : smash_pequiv_smash_left C (smash_comm B A)

  -- end

end smash

  /- attempt 2: proving the induction principle of smash3 A B C for A ∧ (B ∧ C) -/

namespace smash

  variables {A B C : Type*}

  /- an induction principle which has only 1 point constructor, but which has bad computation properties -/
  protected definition rec' {P : smash A B → Type} (Pmk : Πa b, P (smash.mk a b))
    (Pgl : Πa, Pmk a pt =[gluel' a pt] Pmk pt pt)
    (Pgr : Πb, Pmk pt b =[gluer' b pt] Pmk pt pt) (x : smash' A B) : P x :=
  begin
    induction x using smash.rec,
    { apply Pmk },
    { exact gluel pt ▸ Pmk pt pt },
    { exact gluer pt ▸ Pmk pt pt },
    { refine change_path _ (Pgl a ⬝o !pathover_tr), apply inv_con_cancel_right },
    { refine change_path _ (Pgr b ⬝o !pathover_tr), apply inv_con_cancel_right }
  end

--   protected definition rec'_gluel' {P : smash A B → Type} (Pmk : Πa b, P (smash.mk a b))
--     (Pgl : Πa, Pmk a pt =[gluel' a pt] Pmk pt pt)
--     (Pgr : Πb, Pmk pt b =[gluer' b pt] Pmk pt pt) (a : A) : apd (smash.rec' Pmk Pgl Pgr) (gluel' a pt) = Pgl a :=
--   begin
--     refine !apd_con ⬝ _,
--     refine ap011 concato !rec_gluel (!apd_inv ⬝ ap inverseo !rec_gluel ⬝ !change_path_invo⁻¹) ⬝ _,
--     refine !change_path_cono⁻¹ ⬝ _,
--     -- refine cono_invo
-- --      refine change_path_invo
--   end

--   protected definition rec'_gluer' {P : smash A B → Type} (Pmk : Πa b, P (smash.mk a b))
--     (Pgl : Πa, Pmk a pt =[gluel' a pt] Pmk pt pt)
--     (Pgr : Πb, Pmk pt b =[gluer' b pt] Pmk pt pt) (b : B) : apd (smash.rec' Pmk Pgl Pgr) (gluer' b pt) = Pgr b :=
--   sorry

  definition inl3 (a : A) (b : B) (c : C) : A ∧ (B ∧ C) :=
  smash.mk a (smash.mk b c)

  definition aux1 (a : A) : A ∧ (B ∧ C) := pt
  definition aux2 (b : B) : A ∧ (B ∧ C) := pt
  definition aux3 (c : C) : A ∧ (B ∧ C) := pt

  definition glue12 (a : A) (b : B) : inl3 a b (pt : C) = aux1 a :=
  ap (smash.mk a) (gluel' b pt) ⬝ gluel' a pt

  definition glue23 (b : B) (c : C) : inl3 (pt : A) b c = aux2 b :=
  gluer' (smash.mk b c) pt

  definition glue31 (c : C) (a : A) : inl3 a (pt : B) c = aux3 c :=
  ap (smash.mk a) (gluer' c pt) ⬝ gluel' a pt

  definition glue1_eq (a : A) : glue12 a pt = glue31 pt a :> (_ = _ :> (A ∧ (B ∧ C))) :=
  whisker_right _ (ap02 _ (!con.right_inv ⬝ !con.right_inv⁻¹))

  definition glue2_eq (b : B) : glue23 b pt = glue12 pt b :> (_ = _ :> (A ∧ (B ∧ C))) :=
  !con_idp⁻¹ ⬝ !ap_mk_right⁻¹ ◾ !con.right_inv⁻¹

  definition glue3_eq (c : C) : glue31 c pt = glue23 pt c :> (_ = _ :> (A ∧ (B ∧ C))) :=
  !ap_mk_right ◾ !con.right_inv ⬝ !con_idp

local attribute ap_mk_right [reducible]

  definition concat3 {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
    {r r' : p = p'} {s s' : q = q'} : r = r' → s = s' → r ◾ s = r' ◾ s' :=
  ap011 concat2

  definition glue_eq2 : glue3_eq (pt : A) ⬝ glue2_eq (pt : B) ⬝ glue1_eq (pt : C) = idp :=
  begin
    unfold [glue1_eq, glue2_eq, glue3_eq],
    refine proof ap011 concat2 proof (ap_is_constant_idp _ _ !con.right_inv) qed idp qed ◾
           (!idp_con ⬝ proof ap011 concat2 proof (ap_is_constant_idp _ _ !con.right_inv) qed⁻² idp qed) ◾
           idp ⬝ _,
    refine whisker_right _ _ ⬝ _,
      exact ((ap02 (smash.mk (Point C)) (con.right_inv (gluer (Point A))) ⬝ (con.right_inv
        (gluer (smash.mk (Point B) (Point A))))⁻¹) ⬝ (ap02 (smash.mk (Point C))
        (con.right_inv (gluel (Point B))) ⬝ (con.right_inv
        (gluer (smash.mk (Point B) (Point A))))⁻¹)⁻¹) ◾ idp,
    { refine _ ⬝ concat3 idp (con.right_inv  (con.right_inv (gluel (Point C)))),
      refine proof idp qed ⬝ !con2_con_con2 },
    refine !con2_con_con2 ⬝ _,
    refine ap (whisker_right _) _ ⬝ whisker_right_idp_left _ _,
    refine idp ◾ !inv_con_inv_right ◾ idp ⬝ _,
    refine whisker_right _ (!con.assoc ⬝ whisker_left _ (!inv_con_cancel_left ⬝ !ap_inv⁻¹)) ⬝ _,
    refine whisker_right _ !ap_con⁻¹ ⬝ !ap_con⁻¹ ⬝ _,
    refine ap_is_constant (@is_constant.eq _ _ _ (@is_constant_ap _ _ _ _ _ _)) _ ⬝ !con.right_inv,
    constructor, exact gluer
  end

  definition glue12_cancel (a : A) (b : B) : @glue12 A B C a b ⬝ (glue12 a pt)⁻¹ ⬝ ap (smash.mk a) (gluel pt) = ap (smash.mk a) (gluel b) :=
  begin
    unfold [glue12],
    refine whisker_right _ (whisker_left _ !con_inv ⬝ whisker_left _ (whisker_left _ (ap02 _ !con.right_inv)⁻² ⬝ !con_idp) ⬝ !con_inv_cancel_right) ⬝ _,
    refine !ap_con⁻¹ ⬝ ap02 _ !inv_con_cancel_right,
  end

  definition glue12_cancel_pt_pt : @glue12_cancel A B C pt pt = whisker_right _ !con.right_inv ⬝ !idp_con :=
  sorry

  definition glue12_over {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (inl3 a b c))
    (P1 : Πa, P (aux1 a))
    (P12 : Πa b, Ppt a b pt =[glue12 a b] P1 a)
    (a : A) (b : B) : pathover P (Ppt a b pt) (ap (smash.mk a) (gluel b)) (transport P (ap (smash.mk a) (gluel pt)) (Ppt a pt pt)) :=
  begin
    exact change_path (glue12_cancel a b) (P12 a b ⬝o (P12 a pt)⁻¹ᵒ ⬝o pathover_tr (ap (smash.mk a) (gluel pt)) (Ppt a pt pt))
  end

  definition glue12_over_pt_pt {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (inl3 a b c))
    (P1 : Πa, P (aux1 a))
    (P12 : Πa b, Ppt a b pt =[glue12 a b] P1 a) :
    glue12_over Ppt P1 P12 pt pt = pathover_tr (ap (smash.mk pt) (gluel pt)) (Ppt pt pt pt) :=
  sorry

  definition smash3_rec_mk [unfold 13] {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (inl3 a b c))
    (P1 : Πa, P (aux1 a)) (P2 : Πb, P (aux2 b)) (P3 : Πc, P (aux3 c))
    (P12 : Πa b, Ppt a b pt =[glue12 a b] P1 a)
    (P23 : Πb c, Ppt pt b c =[glue23 b c] P2 b)
    (P31 : Πc a, Ppt a pt c =[glue31 c a] P3 c)
    (a : A) (bc : B ∧ C) : P (smash.mk a bc) :=
  begin
    induction bc with b c b c,
    { exact Ppt a b c },
    { refine transport P _ (Ppt a pt pt), exact ap (smash.mk a) (gluel pt) }, --refine transport P _ (Ppt pt pt pt),
    { refine transport P _ (Ppt a pt pt), exact ap (smash.mk a) (gluer pt) },
    { exact pathover_of_pathover_ap P (smash.mk a) (glue12_over Ppt P1 P12 a b) },
    { exact sorry }
  end

  definition apd_constant' {A : Type} {B : Type} {a a' : A} (p : a = a') {b : B} : apd (λa, b) p = pathover_of_eq p idp :=
  by induction p; reflexivity

definition change_path_eq_of_eq_change_path' {A : Type} {B : A → Type} {a a₂ : A} {p p' : a = a₂} {b : B a} {b₂ : B a₂}
  {r : p = p'} {q : b =[p] b₂} {q' : b =[p'] b₂} : change_path r q = q' → q = change_path r⁻¹ q' :=
begin
  induction r, intro s, exact s
end

definition change_path_eq_of_eq_change_path {A : Type} {B : A → Type} {a a₂ : A} {p p' : a = a₂} {b : B a} {b₂ : B a₂}
  {r : p = p'} {q : b =[p] b₂} {q' : b =[p'] b₂} : change_path r⁻¹ q' = q → q' = change_path r q :=
begin
  induction r, intro s, exact s
end

  definition pathover_hconcato' {A : Type} {B : A → Type} {a₀₀ a₂₀ a₀₂ a₂₂ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/
       {p₀₁ : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/
            {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
            {b₀₀ : B a₀₀} {b₂₀ : B a₂₀}
            {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
            /-b₀₀-/ {q₁₀ : b₀₀ =[p₁₀] b₂₀} /-b₂₀-/
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} /-t₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂}
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ {p : a₀₀ = a₀₂} {sp : p = p₀₁} {q : b₀₀ =[p] b₀₂}
    (r : change_path sp q = q₀₁) (t₁₁ : squareover B (sp ⬝ph s₁₁) q₁₀ q₁₂ q q₂₁) :
    squareover B s₁₁ q₁₀ q₁₂ q₀₁ q₂₁ :=
  by induction sp; induction r; exact t₁₁

  definition pathover_hconcato_right_inv {A : Type} {B : A → Type} {a₀₀ a₂₀ a₀₂ a₀₄ a₂₂ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/
       {p₀₁ : a₀₀ = a₀₂} {p₀₃ : a₀₂ = a₀₄} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/
            {s₁₁ : square p₁₀ p₁₂ (p₀₁ ⬝ p₀₃ ⬝ p₀₃⁻¹) p₂₁}
            {b₀₀ : B a₀₀} {b₂₀ : B a₂₀}
            {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₀₄ : B a₀₄}
            /-b₀₀-/ {q₁₀ : b₀₀ =[p₁₀] b₂₀} /-b₂₀-/
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} {q₀₃ : b₀₂ =[p₀₃] b₀₄} /-t₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂}
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ --{p : a₀₀ = a₀₂} {sp : p = p₀₁} {q : b₀₀ =[p] b₀₂}
    (t₁₁ : squareover B (!con_inv_cancel_right⁻¹ ⬝ph s₁₁) q₁₀ q₁₂ q₀₁ q₂₁) :
    squareover B s₁₁ q₁₀ q₁₂ (q₀₁ ⬝o q₀₃ ⬝o q₀₃⁻¹ᵒ) q₂₁ :=
  begin
    exact sorry
  end


  definition smash3_rec_23 {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (inl3 a b c))
    (P1 : Πa, P (aux1 a)) (P2 : Πb, P (aux2 b)) (P3 : Πc, P (aux3 c))
    (P12 : Πa b, Ppt a b pt =[glue12 a b] P1 a)
    (P23 : Πb c, Ppt pt b c =[glue23 b c] P2 b)
    (P31 : Πc a, Ppt a pt c =[glue31 c a] P3 c) (b : B) (c : C) :
      pathover P (Ppt pt b c) (gluer' (smash.mk b c) (smash.mk' pt pt)) (Ppt pt pt pt) :=
  begin
    refine change_path _ (P23 b c ⬝o ((P23 b pt)⁻¹ᵒ ⬝o P12 pt b) ⬝o (P12 pt pt)⁻¹ᵒ),
    refine whisker_left _ (whisker_right _ !glue2_eq⁻² ⬝ !con.left_inv) ◾ (ap02 _ !con.right_inv ◾ !con.right_inv)⁻² ⬝ _,
    reflexivity
  end

  definition smash3_rec {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (inl3 a b c))
    (P1 : Πa, P (aux1 a)) (P2 : Πb, P (aux2 b)) (P3 : Πc, P (aux3 c))
    (P12 : Πa b, Ppt a b pt =[glue12 a b] P1 a)
    (P23 : Πb c, Ppt pt b c =[glue23 b c] P2 b)
    (P31 : Πc a, Ppt a pt c =[glue31 c a] P3 c)
    (x : A ∧ (B ∧ C)) : P x :=
  begin
    induction x using smash.rec' with a bc a bc,
    { exact smash3_rec_mk Ppt P1 P2 P3 P12 P23 P31 a bc },
    { refine change_path _ (P31 pt a ⬝o (P31 pt pt)⁻¹ᵒ),
      refine (whisker_right _ (ap02 _ !con.right_inv)) ◾ (ap02 _ !con.right_inv ◾ !con.right_inv)⁻² ⬝ _, apply idp_con },
    { induction bc using smash.rec' with b c b c,
      { exact smash3_rec_23 Ppt P1 P2 P3 P12 P23 P31 b c },
      { apply pathover_pathover,
        refine ap (pathover_ap _ _) (!apd_con ⬝ ap011 concato !rec_gluel
          (!apd_inv ⬝ ap inverseo !rec_gluel ⬝ !pathover_of_pathover_ap_invo⁻¹) ⬝ !pathover_of_pathover_ap_cono⁻¹) ⬝pho _,
        refine _ ⬝hop (ap (pathover_ap _ _) !apd_constant')⁻¹,
        refine to_right_inv (pathover_compose P (smash.mk pt) _ _ _) _ ⬝pho _,
        apply squareover_change_path_left,
        refine !change_path_cono⁻¹ ⬝pho _,
        apply squareover_change_path_left,
        refine ap (λx, _ ⬝o x⁻¹ᵒ) !glue12_over_pt_pt ⬝pho _,
        apply pathover_hconcato_right_inv,
        exact sorry },
      { exact sorry }}
  end

/- 3rd attempt, proving an induction principle without the aux-points induction principle for the smash -/

--   definition smash3_rec_mk [unfold 10] {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (smash.mk a (smash.mk b c)))
--     (P12 : Πa b, Ppt a b pt =[glue12 a b] Ppt pt pt pt)
--     (P23 : Πb c, Ppt pt b c =[glue23 b c] Ppt pt pt pt)
--     (P31 : Πc a, Ppt a pt c =[glue31 c a] Ppt pt pt pt)
--     (a : A) (bc : B ∧ C) : P (smash.mk a bc) :=
--   begin
--     induction bc with b c b c,
--     { exact Ppt a b c },
--     { refine transport P _ (Ppt a pt pt), exact ap (smash.mk a) (gluel pt) }, --refine transport P _ (Ppt pt pt pt),
--     { refine transport P _ (Ppt a pt pt), exact ap (smash.mk a) (gluer pt) },
--     { },
--     { exact sorry }
--   end

--   definition smash3_rec {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (smash.mk a (smash.mk b c)))
--     (P12 : Πa b, Ppt a b pt =[glue12 a b] Ppt pt pt pt)
--     (P23 : Πb c, Ppt pt b c =[glue23 b c] Ppt pt pt pt)
--     (P31 : Πc a, Ppt a pt c =[glue31 c a] Ppt pt pt pt)
--     (x : A ∧ (B ∧ C)) : P x :=
--   begin
--     induction x using smash.rec' with a bc a bc,
--     { exact smash3_rec_mk Ppt P12 P23 P31 a bc },
--     { esimp, exact sorry },
--     { induction bc using smash.rec' with b c b c,
--       { refine P23 b c },
--       { apply pathover_pathover,
--         refine ap (pathover_ap _ _) (!apd_con ⬝ ap011 concato !rec_gluel (!apd_inv ⬝ ap inverseo !rec_gluel)) ⬝pho _,
--        refine _ ⬝hop (ap (pathover_ap _ _) !apd_constant')⁻¹,
-- check_expr (natural_square (λ a, gluer' a pt) (gluel' b pt)),
-- },
-- --!rec_gluel (!apd_inv ⬝ ap inverseo !rec_gluel)
--       { }}

--   end

end smash
