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
          { },
          { }}}},
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

namespace smash

  variables {A B C : Type*}

  definition glue12 (a : A) (b : B) : smash.mk a (smash.mk b (pt : C)) = pt :=
  ap (smash.mk a) (gluel' b pt) ⬝ gluel' a pt

  definition glue23 (b : B) (c : C) : smash.mk (pt : A) (smash.mk b c) = pt :> (A ∧ (B ∧ C)) :=
  gluer' (smash.mk b c) pt

  definition glue31 (c : C) (a : A) : smash.mk a (smash.mk (pt : B) c) = pt :=
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

  -- definition glue12' (a : A) (b : B) : smash.mk a (smash.mk b (pt : C)) = smash.mk a (pt : B ∧ C) :=
  -- ap (smash.mk a) (gluel' b pt)

  -- definition glue23' (b : B) (c : C) : smash.mk (pt : A) (smash.mk b c) = smash.mk (pt : A) (smash.mk b (pt : C)) :=
  -- gluer' (smash.mk b c) (smash.mk b pt)
print glue12
print gluel'

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

  definition smash3_rec_mk [unfold 10] {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (smash.mk a (smash.mk b c)))
    (P12 : Πa b, Ppt a b pt =[glue12 a b] Ppt pt pt pt)
    (P23 : Πb c, Ppt pt b c =[glue23 b c] Ppt pt pt pt)
    (P31 : Πc a, Ppt a pt c =[glue31 c a] Ppt pt pt pt)
    (a : A) (bc : B ∧ C) : P (smash.mk a bc) :=
  begin
    induction bc with b c b c,
    { exact Ppt a b c },
    { exact sorry }, --refine transport P _ (Ppt pt pt pt),
    { exact sorry },
    { exact sorry },
    { exact sorry }

  end

print glue12
print glue23
print glue31

  definition apd_constant' {A : Type} {B : Type} {a a' : A} (p : a = a') {b : B} : apd (λa, b) p = pathover_of_eq p idp :=
  by induction p; reflexivity

  definition smash3_rec {P : A ∧ (B ∧ C) → Type} (Ppt : Πa b c, P (smash.mk a (smash.mk b c)))
    (P12 : Πa b, Ppt a b pt =[glue12 a b] Ppt pt pt pt)
    (P23 : Πb c, Ppt pt b c =[glue23 b c] Ppt pt pt pt)
    (P31 : Πc a, Ppt a pt c =[glue31 c a] Ppt pt pt pt)
    (x : A ∧ (B ∧ C)) : P x :=
  begin
    induction x using smash.rec' with a bc a bc,
    { exact smash3_rec_mk Ppt P12 P23 P31 a bc },
    { esimp, exact sorry },
    { induction bc using smash.rec' with b c b c,
      { refine P23 b c },
      { apply pathover_pathover,
        refine ap (pathover_ap _ _) (!apd_con ⬝ ap011 concato !rec_gluel (!apd_inv ⬝ ap inverseo !rec_gluel)) ⬝pho _,
--        refine _ ⬝hop (ap (pathover_ap _ _) (!apd_con))⁻¹,

},
--!rec_gluel (!apd_inv ⬝ ap inverseo !rec_gluel)
      { }}

  end
print natural_square
print apd_con
print pathover_pathover
print pathover_ap

end smash
