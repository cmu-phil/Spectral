-- Authors: Floris van Doorn
-- in collaboration with Egbert, Stefano, Robin, Ulrik


import .smash

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function red_susp unit sigma


namespace smash

  variables {A B C : Type*}

  definition pinl [constructor] (A : Type*) {B : Type*} (b : B) : A →* A ∧ B :=
  begin
    fapply pmap.mk,
    { intro a, exact smash.mk a b },
    { exact gluer' b pt }
  end

  definition pinl_phomotopy {A B : Type*} {b b' : B} (p : b = b') : pinl A b ~* pinl A b' :=
  begin
    fapply phomotopy.mk,
    { exact ap010 (pmap.to_fun ∘ pinl A) p },
    { induction p, apply idp_con }
  end

  definition pinr [constructor] {A : Type*} (B : Type*) (a : A) : B →* A ∧ B :=
  begin
    fapply pmap.mk,
    { intro b, exact smash.mk a b },
    { exact gluel' a pt }
  end

  definition smash_pmap_unit_pt [constructor] (A B : Type*)
    : pinl A pt ~* pconst A (A ∧ B) :=
  begin
    fconstructor,
    { intro a, exact gluel' a pt },
    { rexact con.right_inv (gluel pt) ⬝ (con.right_inv (gluer pt))⁻¹ }
  end

  definition smash_pmap_unit [constructor] (A B : Type*) : B →* ppmap A (A ∧ B) :=
  begin
    fapply pmap.mk,
    { exact pinl A },
    { apply eq_of_phomotopy, exact smash_pmap_unit_pt A B }
  end

  definition smash_functor_pid_gluer' (A : Type*) {B C : Type*} (b : B) (f : B →* C) :
    ap (smash_functor (pid A) f) (gluer' b pt) = gluer' (f b) (f pt) :=
  begin
    rexact functor_gluer'2 (@id A) f b pt
  end

  definition smash_functor_pid_pinl' [constructor] {A B C : Type*} (b : B) (f : B →* C) :
    pinl A (f b) ~* smash_functor (pid A) f ∘* pinl A b :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity },
    { refine !idp_con ⬝ _,
      induction C with C c₀, induction f with f f₀, esimp at *,
      induction f₀, rexact smash_functor_pid_gluer' A b (pmap_of_map f pt) }
  end

  definition smash_pmap_unit_pt_natural [constructor] (f : B →* C) :
    smash_functor_pid_pinl' pt f ⬝*
      pwhisker_left (smash_functor (pid A) f) (smash_pmap_unit_pt A B) ⬝*
      pcompose_pconst (smash_functor (pid A) f) =
      pinl_phomotopy (respect_pt f) ⬝* smash_pmap_unit_pt A C :=
  begin
    induction f with f f₀, induction C with C c₀, esimp at *,
    induction f₀, refine _ ⬝ !refl_trans⁻¹,
    refine !trans_refl ⬝ _,
    fapply phomotopy_eq',
    { intro a, refine !idp_con ⬝ _,
      rexact functor_gluel'2 (pid A) f a pt },
    { refine whisker_right_idp _ ⬝ph _,
      refine ap (λx, _ ⬝ x) _ ⬝ph _,
      rotate 1, rexact (functor_gluel'2_same (pid A) f pt),
      -- refine whisker_left _ (!con.assoc ⬝ whisker_left _ !con.left_inv ⬝ !con_idp) ⬝ph _,
      refine whisker_right _ !idp_con ⬝pv _,
      refine !con.assoc⁻¹ ⬝ph _, apply whisker_bl,
      refine !con.assoc⁻¹ ⬝ whisker_right _ _ ⬝pv _,
      rotate 1, esimp, apply whisker_left_idp_con,
      refine !con.assoc ⬝pv _, apply whisker_tl,
      refine whisker_right _ !idp_con ⬝pv _,
      refine whisker_right _ !whisker_right_idp ⬝pv _,
      refine whisker_right _ (!idp_con ⬝ !ap02_con) ⬝ !con.assoc ⬝pv _,
      apply whisker_tl,
      apply vdeg_square,
      refine whisker_right _ !ap_inv ⬝ _, apply inv_con_eq_of_eq_con,
      unfold [smash_functor_pid_gluer'],
      rexact functor_gluer'2_same (pmap_of_map id (Point A)) (pmap_of_map f pt) pt }
  end

  definition smash_pmap_unit_natural {A B C : Type*} (f : B →* C) :
    smash_pmap_unit A C ∘* f ~*
    ppcompose_left (smash_functor (pid A) f) ∘* smash_pmap_unit A B :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀,
    induction f with f f₀, esimp at *, induction f₀, fapply phomotopy_mk_ppmap,
    { esimp [pcompose], intro b, exact smash_functor_pid_pinl' b (pmap_of_map f b₀) },
    { refine ap (λx, _ ⬝* phomotopy_of_eq x) !respect_pt_pcompose ⬝ _
           ⬝ ap phomotopy_of_eq !respect_pt_pcompose⁻¹,
      esimp, refine _ ⬝ ap phomotopy_of_eq !idp_con⁻¹,
      refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      refine ap (λx, _ ⬝* phomotopy_of_eq (x ⬝ _)) !pcompose_eq_of_phomotopy ⬝ _,
      refine ap (λx, _ ⬝* x) (!phomotopy_of_eq_con ⬝
               ap011 phomotopy.trans !phomotopy_of_eq_of_phomotopy
                 !phomotopy_of_eq_of_phomotopy ⬝ !trans_refl) ⬝ _,
      refine _ ⬝ smash_pmap_unit_pt_natural (pmap_of_map f b₀) ⬝ _,
      { exact !trans_refl⁻¹ },
      { exact !refl_trans }}
  end

  definition smash_pmap_counit_map [unfold 3] {A B : Type*} (af : A ∧ (ppmap A B)) : B :=
  begin
    induction af with a f a f,
    { exact f a },
    { exact pt },
    { exact pt },
    { reflexivity },
    { exact respect_pt f }
  end

  definition smash_pmap_counit [constructor] (A B : Type*) : A ∧ (ppmap A B) →* B :=
  begin
    fapply pmap.mk,
    { exact smash_pmap_counit_map },
    { reflexivity }
  end

  definition smash_pmap_counit_natural {A B C : Type*} (g : B →* C) :
    g ∘* smash_pmap_counit A B ~* smash_pmap_counit A C ∘* smash_functor (pid A) (ppcompose_left g) :=
  begin
    symmetry,
    fapply phomotopy.mk,
    { intro af, induction af with a f a f,
      { reflexivity },
      { exact (respect_pt g)⁻¹ },
      { exact (respect_pt g)⁻¹ },
      { apply eq_pathover,
        refine ap_compose (smash_pmap_counit A C) _ _ ⬝ph _ ⬝hp (ap_compose g _ _)⁻¹,
        refine ap02 _ !functor_gluel ⬝ph _ ⬝hp ap02 _ !elim_gluel⁻¹,
        refine !ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_gluel ⬝ph _⁻¹ʰ,
        apply square_of_eq_bot, refine !idp_con ⬝ _,
        induction C with C c₀, induction g with g g₀, esimp at *,
        induction g₀, refine ap02 _ !eq_of_phomotopy_refl },
      { apply eq_pathover,
        refine ap_compose (smash_pmap_counit A C) _ _ ⬝ph _ ⬝hp (ap_compose g _ _)⁻¹,
        refine ap02 _ !functor_gluer ⬝ph _ ⬝hp ap02 _ !elim_gluer⁻¹,
        refine !ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_gluer ⬝ph _,
        refine !idp_con ⬝ph _, apply square_of_eq,
        refine !idp_con ⬝ !con_inv_cancel_right⁻¹ }},
    { refine !idp_con ⬝ !idp_con ⬝ _, refine _ ⬝ !ap_compose',
      refine _ ⬝ !ap_prod_elim⁻¹, esimp,
      refine _ ⬝ (ap_is_constant respect_pt _)⁻¹, refine !idp_con⁻¹ }
  end

  definition smash_pmap_unit_counit (A B : Type*) :
    smash_pmap_counit A (A ∧ B) ∘* smash_functor (pid A) (smash_pmap_unit A B) ~* pid (A ∧ B) :=
  begin
    fconstructor,
    { intro x,
      induction x with a b a b,
      { reflexivity },
      { exact gluel pt },
      { exact gluer pt },
      { apply eq_pathover_id_right,
        refine ap_compose smash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluel ⬝ph _,
        refine !ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_gluel ⬝ph _,
        refine !ap_eq_of_phomotopy ⬝ph _,
        apply square_of_eq, refine !idp_con ⬝ !inv_con_cancel_right⁻¹ },
      { apply eq_pathover_id_right,
        refine ap_compose smash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluer ⬝ph _,
        refine !ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_gluer ⬝ph _,
        refine !idp_con ⬝ph _,
        apply square_of_eq, refine !idp_con ⬝ !inv_con_cancel_right⁻¹ }},
    { refine _ ⬝ !ap_compose',
      refine _ ⬝ !ap_prod_elim⁻¹, refine _ ⬝ (ap_is_constant respect_pt _)⁻¹,
      rexact (con.right_inv (gluer pt))⁻¹ }
  end

  definition smash_pmap_counit_unit_pt [constructor] {A B : Type*} (f : A →* B) :
    smash_pmap_counit A B ∘* pinl A f ~* f :=
  begin
    fconstructor,
    { intro a, reflexivity },
    { refine !idp_con ⬝ !elim_gluer'⁻¹ }
  end

  definition smash_pmap_counit_unit (A B : Type*) :
    ppcompose_left (smash_pmap_counit A B) ∘* smash_pmap_unit A (ppmap A B) ~* pid (ppmap A B) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro f, exact smash_pmap_counit_unit_pt f },
    { refine !trans_refl ⬝ _,
      refine _ ⬝ ap (λx, phomotopy_of_eq (x ⬝ _)) !pcompose_eq_of_phomotopy⁻¹,
      refine _ ⬝ !phomotopy_of_eq_con⁻¹,
      refine _ ⬝ ap011 phomotopy.trans !phomotopy_of_eq_of_phomotopy⁻¹
                   !phomotopy_of_eq_of_phomotopy⁻¹,
      refine _ ⬝ !trans_refl⁻¹,
      fapply phomotopy_eq,
      { intro a, refine !elim_gluel'⁻¹ },
      { esimp, refine whisker_right _ !whisker_right_idp ⬝ _ ⬝ !idp_con⁻¹,
        refine whisker_right _ !elim_gluel'_same⁻² ⬝ _ ⬝ !elim_gluer'_same⁻¹⁻²,
        apply inv_con_eq_of_eq_con, refine !idp_con ⬝ _, esimp,
        refine _ ⬝ !ap02_con ⬝ whisker_left _ !ap_inv,
        refine !whisker_right_idp ⬝ _,
        exact !idp_con }}
  end

  definition smash_elim [constructor] {A B C : Type*} (f : A →* ppmap B C) : B ∧ A →* C :=
  smash_pmap_counit B C ∘* smash_functor (pid B) f

  definition smash_elim_inv [constructor] {A B C : Type*} (g : A ∧ B →* C) : B →* ppmap A C :=
  ppcompose_left g ∘* smash_pmap_unit A B

  definition smash_elim_left_inv {A B C : Type*} (f : A →* ppmap B C) : smash_elim_inv (smash_elim f) ~* f :=
  begin
    refine !pwhisker_right !ppcompose_left_pcompose ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !smash_pmap_unit_natural⁻¹* ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !smash_pmap_counit_unit ⬝* _,
    apply pid_pcompose
  end

  definition smash_elim_right_inv {A B C : Type*} (g : A ∧ B →* C) : smash_elim (smash_elim_inv g) ~* g :=
  begin
    refine !pwhisker_left !smash_functor_pid_pcompose ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !smash_pmap_counit_natural⁻¹* ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !smash_pmap_unit_counit ⬝* _,
    apply pcompose_pid
  end

  definition smash_elim_pconst (A B C : Type*) :
    smash_elim (pconst B (ppmap A C)) ~* pconst (A ∧ B) C :=
  begin
    refine pwhisker_left _ (smash_functor_pconst_right (pid A)) ⬝* !pcompose_pconst
    -- fconstructor,
    -- { intro x, induction x with a b a b,
    --   { reflexivity },
    --   { reflexivity },
    --   { reflexivity },
    --   { apply eq_pathover_constant_right, apply hdeg_square,
    --     refine ap_compose smash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluel ⬝ !ap_con ⬝
    --       !ap_compose'⁻¹ ◾ !elim_gluel},
    --   { apply eq_pathover_constant_right, apply hdeg_square,
    --     refine ap_compose smash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluer ⬝ !ap_con ⬝
    --       !ap_compose'⁻¹ ◾ !elim_gluer }},
    -- { reflexivity }
  end

  definition pconst_pcompose_pconst (A B C : Type*) :
    pconst_pcompose (pconst A B) = pcompose_pconst (pconst B C) :=
  idp

  definition symm_symm {A B : Type*} {f g : A →* B} (p : f ~* g) : p⁻¹*⁻¹* = p :=
  phomotopy_eq (λa, !inv_inv)
    begin
      induction p using phomotopy_rec_on_idp, induction f with f f₀, induction B with B b₀, esimp at *,
      induction f₀, esimp,
    end

  definition pconst_pcompose_phomotopy_pconst {A B C : Type*} {f : A →* B} (p : f ~* pconst A B) :
    pconst_pcompose f = pwhisker_left (pconst B C) p ⬝* pcompose_pconst (pconst B C) :=
  begin
    assert H : Π(p : pconst A B ~* f),
      pconst_pcompose f = pwhisker_left (pconst B C) p⁻¹* ⬝* pcompose_pconst (pconst B C),
    { intro p, induction p using phomotopy_rec_on_idp, reflexivity },
    refine H p⁻¹* ⬝ ap (pwhisker_left _) !symm_symm ◾** idp,
  end

  definition smash_elim_inv_pconst (A B C : Type*) :
    smash_elim_inv (pconst (A ∧ B) C) ~* pconst B (ppmap A C) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro f, apply pconst_pcompose },
    { esimp, refine !trans_refl ⬝ _,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply pconst_pcompose_phomotopy_pconst }
  end

  definition smash_elim_natural {A B C C' : Type*} (f : C →* C')
    (g : B →* ppmap A C) : f ∘* smash_elim g ~* smash_elim (ppcompose_left f ∘* g) :=
  begin
    refine _ ⬝* pwhisker_left _ !smash_functor_pid_pcompose⁻¹*,
    refine !passoc⁻¹* ⬝* pwhisker_right _ _ ⬝* !passoc,
    apply smash_pmap_counit_natural
  end

  definition smash_elim_inv_natural {A B C C' : Type*} (f : C →* C')
    (g : A ∧ B →* C) : ppcompose_left f ∘* smash_elim_inv g ~* smash_elim_inv (f ∘* g) :=
  begin
    refine !passoc⁻¹* ⬝* pwhisker_right _ _,
    exact !ppcompose_left_pcompose⁻¹*
  end

  definition smash_elim_phomotopy {A B C : Type*} {f f' : A →* ppmap B C}
    (p : f ~* f') : smash_elim f ~* smash_elim f' :=
  begin
    apply pwhisker_left,
    exact smash_functor_phomotopy phomotopy.rfl p
  end

  definition smash_elim_inv_phomotopy {A B C : Type*} {f f' : A ∧ B →* C}
    (p : f ~* f') : smash_elim_inv f ~* smash_elim_inv f' :=
  pwhisker_right _ (ppcompose_left_phomotopy p)

  definition smash_elim_eq_of_phomotopy {A B C : Type*} {f f' : A →* ppmap B C}
    (p : f ~* f') : ap smash_elim (eq_of_phomotopy p) = eq_of_phomotopy (smash_elim_phomotopy p) :=
  begin
    induction p using phomotopy_rec_on_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
    refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
    apply ap eq_of_phomotopy,
    refine _ ⬝ ap (pwhisker_left _) !smash_functor_phomotopy_refl⁻¹,
    refine !pwhisker_left_refl⁻¹
  end

  definition smash_elim_inv_eq_of_phomotopy {A B C : Type*} {f f' : A ∧ B →* C} (p : f ~* f') :
    ap smash_elim_inv (eq_of_phomotopy p) = eq_of_phomotopy (smash_elim_inv_phomotopy p) :=
  begin
    induction p using phomotopy_rec_on_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
    refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
    apply ap eq_of_phomotopy,
    refine _ ⬝ ap (pwhisker_right _) !ppcompose_left_phomotopy_refl⁻¹,
    refine !pwhisker_right_refl⁻¹
  end

  definition smash_pelim [constructor] (A B C : Type*) : ppmap A (ppmap B C) →* ppmap (B ∧ A) C :=
  pmap.mk smash_elim (eq_of_phomotopy !smash_elim_pconst)

  definition smash_pelim_inv [constructor] (A B C : Type*) :
    ppmap (B ∧ A) C →* ppmap A (ppmap B C) :=
  pmap.mk smash_elim_inv (eq_of_phomotopy !smash_elim_inv_pconst)

  theorem smash_elim_natural_pconst {A B C C' : Type*} (f : C →* C') :
    smash_elim_natural f (pconst A (ppmap B C)) ⬝*
   (smash_elim_phomotopy (pcompose_pconst (ppcompose_left f)) ⬝*
    smash_elim_pconst B A C') =
    pwhisker_left f (smash_elim_pconst B A C) ⬝*
    pcompose_pconst f :=
  begin
    refine idp ◾** (!trans_assoc⁻¹ ⬝ (!pwhisker_left_trans⁻¹ ◾** idp)) ⬝ _,
    refine !trans_assoc⁻¹ ⬝ _,
    refine (!trans_assoc ⬝ (idp ◾** (!pwhisker_left_trans⁻¹ ⬝
      ap (pwhisker_left _) (smash_functor_pconst_right_pid_pcompose' (ppcompose_left f))⁻¹ ⬝
      !pwhisker_left_trans))) ◾** idp ⬝ _,
    refine (!trans_assoc⁻¹ ⬝ (!passoc_phomotopy_right⁻¹ʰ** ⬝h**
      !pwhisker_right_pwhisker_left ⬝h** !passoc_phomotopy_right) ◾** idp) ◾** idp ⬝ _,
    refine !trans_assoc ⬝ !trans_assoc ⬝ idp ◾**_ ⬝ !trans_assoc⁻¹ ⬝ !pwhisker_left_trans⁻¹ ◾** idp,
    refine !trans_assoc ⬝ !trans_assoc ⬝ (eq_symm_trans_of_trans_eq _)⁻¹,
    refine !pcompose_pconst_pcompose⁻¹ ⬝ _,
    refine _ ⬝ idp ◾** (!pcompose_pconst_pcompose),
    refine !pcompose_pconst_phomotopy⁻¹
  end

  definition smash_pelim_natural {A B C C' : Type*} (f : C →* C') :
    ppcompose_left f ∘* smash_pelim A B C ~*
    smash_pelim A B C' ∘* ppcompose_left (ppcompose_left f) :=
  begin
    fapply phomotopy_mk_ppmap,
    { exact smash_elim_natural f },
    { esimp,
      refine idp ◾** (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !smash_elim_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy) ⬝ _ ,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      exact smash_elim_natural_pconst f }
  end

  definition smash_adjoint_pmap' [constructor] (A B C : Type*) : B →* ppmap A C ≃ A ∧ B →* C :=
  begin
    fapply equiv.MK,
    { exact smash_elim },
    { exact smash_elim_inv },
    { intro g, apply eq_of_phomotopy, exact smash_elim_right_inv g },
    { intro f, apply eq_of_phomotopy, exact smash_elim_left_inv f }
  end

  definition smash_adjoint_pmap_inv [constructor] (A B C : Type*) :
    ppmap B (ppmap A C) ≃* ppmap (A ∧ B) C :=
  pequiv_of_equiv (smash_adjoint_pmap' A B C) (eq_of_phomotopy (smash_elim_pconst A B C))

  definition smash_adjoint_pmap [constructor] (A B C : Type*) :
    ppmap (A ∧ B) C ≃* ppmap B (ppmap A C) :=
  (smash_adjoint_pmap_inv A B C)⁻¹ᵉ*

  definition smash_adjoint_pmap_natural_pt {A B C C' : Type*} (f : C →* C') (g : A ∧ B →* C) :
    ppcompose_left f ∘* smash_adjoint_pmap A B C g ~* smash_adjoint_pmap A B C' (f ∘* g) :=
  begin
    refine !passoc⁻¹* ⬝* pwhisker_right _ _,
    exact !ppcompose_left_pcompose⁻¹*
  end

  definition smash_adjoint_pmap_inv_natural_pt {A B C C' : Type*} (f : C →* C')
    (g : B →* ppmap A C) : f ∘* (smash_adjoint_pmap A B C)⁻¹ᵉ* g ~*
    (smash_adjoint_pmap A B C')⁻¹ᵉ* (ppcompose_left f ∘* g) :=
  begin
    refine _ ⬝* pwhisker_left _ !smash_functor_pid_pcompose⁻¹*,
    refine !passoc⁻¹* ⬝* pwhisker_right _ _ ⬝* !passoc,
    apply smash_pmap_counit_natural
  end

  definition smash_adjoint_pmap_inv_natural [constructor] {A B C C' : Type*} (f : C →* C') :
    ppcompose_left f ∘* smash_adjoint_pmap_inv A B C ~*
    smash_adjoint_pmap_inv A B C' ∘* ppcompose_left (ppcompose_left f) :=
  smash_pelim_natural f

  definition smash_adjoint_pmap_natural [constructor] {A B C C' : Type*} (f : C →* C') :
    ppcompose_left (ppcompose_left f) ∘* smash_adjoint_pmap A B C ~*
    smash_adjoint_pmap A B C' ∘* ppcompose_left f :=
  (smash_adjoint_pmap_inv_natural f)⁻¹ʰ*

  /- associativity of smash -/

  definition smash_assoc_elim_equiv (A B C X : Type*) :
    ppmap (A ∧ (B ∧ C)) X ≃* ppmap ((A ∧ B) ∧ C) X :=
  calc
    ppmap (A ∧ (B ∧ C)) X ≃* ppmap (B ∧ C) (ppmap A X) : smash_adjoint_pmap A (B ∧ C) X
    ... ≃* ppmap C (ppmap B (ppmap A X)) : smash_adjoint_pmap B C (ppmap A X)
    ... ≃* ppmap C (ppmap (A ∧ B) X) : pequiv_ppcompose_left (smash_adjoint_pmap_inv A B X)
    ... ≃* ppmap ((A ∧ B) ∧ C) X : smash_adjoint_pmap_inv (A ∧ B) C X

  definition smash_assoc_elim_equiv_fn (A B C X : Type*) (f : A ∧ (B ∧ C) →* X) :
    (A ∧ B) ∧ C →* X :=
  smash_elim (ppcompose_left (smash_adjoint_pmap A B X)⁻¹ᵉ* (smash_elim_inv (smash_elim_inv f)))

  definition smash_assoc_elim_natural_pt {A B C X X' : Type*} (f : X →* X') (g : A ∧ (B ∧ C) →* X) :
    f ∘* smash_assoc_elim_equiv A B C X g ~* smash_assoc_elim_equiv A B C X' (f ∘* g) :=
  begin
    refine !smash_adjoint_pmap_inv_natural_pt ⬝* _,
    apply smash_elim_phomotopy,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !smash_adjoint_pmap_inv_natural ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    refine !smash_adjoint_pmap_natural_pt ⬝* _,
    apply smash_elim_inv_phomotopy,
    refine !smash_adjoint_pmap_natural_pt
  end

  definition smash_assoc_elim_inv_natural_pt {A B C X X' : Type*} (f : X →* X')
    (g : (A ∧ B) ∧ C →* X) :
    f ∘* (smash_assoc_elim_equiv A B C X)⁻¹ᵉ* g ~* (smash_assoc_elim_equiv A B C X')⁻¹ᵉ* (f ∘* g) :=
  begin
    refine !smash_adjoint_pmap_inv_natural_pt ⬝* _,
    apply smash_elim_phomotopy,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !smash_pmap_counit_natural ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    refine !smash_functor_pid_pcompose⁻¹* ⬝* _,
    apply smash_functor_phomotopy phomotopy.rfl,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !smash_adjoint_pmap_natural ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    apply smash_elim_inv_natural
  end

  -- TODO: maybe do it without pap / phomotopy_of_eq
  definition smash_assoc (A B C : Type*) : A ∧ (B ∧ C) ≃* (A ∧ B) ∧ C :=
  begin
    fapply pequiv.MK2,
    { exact !smash_assoc_elim_equiv⁻¹ᵉ* !pid },
    { exact !smash_assoc_elim_equiv !pid },
    { refine !smash_assoc_elim_inv_natural_pt ⬝* _,
      refine pap !smash_assoc_elim_equiv⁻¹ᵉ* !pcompose_pid ⬝* _,
      apply phomotopy_of_eq, apply to_left_inv !smash_assoc_elim_equiv },
    { refine !smash_assoc_elim_natural_pt ⬝* _,
      refine pap !smash_assoc_elim_equiv !pcompose_pid ⬝* _,
      apply phomotopy_of_eq, apply to_right_inv !smash_assoc_elim_equiv }
  end

print axioms smash_assoc
end smash
