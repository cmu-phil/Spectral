-- Authors: Floris van Doorn
-- informal proofs in collaboration with Egbert, Stefano, Robin, Ulrik

/- the adjunction between the smash product and pointed maps -/
import .smash .susp ..pointed_pi ..pyoneda

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function unit sigma susp sphere

namespace smash

  variables {A A' B B' C C' X X' : Type*}

  /- we start by defining the unit of the adjunction -/
  definition pinr [constructor] {A : Type*} (B : Type*) (a : A) : B →* A ∧ B :=
  begin
    fapply pmap.mk,
    { intro b, exact smash.mk a b },
    { exact gluel' a pt }
  end

  definition pinr_phomotopy {a a' : A} (p : a = a') : pinr B a ~* pinr B a' :=
  begin
    fapply phomotopy.mk,
    { exact ap010 (pmap.to_fun ∘ pinr B) p },
    { induction p, apply idp_con }
  end

  definition smash_pmap_unit_pt [constructor] (A B : Type*)
    : pinr B pt ~* pconst B (A ∧ B) :=
  begin
    fapply phomotopy.mk,
    { intro b, exact gluer' b pt },
    { rexact con.right_inv (gluer pt) ⬝ (con.right_inv (gluel pt))⁻¹ }
  end

  definition smash_pmap_unit [constructor] (A B : Type*) : A →* ppmap B (A ∧ B) :=
  begin
    fapply pmap.mk,
    { exact pinr B },
    { apply eq_of_phomotopy, exact smash_pmap_unit_pt A B }
  end

  /- The unit is natural in the first argument -/
  definition smash_functor_pid_pinr' [constructor] (B : Type*) (f : A →* A') (a : A) :
    pinr B (f a) ~* smash_functor f (pid B) ∘* pinr B a :=
  begin
    fapply phomotopy.mk,
    { intro b, reflexivity },
    { refine !idp_con ⬝ _,
      induction A' with A' a₀', induction f with f f₀, esimp at *,
      induction f₀, rexact functor_gluel'2 f (@id B) a pt }
  end

  definition smash_pmap_unit_pt_natural [constructor] (B : Type*) (f : A →* A') :
    smash_functor_pid_pinr' B f pt ⬝*
    pwhisker_left (smash_functor f (pid B)) (smash_pmap_unit_pt A B) ⬝*
    pcompose_pconst (f ∧→ (pid B)) =
    pinr_phomotopy (respect_pt f) ⬝* smash_pmap_unit_pt A' B :=
  begin
    induction f with f f₀, induction A' with A' a₀', esimp at *,
    induction f₀, refine _ ⬝ !refl_trans⁻¹,
    refine !trans_refl ⬝ _,
    fapply phomotopy_eq',
    { intro b, refine !idp_con ⬝ _,
      rexact functor_gluer'2 f (pid B) b pt },
    { refine whisker_right_idp _ ⬝ph _,
      refine ap (λx, _ ⬝ x) _ ⬝ph _,
      rotate 1, rexact (functor_gluer'2_same f (pid B) pt),
      refine whisker_right _ !idp_con ⬝pv _,
      refine !con.assoc⁻¹ ⬝ph _, apply whisker_bl,
      refine whisker_left _ !to_homotopy_pt_mk ⬝pv _,
      refine !con.assoc⁻¹ ⬝ whisker_right _ _ ⬝pv _,
      rotate 1, esimp, apply whisker_left_idp_con,
      refine !con.assoc ⬝pv _, apply whisker_tl,
      refine whisker_right _ !idp_con ⬝pv _,
      refine whisker_right _ !whisker_right_idp ⬝pv _,
      refine whisker_right _ (!idp_con ⬝ !ap02_con) ⬝ !con.assoc ⬝pv _,
      apply whisker_tl,
      apply vdeg_square,
      refine whisker_right _ !ap_inv ⬝ _, apply inv_con_eq_of_eq_con,
      rexact functor_gluel'2_same (pmap_of_map f pt) (pmap_of_map id (Point B)) pt }
  end

  definition smash_pmap_unit_natural (B : Type*) (f : A →* A') :
    psquare (smash_pmap_unit A B) (smash_pmap_unit A' B) f (ppcompose_left (f ∧→ pid B)) :=
  begin
    apply ptranspose,
    induction A with A a₀, induction B with B b₀, induction A' with A' a₀',
    induction f with f f₀, esimp at *, induction f₀, fapply phomotopy_mk_ppmap,
    { intro a, exact smash_functor_pid_pinr' _ (pmap_of_map f a₀) a },
    { refine ap (λx, _ ⬝* phomotopy_of_eq x) !respect_pt_pcompose ⬝ _
           ⬝ ap phomotopy_of_eq !respect_pt_pcompose⁻¹,
      esimp, refine _ ⬝ ap phomotopy_of_eq !idp_con⁻¹,
      refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      refine ap (λx, _ ⬝* phomotopy_of_eq (x ⬝ _)) !pcompose_left_eq_of_phomotopy ⬝ _,
      refine ap (λx, _ ⬝* x) (!phomotopy_of_eq_con ⬝
               !phomotopy_of_eq_of_phomotopy ◾** !phomotopy_of_eq_of_phomotopy ⬝ !trans_refl) ⬝ _,
      refine _ ⬝ smash_pmap_unit_pt_natural _ (pmap_of_map f a₀) ⬝ _,
      { exact !trans_refl⁻¹ },
      { exact !refl_trans }}
  end

  /- The unit is also dinatural in the first argument, but that's easier to prove after the adjunction.
     We don't need it for the adjunction -/

  /- The counit -/
  definition smash_pmap_counit_map [unfold 3] (fb : ppmap B C ∧ B) : C :=
  begin
    induction fb with f b f b,
    { exact f b },
    { exact pt },
    { exact pt },
    { exact respect_pt f },
    { reflexivity }
  end

  definition smash_pmap_counit [constructor] (B C : Type*) : ppmap B C ∧ B →* C :=
  begin
    fapply pmap.mk,
    { exact smash_pmap_counit_map },
    { reflexivity }
  end

  /- The counit is natural in both arguments -/
  definition smash_pmap_counit_natural_right (B : Type*) (g : C →* C') :
    psquare (smash_pmap_counit B C) (smash_pmap_counit B C') (ppcompose_left g ∧→ pid B) g :=
  begin
    apply ptranspose,
    fapply phomotopy.mk,
    { intro fb, induction fb with f b f b,
      { reflexivity },
      { exact (respect_pt g)⁻¹ },
      { exact (respect_pt g)⁻¹ },
      { apply eq_pathover,
        refine ap_compose (smash_pmap_counit B C') _ _ ⬝ph _ ⬝hp (ap_compose g _ _)⁻¹,
        refine ap02 _ !functor_gluel ⬝ph _ ⬝hp ap02 _ !elim_gluel⁻¹,
        refine !ap_con ⬝ !ap_compose' ◾ !elim_gluel ⬝ph _,
        refine !idp_con ⬝ph _, apply square_of_eq,
        refine !idp_con ⬝ !con_inv_cancel_right⁻¹ },
      { apply eq_pathover,
        refine ap_compose (smash_pmap_counit B C') _ _ ⬝ph _ ⬝hp (ap_compose g _ _)⁻¹,
        refine ap02 _ !functor_gluer ⬝ph _ ⬝hp ap02 _ !elim_gluer⁻¹,
        refine !ap_con ⬝ !ap_compose' ◾ !elim_gluer ⬝ph _⁻¹ʰ,
        apply square_of_eq_bot, refine !idp_con ⬝ _,
        induction C' with C' c₀', induction g with g g₀, esimp at *,
        induction g₀, refine ap02 _ !eq_of_phomotopy_refl }},
    { refine !idp_con ⬝ !idp_con ⬝ _, refine _ ⬝ !ap_compose,
      refine _ ⬝ (ap_is_constant respect_pt _)⁻¹, refine !idp_con⁻¹ }
  end

  definition smash_pmap_counit_natural_left (C : Type*) (g : B →* B') :
    psquare (pid (ppmap B' C) ∧→ g) (smash_pmap_counit B C)
            (ppcompose_right g ∧→ pid B) (smash_pmap_counit B' C) :=
  begin
    fapply phomotopy.mk,
    { intro af, induction af with a f a f,
      { reflexivity },
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ !elim_gluel ⬝ !ap_con ⬝
          !ap_compose' ◾ !elim_gluel ⬝ _,
        refine (ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ !elim_gluel ⬝ !ap_con ⬝
          !ap_compose' ◾ !elim_gluel ⬝ !idp_con)⁻¹ },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ (!elim_gluer ⬝ !idp_con) ⬝
          !elim_gluer ⬝ _,
        refine (ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ !elim_gluer ⬝ !ap_con ⬝
          !ap_compose' ◾ !elim_gluer ⬝ !con_idp ⬝ _)⁻¹,
        refine !to_fun_eq_of_phomotopy ⬝ _, reflexivity }},
    { refine !idp_con ⬝ _, refine !ap_compose' ⬝ _ ⬝ !ap_ap011⁻¹, esimp,
      refine !to_fun_eq_of_phomotopy ⬝ _, exact !ap_constant⁻¹ }
  end

  /- The unit-counit laws -/
  definition smash_pmap_unit_counit (A B : Type*) :
    smash_pmap_counit B (A ∧ B) ∘* smash_pmap_unit A B ∧→ pid B ~* pid (A ∧ B) :=
  begin
    fapply phomotopy.mk,
    { intro x,
      induction x with a b a b,
      { reflexivity },
      { exact gluel pt },
      { exact gluer pt },
      { apply eq_pathover_id_right,
        refine ap_compose smash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluel ⬝ph _,
        refine !ap_con ⬝ !ap_compose' ◾ !elim_gluel ⬝ph _,
        refine !idp_con ⬝ph _,
        apply square_of_eq, refine !idp_con ⬝ !inv_con_cancel_right⁻¹ },
      { apply eq_pathover_id_right,
        refine ap_compose smash_pmap_counit_map _ _ ⬝ ap02 _ !functor_gluer ⬝ph _,
        refine !ap_con ⬝ !ap_compose' ◾ !elim_gluer ⬝ph _,
        refine !ap_eq_of_phomotopy ⬝ph _,
        apply square_of_eq, refine !idp_con ⬝ !inv_con_cancel_right⁻¹ }},
    { refine _ ⬝ !ap_compose, refine _ ⬝ (ap_is_constant respect_pt _)⁻¹,
         rexact (con.right_inv (gluel pt))⁻¹ }
  end

  definition smash_pmap_counit_unit_pt [constructor] (f : A →* B) :
    smash_pmap_counit A B ∘* pinr A f ~* f :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity },
    { refine !idp_con ⬝ !elim_gluel'⁻¹ }
  end

  definition smash_pmap_counit_unit (A B : Type*) :
    ppcompose_left (smash_pmap_counit A B) ∘* smash_pmap_unit (ppmap A B) A ~* pid (ppmap A B) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro f, exact smash_pmap_counit_unit_pt f },
    { refine !trans_refl ⬝ _,
      refine _ ⬝ ap (λx, phomotopy_of_eq (x ⬝ _)) !pcompose_left_eq_of_phomotopy⁻¹,
      refine _ ⬝ !phomotopy_of_eq_con⁻¹,
      refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹ ◾** !phomotopy_of_eq_of_phomotopy⁻¹,
      refine _ ⬝ !trans_refl⁻¹,
      fapply phomotopy_eq,
      { intro a, esimp, refine !elim_gluer'⁻¹ },
      { esimp, refine whisker_right _ !whisker_right_idp ⬝ _ ⬝ !idp_con⁻¹,
        refine whisker_right _ !elim_gluer'_same⁻² ⬝ _ ⬝ !elim_gluel'_same⁻¹⁻²,
        apply inv_con_eq_of_eq_con, refine !idp_con ⬝ _, esimp,
        refine _ ⬝ !ap02_con ⬝ whisker_left _ !ap_inv,
        refine !whisker_right_idp ⬝ _,
        exact !idp_con }}
  end

  /- The underlying (unpointed) functions of the equivalence A →* (B →* C) ≃* A ∧ B →* C) -/
  definition smash_elim [constructor] (f : A →* ppmap B C) : A ∧ B →* C :=
  smash_pmap_counit B C ∘* f ∧→ pid B

  definition smash_elim_inv [constructor] (g : A ∧ B →* C) : A →* ppmap B C :=
  ppcompose_left g ∘* smash_pmap_unit A B

  /- They are inverses, constant on the constant function and natural -/
  definition smash_elim_left_inv (f : A →* ppmap B C) : smash_elim_inv (smash_elim f) ~* f :=
  begin
    refine !pwhisker_right !ppcompose_left_pcompose ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !smash_pmap_unit_natural ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !smash_pmap_counit_unit ⬝* _,
    apply pid_pcompose
  end

  definition smash_elim_right_inv (g : A ∧ B →* C) : smash_elim (smash_elim_inv g) ~* g :=
  begin
    refine !pwhisker_left !smash_functor_pcompose_pid ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !smash_pmap_counit_natural_right⁻¹* ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !smash_pmap_unit_counit ⬝* _,
    apply pcompose_pid
  end

  definition smash_elim_pconst (A B C : Type*) :
    smash_elim (pconst A (ppmap B C)) ~* pconst (A ∧ B) C :=
  begin
    refine pwhisker_left _ (smash_functor_pconst_left (pid B)) ⬝* !pcompose_pconst
  end

  definition smash_elim_inv_pconst (A B C : Type*) :
    smash_elim_inv (pconst (A ∧ B) C) ~* pconst A (ppmap B C) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro f, apply pconst_pcompose },
    { esimp, refine !trans_refl ⬝ _,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply pconst_pcompose_phomotopy_pconst }
  end

  definition smash_elim_natural_right (f : C →* C') (g : A →* ppmap B C) :
    f ∘* smash_elim g ~* smash_elim (ppcompose_left f ∘* g) :=
  begin
    refine _ ⬝* pwhisker_left _ !smash_functor_pcompose_pid⁻¹*,
    refine !passoc⁻¹* ⬝* pwhisker_right _ _ ⬝* !passoc,
    apply smash_pmap_counit_natural_right
  end

  definition smash_elim_inv_natural_right {A B C C' : Type*} (f : C →* C')
    (g : A ∧ B →* C) : ppcompose_left f ∘* smash_elim_inv g ~* smash_elim_inv (f ∘* g) :=
  begin
    refine !passoc⁻¹* ⬝* pwhisker_right _ _,
    exact !ppcompose_left_pcompose⁻¹*
  end

  definition smash_elim_natural_left (f : A →* A') (g : B →* B') (h : A' →* ppmap B' C) :
    smash_elim h ∘* (f ∧→ g) ~* smash_elim (ppcompose_right g ∘* h ∘* f) :=
  begin
    refine !smash_functor_pcompose_pid ⬝ph* _,
    refine _ ⬝v* !smash_pmap_counit_natural_left,
    refine smash_functor_psquare !pid_pcompose⁻¹* (phrefl g)
  end

  definition smash_elim_phomotopy {f f' : A →* ppmap B C} (p : f ~* f') :
    smash_elim f ~* smash_elim f' :=
  begin
    apply pwhisker_left,
    exact smash_functor_phomotopy p phomotopy.rfl
  end

  definition smash_elim_inv_phomotopy {f f' : A ∧ B →* C} (p : f ~* f') :
    smash_elim_inv f ~* smash_elim_inv f' :=
  pwhisker_right _ (ppcompose_left_phomotopy p)

  definition smash_elim_eq_of_phomotopy {f f' : A →* ppmap B C} (p : f ~* f') :
    ap smash_elim (eq_of_phomotopy p) = eq_of_phomotopy (smash_elim_phomotopy p) :=
  begin
    induction p using phomotopy_rec_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
    refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
    apply ap eq_of_phomotopy,
    refine _ ⬝ ap (pwhisker_left _) !smash_functor_phomotopy_refl⁻¹,
    refine !pwhisker_left_refl⁻¹
  end

  definition smash_elim_inv_eq_of_phomotopy {f f' : A ∧ B →* C} (p : f ~* f') :
    ap smash_elim_inv (eq_of_phomotopy p) = eq_of_phomotopy (smash_elim_inv_phomotopy p) :=
  begin
    induction p using phomotopy_rec_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
    refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
    apply ap eq_of_phomotopy,
    refine _ ⬝ ap (pwhisker_right _) !ppcompose_left_phomotopy_refl⁻¹,
    refine !pwhisker_right_refl⁻¹
  end

  /- The pointed maps of the equivalence A →* (B →* C) ≃* A ∧ B →* C -/
  definition smash_pelim (A B C : Type*) : ppmap A (ppmap B C) →* ppmap (A ∧ B) C :=
  ppcompose_left (smash_pmap_counit B C) ∘* smash_functor_left A (ppmap B C) B

  definition smash_pelim_inv (A B C : Type*) :
    ppmap (A ∧ B) C →* ppmap A (ppmap B C) :=
  pmap.mk smash_elim_inv (eq_of_phomotopy !smash_elim_inv_pconst)

  /- The forward function is natural in all three arguments -/
  definition smash_pelim_natural_left (B C : Type*) (f : A' →* A) :
    psquare (smash_pelim A B C) (smash_pelim A' B C)
            (ppcompose_right f) (ppcompose_right (f ∧→ pid B)) :=
  smash_functor_left_natural_left (ppmap B C) B f ⬝h* !ppcompose_left_ppcompose_right

  definition smash_pelim_natural_middle (A C : Type*) (f : B' →* B) :
    psquare (smash_pelim A B C) (smash_pelim A B' C)
            (ppcompose_left (ppcompose_right f)) (ppcompose_right (pid A ∧→ f)) :=
  pwhisker_tl _ !ppcompose_left_ppcompose_right ⬝*
  (!smash_functor_left_natural_right⁻¹* ⬝pv*
  smash_functor_left_natural_middle _ _ (ppcompose_right f) ⬝h*
  ppcompose_left_psquare !smash_pmap_counit_natural_left)

  definition smash_pelim_natural_right (A B : Type*) (f : C →* C') :
    psquare (smash_pelim A B C) (smash_pelim A B C')
            (ppcompose_left (ppcompose_left f)) (ppcompose_left f) :=
  smash_functor_left_natural_middle _ _ (ppcompose_left f) ⬝h*
  ppcompose_left_psquare (smash_pmap_counit_natural_right _ f)

  definition smash_pelim_natural_lm (C : Type*) (f : A' →* A) (g : B' →* B) :
    psquare (smash_pelim A B C) (smash_pelim A' B' C)
            (ppcompose_left (ppcompose_right g) ∘* ppcompose_right f) (ppcompose_right (f ∧→ g)) :=
  smash_pelim_natural_left B C f ⬝v* smash_pelim_natural_middle A' C g ⬝hp*
  ppcompose_right_phomotopy (smash_functor_split f g) ⬝* !ppcompose_right_pcompose

  definition smash_pelim_pid (B C : Type*) :
    smash_pelim (ppmap B C) B C !pid ~* smash_pmap_counit B C :=
  pwhisker_left _ !smash_functor_pid ⬝* !pcompose_pid

  definition smash_pelim_inv_pid (A B : Type*) :
    smash_pelim_inv A B (A ∧ B) !pid ~* smash_pmap_unit A B :=
  pwhisker_right _ !ppcompose_left_pid ⬝* !pid_pcompose

  /- The equivalence (note: the forward function of smash_adjoint_pmap is smash_pelim_inv) -/
  definition is_equiv_smash_elim [constructor] (A B C : Type*) : is_equiv (@smash_elim A B C) :=
  begin
    fapply adjointify,
    { exact smash_elim_inv },
    { intro g, apply eq_of_phomotopy, exact smash_elim_right_inv g },
    { intro f, apply eq_of_phomotopy, exact smash_elim_left_inv f }
  end

  definition smash_adjoint_pmap_inv [constructor] (A B C : Type*) :
    ppmap A (ppmap B C) ≃* ppmap (A ∧ B) C :=
  pequiv_of_pmap (smash_pelim A B C) (is_equiv_smash_elim A B C)

  definition smash_adjoint_pmap [constructor] (A B C : Type*) :
    ppmap (A ∧ B) C ≃* ppmap A (ppmap B C) :=
  (smash_adjoint_pmap_inv A B C)⁻¹ᵉ*

  /- The naturality of the equivalence is a direct consequence of the earlier naturalities -/
  definition smash_adjoint_pmap_natural_right_pt {A B C C' : Type*} (f : C →* C') (g : A ∧ B →* C) :
    ppcompose_left f ∘* smash_adjoint_pmap A B C g ~* smash_adjoint_pmap A B C' (f ∘* g) :=
  smash_elim_inv_natural_right f g

  definition smash_adjoint_pmap_inv_natural_right_pt {A B C C' : Type*} (f : C →* C')
    (g : A →* ppmap B C) : f ∘* (smash_adjoint_pmap A B C)⁻¹ᵉ* g ~*
    (smash_adjoint_pmap A B C')⁻¹ᵉ* (ppcompose_left f ∘* g) :=
  smash_elim_natural_right f g

   definition smash_adjoint_pmap_inv_natural_right [constructor] (A B : Type*) (f : C →* C') :
    psquare (smash_adjoint_pmap_inv A B C) (smash_adjoint_pmap_inv A B C')
            (ppcompose_left (ppcompose_left f)) (ppcompose_left f) :=
  smash_pelim_natural_right A B f

  definition smash_adjoint_pmap_natural_right [constructor] (A B : Type*) (f : C →* C') :
    psquare (smash_adjoint_pmap A B C) (smash_adjoint_pmap A B C')
            (ppcompose_left f) (ppcompose_left (ppcompose_left f)) :=
  (smash_adjoint_pmap_inv_natural_right A B f)⁻¹ʰ*

  definition smash_adjoint_pmap_natural_lm (C : Type*) (f : A →* A') (g : B →* B') :
    psquare (smash_adjoint_pmap A' B' C) (smash_adjoint_pmap A B C)
            (ppcompose_right (f ∧→ g)) (ppcompose_left (ppcompose_right g) ∘* ppcompose_right f) :=
  (smash_pelim_natural_lm C f g)⁻¹ʰ*

  /- some naturalities we skipped, but are now easier to prove -/
  definition smash_elim_inv_natural_middle (f : B' →* B)
    (g : A ∧ B →* C) : ppcompose_right f ∘* smash_elim_inv g ~* smash_elim_inv (g ∘* pid A ∧→ f) :=
  !pcompose_pid⁻¹* ⬝* !passoc ⬝* phomotopy_of_eq (smash_adjoint_pmap_natural_lm C (pid A) f g)

  definition smash_pmap_unit_natural_left (f : B →* B') :
    psquare (smash_pmap_unit A B) (ppcompose_right f)
            (smash_pmap_unit A B') (ppcompose_left (pid A ∧→ f)) :=
  begin
    refine pwhisker_left _ !smash_pelim_inv_pid⁻¹* ⬝* _ ⬝* pwhisker_left _ !smash_pelim_inv_pid,
    refine !smash_elim_inv_natural_right ⬝* _ ⬝* !smash_elim_inv_natural_middle⁻¹*,
    refine pap smash_elim_inv (!pcompose_pid ⬝* !pid_pcompose⁻¹*),
  end

  /- Corollary: associativity of smash -/

  definition smash_assoc_elim_pequiv (A B C X : Type*) :
    ppmap (A ∧ (B ∧ C)) X ≃* ppmap ((A ∧ B) ∧ C) X :=
  calc
    ppmap (A ∧ (B ∧ C)) X
        ≃* ppmap A (ppmap (B ∧ C) X)     : smash_adjoint_pmap A (B ∧ C) X
    ... ≃* ppmap A (ppmap B (ppmap C X)) : ppmap_pequiv_ppmap_right (smash_adjoint_pmap B C X)
    ... ≃* ppmap (A ∧ B) (ppmap C X)     : smash_adjoint_pmap_inv A B (ppmap C X)
    ... ≃* ppmap ((A ∧ B) ∧ C) X         : smash_adjoint_pmap_inv (A ∧ B) C X

  -- definition smash_assoc_elim_pequiv_fn (A B C X : Type*) (f : A ∧ (B ∧ C) →* X) :
  --   (A ∧ B) ∧ C →* X :=
  -- smash_elim (ppcompose_left (smash_adjoint_pmap A B X)⁻¹ᵉ* (smash_elim_inv (smash_elim_inv f)))

  definition smash_assoc_elim_natural_left (X : Type*)
    (f : A' →* A) (g : B' →* B) (h : C' →* C) :
    psquare (smash_assoc_elim_pequiv A B C X) (smash_assoc_elim_pequiv A' B' C' X)
            (ppcompose_right (f ∧→ g ∧→ h)) (ppcompose_right ((f ∧→ g) ∧→ h)) :=
  begin
    refine !smash_adjoint_pmap_natural_lm ⬝h*
    (!ppcompose_left_ppcompose_right ⬝v* ppcompose_left_psquare !smash_adjoint_pmap_natural_lm) ⬝h*
    _ ⬝h* !smash_pelim_natural_lm,
    refine pwhisker_right _ (ppcompose_left_phomotopy !ppcompose_left_ppcompose_right⁻¹* ⬝*
      !ppcompose_left_pcompose) ⬝* !passoc ⬝* pwhisker_left _ !ppcompose_left_ppcompose_right⁻¹* ⬝*
      !passoc⁻¹* ⬝ph* _,
    refine _ ⬝hp* !ppcompose_left_ppcompose_right⁻¹*,
    refine !smash_pelim_natural_right ⬝v* !smash_pelim_natural_lm
  end

  definition smash_assoc_elim_natural_right (A B C : Type*) (f : X →* X') :
    psquare (smash_assoc_elim_pequiv A B C X) (smash_assoc_elim_pequiv A B C X')
            (ppcompose_left f) (ppcompose_left f) :=
  !smash_adjoint_pmap_natural_right ⬝h*
  ppcompose_left_psquare !smash_adjoint_pmap_natural_right ⬝h*
  !smash_adjoint_pmap_inv_natural_right ⬝h*
  !smash_adjoint_pmap_inv_natural_right

  definition smash_assoc_elim_natural_right_pt (f : X →* X') (g : A ∧ (B ∧ C) →* X) :
    f ∘* smash_assoc_elim_pequiv A B C X g ~* smash_assoc_elim_pequiv A B C X' (f ∘* g) :=
  begin
    refine !smash_adjoint_pmap_inv_natural_right_pt ⬝* _,
    apply smash_elim_phomotopy,
    refine !smash_adjoint_pmap_inv_natural_right_pt ⬝* _,
    apply smash_elim_phomotopy,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !smash_adjoint_pmap_natural_right ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    refine !smash_adjoint_pmap_natural_right_pt
  end

  definition smash_assoc_elim_inv_natural_right_pt (f : X →* X') (g : (A ∧ B) ∧ C →* X) :
    f ∘* (smash_assoc_elim_pequiv A B C X)⁻¹ᵉ* g ~*
    (smash_assoc_elim_pequiv A B C X')⁻¹ᵉ* (f ∘* g) :=
  phomotopy_of_eq ((smash_assoc_elim_natural_right A B C f)⁻¹ʰ* g)

  definition smash_assoc (A B C : Type*) : (A ∧ B) ∧ C ≃* A ∧ (B ∧ C) :=
  pyoneda (smash_assoc_elim_pequiv A B C) (λX X' f, smash_assoc_elim_natural_right A B C f)
  -- begin
  --   fapply pequiv.MK,
  --   { exact !smash_assoc_elim_pequiv !pid },
  --   { exact !smash_assoc_elim_pequiv⁻¹ᵉ* !pid },
  --   { refine !smash_assoc_elim_natural_right_pt ⬝* _,
  --     refine pap !smash_assoc_elim_pequiv !pcompose_pid ⬝* _,
  --     apply phomotopy_of_eq, apply to_right_inv !smash_assoc_elim_pequiv },
  --   { refine !smash_assoc_elim_inv_natural_right_pt ⬝* _,
  --     refine pap !smash_assoc_elim_pequiv⁻¹ᵉ* !pcompose_pid ⬝* _,
  --     apply phomotopy_of_eq, apply to_left_inv !smash_assoc_elim_pequiv }
  -- end

  definition pcompose_smash_assoc {A B C X : Type*} (f : A ∧ (B ∧ C) →* X) :
    f ∘* smash_assoc A B C ~* smash_assoc_elim_pequiv A B C X f :=
  smash_assoc_elim_natural_right_pt f !pid ⬝* pap !smash_assoc_elim_pequiv !pcompose_pid

  definition pcompose_smash_assoc_pinv {A B C X : Type*} (f : (A ∧ B) ∧ C →* X) :
    f ∘* (smash_assoc A B C)⁻¹ᵉ* ~* (smash_assoc_elim_pequiv A B C X)⁻¹ᵉ* f :=
  smash_assoc_elim_inv_natural_right_pt f !pid ⬝* pap !smash_assoc_elim_pequiv⁻¹ᵉ* !pcompose_pid

  /- the associativity of smash is natural in all arguments -/
  definition smash_assoc_natural (f : A →* A') (g : B →* B') (h : C →* C') :
    psquare (smash_assoc A B C) (smash_assoc A' B' C') ((f ∧→ g) ∧→ h) (f ∧→ (g ∧→ h)) :=
  begin
    refine !pcompose_smash_assoc ⬝* _,
    refine pap !smash_assoc_elim_pequiv !pid_pcompose⁻¹* ⬝* _,
    rexact phomotopy_of_eq (smash_assoc_elim_natural_left _ f g h !pid)⁻¹
  end

  /- we prove the pentagon for the associativity -/
  definition smash_assoc_elim_left_pequiv (A B C D X : Type*) :
    ppmap (D ∧ (A ∧ (B ∧ C))) X ≃* ppmap (D ∧ ((A ∧ B) ∧ C)) X :=
  calc     ppmap (D ∧ (A ∧ (B ∧ C))) X
        ≃* ppmap D (ppmap (A ∧ (B ∧ C)) X) : smash_adjoint_pmap D (A ∧ (B ∧ C)) X
    ... ≃* ppmap D (ppmap ((A ∧ B) ∧ C) X) : ppmap_pequiv_ppmap_right (smash_assoc_elim_pequiv A B C X)
    ... ≃* ppmap (D ∧ ((A ∧ B) ∧ C)) X     : smash_adjoint_pmap_inv D ((A ∧ B) ∧ C) X

  definition smash_assoc_elim_right_pequiv (A B C D X : Type*) :
    ppmap ((A ∧ (B ∧ C)) ∧ D) X ≃* ppmap (((A ∧ B) ∧ C) ∧ D) X :=
  calc     ppmap ((A ∧ (B ∧ C)) ∧ D) X
        ≃* ppmap (A ∧ (B ∧ C)) (ppmap D X) : smash_adjoint_pmap (A ∧ (B ∧ C)) D X
    ... ≃* ppmap ((A ∧ B) ∧ C) (ppmap D X) : smash_assoc_elim_pequiv A B C (ppmap D X)
    ... ≃* ppmap (((A ∧ B) ∧ C) ∧ D) X     : smash_adjoint_pmap_inv ((A ∧ B) ∧ C) D X

  definition smash_assoc_elim_right_natural_right (A B C D : Type*) (f : X →* X') :
    psquare (smash_assoc_elim_right_pequiv A B C D X) (smash_assoc_elim_right_pequiv A B C D X')
            (ppcompose_left f) (ppcompose_left f) :=
  smash_adjoint_pmap_natural_right (A ∧ (B ∧ C)) D f ⬝h*
  smash_assoc_elim_natural_right A B C (ppcompose_left f) ⬝h*
  smash_adjoint_pmap_inv_natural_right ((A ∧ B) ∧ C) D f

  definition smash_assoc_smash_functor (A B C D : Type*) :
    smash_assoc A B C ∧→ pid D ~* !smash_assoc_elim_right_pequiv (pid _) :=
  begin
    symmetry,
    refine pap (!smash_adjoint_pmap_inv ∘* !smash_assoc_elim_pequiv) !smash_pelim_inv_pid ⬝* _,
    refine pap !smash_adjoint_pmap_inv !pcompose_smash_assoc⁻¹* ⬝* _,
    refine pwhisker_left _ !smash_functor_pcompose_pid ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    exact pwhisker_right _ !smash_pmap_unit_counit ⬝* !pid_pcompose,
  end

  definition ppcompose_right_smash_assoc (A B C X : Type*) :
    ppcompose_right (smash_assoc A B C) ~* smash_assoc_elim_pequiv A B C X :=
  sorry

  definition smash_functor_smash_assoc (A B C D : Type*) :
    pid A ∧→ smash_assoc B C D ~* !smash_assoc_elim_left_pequiv (pid _) :=
  begin
    symmetry,
    refine pap (!smash_adjoint_pmap_inv ∘* ppcompose_left _) !smash_pelim_inv_pid ⬝* _,
    refine pap !smash_adjoint_pmap_inv (pwhisker_right _ !ppcompose_right_smash_assoc⁻¹* ⬝*
      !smash_pmap_unit_natural_left⁻¹*) ⬝* _,
    refine phomotopy_of_eq (smash_adjoint_pmap_inv_natural_right _ _ (pid A ∧→ smash_assoc B C D)
      !smash_pmap_unit)⁻¹ ⬝* _,
    refine pwhisker_left _ _ ⬝* !pcompose_pid,
    apply smash_pmap_unit_counit
  end

  definition smash_assoc_pentagon (A B C D : Type*) :
    smash_assoc A B (C ∧ D) ∘* smash_assoc (A ∧ B) C D ~*
    pid A ∧→ smash_assoc B C D ∘* smash_assoc A (B ∧ C) D ∘* smash_assoc A B C ∧→ pid D :=
  begin
    refine !pcompose_smash_assoc ⬝* _,
    refine pap (!smash_adjoint_pmap_inv ∘* !smash_adjoint_pmap_inv ∘*
      ppcompose_left !smash_adjoint_pmap)
      (phomotopy_of_eq (to_left_inv !smash_adjoint_pmap_inv _)) ⬝* _,
    refine pap (!smash_adjoint_pmap_inv ∘* !smash_adjoint_pmap_inv)
      (phomotopy_of_eq (!smash_pelim_natural_right _)) ⬝* _,
    symmetry,
    refine !smash_functor_smash_assoc ◾* pwhisker_left _ !smash_assoc_smash_functor ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine phomotopy_of_eq (smash_assoc_elim_right_natural_right A B C D _ _) ⬝*
           pap !smash_assoc_elim_right_pequiv (!pcompose_pid ⬝* !pcompose_smash_assoc) ⬝* _,
    apply phomotopy_of_eq,
    apply ap (!smash_adjoint_pmap_inv ∘ !smash_adjoint_pmap_inv ∘ !smash_adjoint_pmap_inv),
    refine ap (ppcompose_left _ ∘ !smash_adjoint_pmap) (to_left_inv !smash_adjoint_pmap_inv _) ⬝ _,
    refine ap (ppcompose_left _) (to_left_inv !smash_adjoint_pmap_inv _) ⬝ _,
    refine ap (ppcompose_left _ ∘ ppcompose_left _) (to_left_inv !smash_adjoint_pmap_inv _) ⬝ _,
    refine ap (ppcompose_left _) ((ppcompose_left_pcompose _ _ _)⁻¹ ⬝
      ppcompose_left_phomotopy !pinv_pcompose_cancel_left _) ⬝ _,
    refine (ppcompose_left_pcompose _ _ _)⁻¹ ⬝
      ppcompose_left_phomotopy !pinv_pcompose_cancel_left _ ⬝ _,
    exact ppcompose_left_pcompose _ _ _,
  end

  /- Corollary 2: smashing with a suspension -/
  definition smash_susp_elim_pequiv (A B X : Type*) :
    ppmap (⅀ A ∧ B) X ≃* ppmap (⅀ (A ∧ B)) X :=
  calc
    ppmap (⅀ A ∧ B) X ≃* ppmap (⅀ A) (ppmap B X) : smash_adjoint_pmap (⅀ A) B X
    ... ≃* ppmap A (Ω (ppmap B X)) : susp_adjoint_loop A (ppmap B X)
    ... ≃* ppmap A (ppmap B (Ω X)) : ppmap_pequiv_ppmap_right (loop_ppmap_pequiv B X)
    ... ≃* ppmap (A ∧ B) (Ω X) : smash_adjoint_pmap A B (Ω X)
    ... ≃* ppmap (⅀ (A ∧ B)) X : susp_adjoint_loop (A ∧ B) X

  definition smash_susp_elim_natural_right (A B : Type*) (f : X →* X') :
    psquare (smash_susp_elim_pequiv A B X) (smash_susp_elim_pequiv A B X')
            (ppcompose_left f) (ppcompose_left f) :=
  smash_adjoint_pmap_natural_right (⅀ A) B f ⬝h*
  susp_adjoint_loop_natural_right (ppcompose_left f) ⬝h*
  ppcompose_left_psquare (loop_ppmap_pequiv_natural_right B f) ⬝h*
  (smash_adjoint_pmap_natural_right A B (Ω→ f))⁻¹ʰ* ⬝h*
  (susp_adjoint_loop_natural_right f)⁻¹ʰ*

  definition smash_susp_elim_natural_left (X : Type*) (f : A' →* A) (g : B' →* B) :
    psquare (smash_susp_elim_pequiv A B X) (smash_susp_elim_pequiv A' B' X)
            (ppcompose_right (⅀→ f ∧→ g)) (ppcompose_right (susp_functor (f ∧→ g))) :=
  begin
    refine smash_adjoint_pmap_natural_lm X (⅀→ f) g ⬝h*
           _ ⬝h* _ ⬝h*
           (smash_adjoint_pmap_natural_lm (Ω X) f g)⁻¹ʰ* ⬝h*
           (susp_adjoint_loop_natural_left (f ∧→ g))⁻¹ʰ*,
    rotate 2,
    exact !ppcompose_left_ppcompose_right ⬝v*
      ppcompose_left_psquare (loop_ppmap_pequiv_natural_left X g),
    exact susp_adjoint_loop_natural_left f ⬝v* susp_adjoint_loop_natural_right (ppcompose_right g)
  end

  definition susp_smash_rev (A B : Type*) : ⅀ (A ∧ B) ≃* ⅀ A ∧ B :=
  pyoneda (smash_susp_elim_pequiv A B) (λX X' f, smash_susp_elim_natural_right A B f)
  -- begin
  --   fapply pequiv.MK,
  --   { exact !smash_susp_elim_pequiv⁻¹ᵉ* !pid },
  --   { exact !smash_susp_elim_pequiv !pid },
  --   { refine phomotopy_of_eq (!smash_susp_elim_natural_right⁻¹ʰ* _) ⬝* _,
  --     refine pap !smash_susp_elim_pequiv⁻¹ᵉ* !pcompose_pid ⬝* _,
  --     apply phomotopy_of_eq, apply to_left_inv !smash_susp_elim_pequiv },
  --   { refine phomotopy_of_eq (!smash_susp_elim_natural_right _) ⬝* _,
  --     refine pap !smash_susp_elim_pequiv !pcompose_pid ⬝* _,
  --     apply phomotopy_of_eq, apply to_right_inv !smash_susp_elim_pequiv }
  -- end

  definition susp_smash_rev_natural (f : A →* A') (g : B →* B') :
    psquare (susp_smash_rev A B) (susp_smash_rev A' B') (⅀→ (f ∧→ g)) (⅀→ f ∧→ g) :=
  begin
    refine phomotopy_of_eq (smash_susp_elim_natural_right _ _ _ _) ⬝* _,
    refine pap !smash_susp_elim_pequiv (!pcompose_pid ⬝* !pid_pcompose⁻¹*) ⬝* _,
    rexact phomotopy_of_eq (smash_susp_elim_natural_left _ f g !pid)⁻¹
  end

  definition susp_smash (A B : Type*) : ⅀ A ∧ B ≃* ⅀ (A ∧ B) :=
  (susp_smash_rev A B)⁻¹ᵉ*

  definition smash_susp (A B : Type*) : A ∧ ⅀ B ≃* ⅀ (A ∧ B) :=
  calc A ∧ ⅀ B
            ≃* ⅀ B ∧ A  : smash_comm A (⅀ B)
        ... ≃* ⅀(B ∧ A) : susp_smash B A
        ... ≃* ⅀(A ∧ B) : susp_pequiv (smash_comm B A)


  definition smash_susp_natural (f : A →* A') (g : B →* B') :
    psquare (smash_susp A B) (smash_susp A' B') (f ∧→ ⅀→g) (⅀→ (f ∧→ g)) :=
  sorry

  definition susp_smash_move (A B : Type*) : ⅀ A ∧ B ≃* A ∧ ⅀ B :=
  susp_smash A B ⬝e* (smash_susp A B)⁻¹ᵉ*

  definition smash_iterate_susp (n : ℕ) (A B : Type*) :
    A ∧ iterate_susp n B ≃* iterate_susp n (A ∧ B) :=
  begin
    induction n with n e,
    { reflexivity },
    { exact smash_susp A (iterate_susp n B) ⬝e* susp_pequiv e }
  end

  definition smash_sphere (A : Type*) (n : ℕ) : A ∧ sphere n ≃* iterate_susp n A :=
  pequiv.rfl ∧≃ (sphere_pequiv_iterate_susp n) ⬝e*
  smash_iterate_susp n A pbool ⬝e*
  iterate_susp_pequiv n (smash_pbool_pequiv A)

  definition smash_pcircle (A : Type*) : A ∧ S¹* ≃* susp A :=
  smash_sphere A 1

  definition sphere_smash_sphere (n m : ℕ) : sphere n ∧ sphere m ≃* sphere (n+m) :=
  smash_sphere (sphere n) m ⬝e*
  iterate_susp_pequiv m (sphere_pequiv_iterate_susp n) ⬝e*
  iterate_susp_iterate_susp_rev m n pbool ⬝e*
  (sphere_pequiv_iterate_susp (n + m))⁻¹ᵉ*

end smash
