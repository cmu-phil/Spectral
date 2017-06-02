-- Authors: Floris van Doorn
-- in collaboration with Egbert, Stefano, Robin, Ulrik

/- the adjunction between the smash product and pointed maps -/
import .smash .susp ..pointed

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function unit sigma susp sphere

namespace smash

  variables {A A' B B' C C' X X' : Type*}

  /- we start by defining the unit of the adjunction -/
  definition pinl [constructor] (A : Type*) {B : Type*} (b : B) : A →* A ∧ B :=
  begin
    fapply pmap.mk,
    { intro a, exact smash.mk a b },
    { exact gluer' b pt }
  end

  definition pinl_phomotopy {b b' : B} (p : b = b') : pinl A b ~* pinl A b' :=
  begin
    fapply phomotopy.mk,
    { exact ap010 (pmap.to_fun ∘ pinl A) p },
    { induction p, apply idp_con }
  end

  definition smash_pmap_unit_pt [constructor] (A B : Type*)
    : pinl A pt ~* pconst A (A ∧ B) :=
  begin
    fconstructor,
    { intro a, exact gluel' a pt },
    { rexact con.right_inv (gluel pt) ⬝ (con.right_inv (gluer pt))⁻¹ }
  end

  /- We chose an unfortunate order of arguments, but it might be bothersome to change it-/
  definition smash_pmap_unit [constructor] (A B : Type*) : B →* ppmap A (A ∧ B) :=
  begin
    fapply pmap.mk,
    { exact pinl A },
    { apply eq_of_phomotopy, exact smash_pmap_unit_pt A B }
  end

  /- The unit is natural in the second argument -/
  definition smash_functor_pid_pinl' [constructor] {A B C : Type*} (b : B) (f : B →* C) :
    pinl A (f b) ~* smash_functor (pid A) f ∘* pinl A b :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity },
    { refine !idp_con ⬝ _,
      induction C with C c₀, induction f with f f₀, esimp at *,
      induction f₀, rexact functor_gluer'2 (@id A) f b pt }
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
      rexact functor_gluer'2_same (pmap_of_map id (Point A)) (pmap_of_map f pt) pt }
  end

  definition smash_pmap_unit_natural (f : B →* C) :
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
      refine ap (λx, _ ⬝* phomotopy_of_eq (x ⬝ _)) !pcompose_left_eq_of_phomotopy ⬝ _,
      refine ap (λx, _ ⬝* x) (!phomotopy_of_eq_con ⬝
               !phomotopy_of_eq_of_phomotopy ◾** !phomotopy_of_eq_of_phomotopy ⬝ !trans_refl) ⬝ _,
      refine _ ⬝ smash_pmap_unit_pt_natural (pmap_of_map f b₀) ⬝ _,
      { exact !trans_refl⁻¹ },
      { exact !refl_trans }}
  end

  /- The counit -/
  definition smash_pmap_counit_map [unfold 3] (af : A ∧ (ppmap A B)) : B :=
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

  /- The counit is natural in both arguments -/
  definition smash_pmap_counit_natural_right (g : B →* C) : g ∘* smash_pmap_counit A B ~*
    smash_pmap_counit A C ∘* smash_functor (pid A) (ppcompose_left g) :=
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
      refine _ ⬝ (ap_is_constant respect_pt _)⁻¹, refine !idp_con⁻¹ }
  end

  definition smash_pmap_counit_natural_left (g : A →* A') :
    smash_pmap_counit A' B ∘* g ∧→ (pid (ppmap A' B)) ~*
    smash_pmap_counit A B ∘* (pid A) ∧→ (ppcompose_right g) :=
  begin
    fapply phomotopy.mk,
    { intro af, induction af with a f a f,
      { reflexivity },
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ (!elim_gluel ⬝ !idp_con) ⬝
          !elim_gluel ⬝ _,
        refine (ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ !elim_gluel ⬝ !ap_con ⬝
          !ap_compose'⁻¹ ◾ !elim_gluel ⬝ !con_idp ⬝ _)⁻¹,
        refine !to_fun_eq_of_phomotopy ⬝ _, reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ !elim_gluer ⬝ !ap_con ⬝
          !ap_compose'⁻¹ ◾ !elim_gluer ⬝ _,
        refine (ap_compose !smash_pmap_counit _ _ ⬝ ap02 _ !elim_gluer ⬝ !ap_con ⬝
          !ap_compose'⁻¹ ◾ !elim_gluer ⬝ !idp_con)⁻¹ }},
    { refine !idp_con ⬝ _, refine !ap_compose'⁻¹ ⬝ _ ⬝ !ap_ap011⁻¹, esimp,
      refine !to_fun_eq_of_phomotopy ⬝ _, exact !ap_constant⁻¹, }
  end

  /- The unit-counit laws -/
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
    { refine _ ⬝ !ap_compose', refine _ ⬝ (ap_is_constant respect_pt _)⁻¹,
      rexact (con.right_inv (gluer pt))⁻¹ }
  end

  definition smash_pmap_counit_unit_pt [constructor] (f : A →* B) :
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
      refine _ ⬝ ap (λx, phomotopy_of_eq (x ⬝ _)) !pcompose_left_eq_of_phomotopy⁻¹,
      refine _ ⬝ !phomotopy_of_eq_con⁻¹,
      refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹ ◾** !phomotopy_of_eq_of_phomotopy⁻¹,
      refine _ ⬝ !trans_refl⁻¹,
      fapply phomotopy_eq,
      { intro a, esimp, refine !elim_gluel'⁻¹ },
      { esimp, refine whisker_right _ !whisker_right_idp ⬝ _ ⬝ !idp_con⁻¹,
        refine whisker_right _ !elim_gluel'_same⁻² ⬝ _ ⬝ !elim_gluer'_same⁻¹⁻²,
        apply inv_con_eq_of_eq_con, refine !idp_con ⬝ _, esimp,
        refine _ ⬝ !ap02_con ⬝ whisker_left _ !ap_inv,
        refine !whisker_right_idp ⬝ _,
        exact !idp_con }}
  end

  /- The underlying (unpointed) functions of the equivalence A →* (B →* C) ≃* A ∧ B →* C) -/
  definition smash_elim [constructor] (f : A →* ppmap B C) : B ∧ A →* C :=
  smash_pmap_counit B C ∘* smash_functor (pid B) f

  definition smash_elim_inv [constructor] (g : A ∧ B →* C) : B →* ppmap A C :=
  ppcompose_left g ∘* smash_pmap_unit A B

  /- They are inverses, constant on the constant function and natural -/
  definition smash_elim_left_inv (f : A →* ppmap B C) : smash_elim_inv (smash_elim f) ~* f :=
  begin
    refine !pwhisker_right !ppcompose_left_pcompose ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !smash_pmap_unit_natural⁻¹* ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !smash_pmap_counit_unit ⬝* _,
    apply pid_pcompose
  end

  definition smash_elim_right_inv (g : A ∧ B →* C) : smash_elim (smash_elim_inv g) ~* g :=
  begin
    refine !pwhisker_left !smash_functor_pid_pcompose ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !smash_pmap_counit_natural_right⁻¹* ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !smash_pmap_unit_counit ⬝* _,
    apply pcompose_pid
  end

  definition smash_elim_pconst (A B C : Type*) :
    smash_elim (pconst B (ppmap A C)) ~* pconst (A ∧ B) C :=
  begin
    refine pwhisker_left _ (smash_functor_pconst_right (pid A)) ⬝* !pcompose_pconst
  end

  definition smash_elim_inv_pconst (A B C : Type*) :
    smash_elim_inv (pconst (A ∧ B) C) ~* pconst B (ppmap A C) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro f, apply pconst_pcompose },
    { esimp, refine !trans_refl ⬝ _,
      refine _ ⬝ (!phomotopy_of_eq_con ⬝ (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝
        !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply pconst_pcompose_phomotopy_pconst }
  end

  definition smash_elim_natural_right {A B C C' : Type*} (f : C →* C')
    (g : B →* ppmap A C) : f ∘* smash_elim g ~* smash_elim (ppcompose_left f ∘* g) :=
  begin
    refine _ ⬝* pwhisker_left _ !smash_functor_pid_pcompose⁻¹*,
    refine !passoc⁻¹* ⬝* pwhisker_right _ _ ⬝* !passoc,
    apply smash_pmap_counit_natural_right
  end

  definition smash_elim_inv_natural_right {A B C C' : Type*} (f : C →* C')
    (g : A ∧ B →* C) : ppcompose_left f ∘* smash_elim_inv g ~* smash_elim_inv (f ∘* g) :=
  begin
    refine !passoc⁻¹* ⬝* pwhisker_right _ _,
    exact !ppcompose_left_pcompose⁻¹*
  end

  definition smash_elim_natural_left (f : A →* A') (g : B →* B')
    (h : B' →* ppmap A' C) : smash_elim h ∘* (f ∧→ g) ~* smash_elim (ppcompose_right f ∘* h ∘* g) :=
  begin
    refine !smash_functor_pid_pcompose ⬝ph* _,
    refine _ ⬝v* !smash_pmap_counit_natural_left,
    refine smash_functor_psquare (pvrefl f) !pid_pcompose⁻¹*
  end

  definition smash_elim_phomotopy {f f' : A →* ppmap B C}
    (p : f ~* f') : smash_elim f ~* smash_elim f' :=
  begin
    apply pwhisker_left,
    exact smash_functor_phomotopy phomotopy.rfl p
  end

  definition smash_elim_inv_phomotopy {f f' : A ∧ B →* C}
    (p : f ~* f') : smash_elim_inv f ~* smash_elim_inv f' :=
  pwhisker_right _ (ppcompose_left_phomotopy p)

  definition smash_elim_eq_of_phomotopy {f f' : A →* ppmap B C}
    (p : f ~* f') : ap smash_elim (eq_of_phomotopy p) = eq_of_phomotopy (smash_elim_phomotopy p) :=
  begin
    induction p using phomotopy_rec_on_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
    refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
    apply ap eq_of_phomotopy,
    refine _ ⬝ ap (pwhisker_left _) !smash_functor_phomotopy_refl⁻¹,
    refine !pwhisker_left_refl⁻¹
  end

  definition smash_elim_inv_eq_of_phomotopy {f f' : A ∧ B →* C} (p : f ~* f') :
    ap smash_elim_inv (eq_of_phomotopy p) = eq_of_phomotopy (smash_elim_inv_phomotopy p) :=
  begin
    induction p using phomotopy_rec_on_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ _,
    refine !eq_of_phomotopy_refl⁻¹ ⬝ _,
    apply ap eq_of_phomotopy,
    refine _ ⬝ ap (pwhisker_right _) !ppcompose_left_phomotopy_refl⁻¹,
    refine !pwhisker_right_refl⁻¹
  end

  /- The pointed maps of the equivalence A →* (B →* C) ≃* A ∧ B →* C -/
  definition smash_pelim [constructor] (A B C : Type*) : ppmap A (ppmap B C) →* ppmap (B ∧ A) C :=
  ppcompose_left (smash_pmap_counit B C) ∘* smash_functor_right B A (ppmap B C)

  definition smash_pelim_inv [constructor] (A B C : Type*) :
    ppmap (B ∧ A) C →* ppmap A (ppmap B C) :=
  pmap.mk smash_elim_inv (eq_of_phomotopy !smash_elim_inv_pconst)

  /- The forward function is natural in all three arguments -/
  definition smash_pelim_natural_right (f : C →* C') :
    psquare (smash_pelim A B C) (smash_pelim A B C')
            (ppcompose_left (ppcompose_left f)) (ppcompose_left f) :=
  smash_functor_right_natural_right (ppcompose_left f) ⬝h*
  ppcompose_left_psquare (smash_pmap_counit_natural_right f)

  definition smash_pelim_natural_left (B C : Type*) (f : A' →* A) :
    psquare (smash_pelim A B C) (smash_pelim A' B C)
            (ppcompose_right f) (ppcompose_right (pid B ∧→ f)) :=
  smash_functor_right_natural_middle f ⬝h* !ppcompose_left_ppcompose_right

  definition smash_pelim_natural_middle (A C : Type*) (g : B' →* B) :
    psquare (smash_pelim A B C) (smash_pelim A B' C)
            (ppcompose_left (ppcompose_right g)) (ppcompose_right (g ∧→ pid A)) :=
  pwhisker_tl _ !ppcompose_left_ppcompose_right ⬝*
  (!smash_functor_right_natural_left⁻¹* ⬝pv*
  smash_functor_right_natural_right (ppcompose_right g) ⬝h*
  ppcompose_left_psquare !smash_pmap_counit_natural_left)

  definition smash_pelim_natural_lm (C : Type*) (f : A' →* A) (g : B' →* B) :
    psquare (smash_pelim A B C) (smash_pelim A' B' C)
            (ppcompose_left (ppcompose_right g) ∘* ppcompose_right f) (ppcompose_right (g ∧→ f)) :=
  smash_pelim_natural_left B C f ⬝v* smash_pelim_natural_middle A' C g ⬝hp*
  ppcompose_right_phomotopy proof !smash_functor_split qed ⬝* !ppcompose_right_pcompose

  /- The equivalence (note: the forward function of smash_adjoint_pmap is smash_pelim_inv) -/
  definition is_equiv_smash_elim [constructor] (A B C : Type*) : is_equiv (@smash_elim A B C) :=
  begin
    fapply adjointify,
    { exact smash_elim_inv },
    { intro g, apply eq_of_phomotopy, exact smash_elim_right_inv g },
    { intro f, apply eq_of_phomotopy, exact smash_elim_left_inv f }
  end

  definition smash_adjoint_pmap_inv [constructor] (A B C : Type*) :
    ppmap B (ppmap A C) ≃* ppmap (A ∧ B) C :=
  pequiv_of_pmap (smash_pelim B A C) (is_equiv_smash_elim B A C)

  definition smash_adjoint_pmap [constructor] (A B C : Type*) :
    ppmap (A ∧ B) C ≃* ppmap B (ppmap A C) :=
  (smash_adjoint_pmap_inv A B C)⁻¹ᵉ*

  /- The naturality of the equivalence is a direct consequence of the earlier naturalities -/
  definition smash_adjoint_pmap_natural_right_pt {A B C C' : Type*} (f : C →* C') (g : A ∧ B →* C) :
    ppcompose_left f ∘* smash_adjoint_pmap A B C g ~* smash_adjoint_pmap A B C' (f ∘* g) :=
  begin
    refine !passoc⁻¹* ⬝* pwhisker_right _ _,
    exact !ppcompose_left_pcompose⁻¹*
  end

  definition smash_adjoint_pmap_inv_natural_right_pt {A B C C' : Type*} (f : C →* C')
    (g : B →* ppmap A C) : f ∘* (smash_adjoint_pmap A B C)⁻¹ᵉ* g ~*
    (smash_adjoint_pmap A B C')⁻¹ᵉ* (ppcompose_left f ∘* g) :=
  begin
    refine _ ⬝* pwhisker_left _ !smash_functor_pid_pcompose⁻¹*,
    refine !passoc⁻¹* ⬝* pwhisker_right _ _ ⬝* !passoc,
    apply smash_pmap_counit_natural_right
  end

   definition smash_adjoint_pmap_inv_natural_right [constructor] {A B C C' : Type*} (f : C →* C') :
    ppcompose_left f ∘* smash_adjoint_pmap_inv A B C ~*
    smash_adjoint_pmap_inv A B C' ∘* ppcompose_left (ppcompose_left f) :=
  smash_pelim_natural_right f

  definition smash_adjoint_pmap_natural_right [constructor] {A B C C' : Type*} (f : C →* C') :
    ppcompose_left (ppcompose_left f) ∘* smash_adjoint_pmap A B C ~*
    smash_adjoint_pmap A B C' ∘* ppcompose_left f :=
  (smash_adjoint_pmap_inv_natural_right f)⁻¹ʰ*

  definition smash_adjoint_pmap_natural_lm (C : Type*) (f : A →* A') (g : B →* B') :
    psquare (smash_adjoint_pmap A' B' C) (smash_adjoint_pmap A B C)
            (ppcompose_right (f ∧→ g)) (ppcompose_left (ppcompose_right f) ∘* ppcompose_right g) :=
  (smash_pelim_natural_lm C g f)⁻¹ʰ*

  /- Corollary: associativity of smash -/

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

  definition smash_assoc_elim_natural_right (A B C : Type*) (f : X →* X') :
    psquare (smash_assoc_elim_equiv A B C X) (smash_assoc_elim_equiv A B C X')
            (ppcompose_left f) (ppcompose_left f) :=
  !smash_adjoint_pmap_natural_right ⬝h*
  !smash_adjoint_pmap_natural_right ⬝h*
  ppcompose_left_psquare !smash_adjoint_pmap_inv_natural_right ⬝h*
  !smash_adjoint_pmap_inv_natural_right

  /-
    We could prove the following two pointed homotopies by applying smash_assoc_elim_natural_right
    to g, but we give a more explicit proof
  -/
  definition smash_assoc_elim_natural_right_pt {A B C X X' : Type*} (f : X →* X')
    (g : A ∧ (B ∧ C) →* X) :
    f ∘* smash_assoc_elim_equiv A B C X g ~* smash_assoc_elim_equiv A B C X' (f ∘* g) :=
  begin
    refine !smash_adjoint_pmap_inv_natural_right_pt ⬝* _,
    apply smash_elim_phomotopy,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !smash_adjoint_pmap_inv_natural_right ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    refine !smash_adjoint_pmap_natural_right_pt ⬝* _,
    apply smash_elim_inv_phomotopy,
    refine !smash_adjoint_pmap_natural_right_pt
  end

  definition smash_assoc_elim_inv_natural_right_pt {A B C X X' : Type*} (f : X →* X')
    (g : (A ∧ B) ∧ C →* X) :
    f ∘* (smash_assoc_elim_equiv A B C X)⁻¹ᵉ* g ~* (smash_assoc_elim_equiv A B C X')⁻¹ᵉ* (f ∘* g) :=
  begin
    refine !smash_adjoint_pmap_inv_natural_right_pt ⬝* _,
    apply smash_elim_phomotopy,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !smash_pmap_counit_natural_right ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    refine !smash_functor_pid_pcompose⁻¹* ⬝* _,
    apply smash_functor_phomotopy phomotopy.rfl,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !smash_adjoint_pmap_natural_right ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    apply smash_elim_inv_natural_right
  end

  definition smash_assoc (A B C : Type*) : A ∧ (B ∧ C) ≃* (A ∧ B) ∧ C :=
  begin
    fapply pequiv.MK2,
    { exact !smash_assoc_elim_equiv⁻¹ᵉ* !pid },
    { exact !smash_assoc_elim_equiv !pid },
    { refine !smash_assoc_elim_inv_natural_right_pt ⬝* _,
      refine pap !smash_assoc_elim_equiv⁻¹ᵉ* !pcompose_pid ⬝* _,
      apply phomotopy_of_eq, apply to_left_inv !smash_assoc_elim_equiv },
    { refine !smash_assoc_elim_natural_right_pt ⬝* _,
      refine pap !smash_assoc_elim_equiv !pcompose_pid ⬝* _,
      apply phomotopy_of_eq, apply to_right_inv !smash_assoc_elim_equiv }
  end

  /- the associativity of smash is natural in all arguments -/
  definition smash_assoc_elim_natural_left (X : Type*)
    (f : A →* A') (g : B →* B') (h : C →* C') :
    psquare (smash_assoc_elim_equiv A' B' C' X) (smash_assoc_elim_equiv A B C X)
            (ppcompose_right (f ∧→ g ∧→ h)) (ppcompose_right ((f ∧→ g) ∧→ h)) :=
  begin
    refine !smash_adjoint_pmap_natural_lm ⬝h* _ ⬝h*
      (!ppcompose_left_ppcompose_right ⬝v* ppcompose_left_psquare !smash_pelim_natural_lm) ⬝h*
      !smash_pelim_natural_lm,
    refine !ppcompose_left_ppcompose_right⁻¹* ⬝ph* _,
    refine _ ⬝hp* pwhisker_right _ (ppcompose_left_phomotopy !ppcompose_left_ppcompose_right⁻¹* ⬝*
      !ppcompose_left_pcompose) ⬝* !passoc ⬝* pwhisker_left _ !ppcompose_left_ppcompose_right⁻¹* ⬝*
      !passoc⁻¹*,
    refine _ ⬝v* !smash_adjoint_pmap_natural_lm,
    refine !smash_adjoint_pmap_natural_right
  end

  definition smash_assoc_natural (f : A →* A') (g : B →* B') (h : C →* C') :
    psquare (smash_assoc A B C) (smash_assoc A' B' C') (f ∧→ (g ∧→ h)) ((f ∧→ g) ∧→ h) :=
  begin
    refine !smash_assoc_elim_inv_natural_right_pt ⬝* _,
    refine pap !smash_assoc_elim_equiv⁻¹ᵉ* (!pcompose_pid ⬝* !pid_pcompose⁻¹*) ⬝* _,
    rexact phomotopy_of_eq ((smash_assoc_elim_natural_left _ f g h)⁻¹ʰ* !pid)⁻¹
  end

  /- Corollary 2: smashing with a suspension -/
  definition smash_psusp_elim_equiv (A B X : Type*) :
    ppmap (A ∧ psusp B) X ≃* ppmap (psusp (A ∧ B)) X :=
  calc
    ppmap (A ∧ psusp B) X ≃* ppmap (psusp B) (ppmap A X) : smash_adjoint_pmap A (psusp B) X
    ... ≃* ppmap B (Ω (ppmap A X)) : psusp_adjoint_loop' B (ppmap A X)
    ... ≃* ppmap B (ppmap A (Ω X)) : pequiv_ppcompose_left (loop_ppmap_commute A X)
    ... ≃* ppmap (A ∧ B) (Ω X) : smash_adjoint_pmap A B (Ω X)
    ... ≃* ppmap (psusp (A ∧ B)) X : psusp_adjoint_loop' (A ∧ B) X

  definition smash_psusp_elim_natural_right (A B : Type*) (f : X →* X') :
    psquare (smash_psusp_elim_equiv A B X) (smash_psusp_elim_equiv A B X')
            (ppcompose_left f) (ppcompose_left f) :=
  smash_adjoint_pmap_natural_right f ⬝h*
  psusp_adjoint_loop_natural_right (ppcompose_left f) ⬝h*
  ppcompose_left_psquare (loop_pmap_commute_natural_right A f) ⬝h*
  (smash_adjoint_pmap_natural_right (Ω→ f))⁻¹ʰ* ⬝h*
  (psusp_adjoint_loop_natural_right f)⁻¹ʰ*

  definition smash_psusp_elim_natural_left (X : Type*) (f : A' →* A) (g : B' →* B) :
    psquare (smash_psusp_elim_equiv A B X) (smash_psusp_elim_equiv A' B' X)
            (ppcompose_right (f ∧→ psusp_functor g)) (ppcompose_right (psusp_functor (f ∧→ g))) :=
  begin
    refine smash_adjoint_pmap_natural_lm X f (psusp_functor g) ⬝h*
           _ ⬝h* _ ⬝h*
           (smash_adjoint_pmap_natural_lm (Ω X) f g)⁻¹ʰ* ⬝h*
           (psusp_adjoint_loop_natural_left (f ∧→ g))⁻¹ʰ*,
    rotate 2,
    exact !ppcompose_left_ppcompose_right ⬝v* ppcompose_left_psquare (loop_pmap_commute_natural_left X f),
    exact psusp_adjoint_loop_natural_left g ⬝v* psusp_adjoint_loop_natural_right (ppcompose_right f)
  end

  definition smash_psusp (A B : Type*) : A ∧ ⅀ B ≃* ⅀(A ∧ B) :=
  begin
    fapply pequiv.MK2,
    { exact !smash_psusp_elim_equiv⁻¹ᵉ* !pid },
    { exact !smash_psusp_elim_equiv !pid },
    { refine phomotopy_of_eq (!smash_psusp_elim_natural_right⁻¹ʰ* _) ⬝* _,
      refine pap !smash_psusp_elim_equiv⁻¹ᵉ* !pcompose_pid ⬝* _,
      apply phomotopy_of_eq, apply to_left_inv !smash_psusp_elim_equiv },
    { refine phomotopy_of_eq (!smash_psusp_elim_natural_right _) ⬝* _,
      refine pap !smash_psusp_elim_equiv !pcompose_pid ⬝* _,
      apply phomotopy_of_eq, apply to_right_inv !smash_psusp_elim_equiv }
  end

  definition smash_psusp_natural (f : A →* A') (g : B →* B') :
    psquare (smash_psusp A B) (smash_psusp A' B') (f ∧→ (psusp_functor g)) (psusp_functor (f ∧→ g)) :=
  begin
    refine phomotopy_of_eq (!smash_psusp_elim_natural_right⁻¹ʰ* _) ⬝* _,
    refine pap !smash_psusp_elim_equiv⁻¹ᵉ* (!pcompose_pid ⬝* !pid_pcompose⁻¹*) ⬝* _,
    rexact phomotopy_of_eq ((smash_psusp_elim_natural_left _ f g)⁻¹ʰ* !pid)⁻¹
  end

  definition smash_iterate_psusp (n : ℕ) (A B : Type*) : A ∧ iterate_psusp n B ≃* iterate_psusp n (A ∧ B) :=
  begin
    induction n with n e,
    { reflexivity },
    { exact smash_psusp A (iterate_psusp n B) ⬝e* psusp_pequiv e }
  end

  definition smash_sphere (A : Type*) (n : ℕ) : A ∧ psphere n ≃* iterate_psusp n A :=
  smash_pequiv pequiv.rfl (psphere_pequiv_iterate_psusp n) ⬝e*
  smash_iterate_psusp n A pbool ⬝e*
  iterate_psusp_pequiv n (smash_pbool_pequiv A)

  definition sphere_smash_sphere (n m : ℕ) : psphere n ∧ psphere m ≃* psphere (n+m) :=
  smash_sphere (psphere n) m ⬝e*
  iterate_psusp_pequiv m (psphere_pequiv_iterate_psusp n) ⬝e*
  iterate_psusp_iterate_psusp_rev m n pbool ⬝e*
  (psphere_pequiv_iterate_psusp (n + m))⁻¹ᵉ*

end smash
