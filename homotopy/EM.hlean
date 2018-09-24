-- Authors: Floris van Doorn

import homotopy.EM algebra.category.functor.equivalence types.pointed2 ..pointed_pi ..pointed
       ..move_to_lib .susp ..algebra.exactness ..univalent_subcategory

open eq equiv is_equiv algebra group nat pointed EM.ops is_trunc trunc susp function is_conn nat
universe variable u
/- TODO: try to fix the compilation time of this file -/


namespace EM

  definition EM1_functor_gid (G : Group) : EM1_functor (gid G) ~* !pid :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square, apply elim_pth, },
      { apply @is_prop.elim, apply is_trunc_pathover }},
    { reflexivity },
  end

  definition EMadd1_functor_gid (G : AbGroup) (n : ℕ) : EMadd1_functor (gid G) n ~* !pid :=
  begin
    induction n with n p,
    { apply EM1_functor_gid },
    { refine !EMadd1_functor_succ ⬝* _,
      refine ptrunc_functor_phomotopy _ (susp_functor_phomotopy p ⬝* !susp_functor_pid) ⬝* _,
      apply ptrunc_functor_pid }
  end

  definition EM_functor_gid (G : AbGroup) (n : ℕ) : EM_functor (gid G) n ~* !pid :=
  begin
    cases n with n,
    { apply pmap_of_homomorphism_gid },
    { apply EMadd1_functor_gid }
  end

  definition EM1_functor_gcompose {G H K : Group} (ψ : H →g K) (φ : G →g H) :
    EM1_functor (ψ ∘g φ) ~* EM1_functor ψ ∘* EM1_functor φ :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square, esimp,
        refine !elim_pth ⬝ _ ⬝ (ap_compose (EM1_functor ψ) _ _)⁻¹,
        refine _ ⬝ ap02 _ !elim_pth⁻¹, exact !elim_pth⁻¹ },
      { apply @is_prop.elim, apply is_trunc_pathover }},
    { reflexivity },
  end

  definition EMadd1_functor_gcompose {G H K : AbGroup} (ψ : H →g K) (φ : G →g H) (n : ℕ) :
    EMadd1_functor (ψ ∘g φ) n ~* EMadd1_functor ψ n ∘* EMadd1_functor φ n :=
  begin
    induction n with n p,
    { apply EM1_functor_gcompose },
    { refine !EMadd1_functor_succ ⬝* _,
      refine ptrunc_functor_phomotopy _ (susp_functor_phomotopy p ⬝* !susp_functor_pcompose) ⬝* _,
      apply ptrunc_functor_pcompose }
  end

  definition EM_functor_gcompose {G H K : AbGroup} (ψ : H →g K) (φ : G →g H) (n : ℕ) :
    EM_functor (ψ ∘g φ) n ~* EM_functor ψ n ∘* EM_functor φ n :=
  begin
    cases n with n,
    { apply pmap_of_homomorphism_gcompose },
    { apply EMadd1_functor_gcompose }
  end

  definition EM1_functor_phomotopy {G H : Group} {φ ψ : G →g H} (p : φ ~ ψ) :
    EM1_functor φ ~* EM1_functor ψ :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square, esimp,
        refine !elim_pth ⬝ _ ⬝ !elim_pth⁻¹, exact ap pth (p g) },
      { apply @is_prop.elim, apply is_trunc_pathover }},
    { reflexivity },
  end

  definition EMadd1_functor_phomotopy {G H : AbGroup} {φ ψ : G →g H} (p : φ ~ ψ) (n : ℕ) :
    EMadd1_functor φ n ~* EMadd1_functor ψ n :=
  begin
    induction n with n q,
    { exact EM1_functor_phomotopy p },
    { exact ptrunc_functor_phomotopy _ (susp_functor_phomotopy q) }
  end

  definition EM_functor_phomotopy {G H : AbGroup} {φ ψ : G →g H} (p : φ ~ ψ) (n : ℕ) :
    EM_functor φ n ~* EM_functor ψ n :=
  begin
    cases n with n,
    { exact pmap_of_homomorphism_phomotopy p },
    { exact EMadd1_functor_phomotopy p n }
  end

  definition EM_equiv_EM [constructor] {G H : AbGroup} (φ : G ≃g H) (n : ℕ) : K G n ≃* K H n :=
  begin
    fapply pequiv.MK',
    { exact EM_functor φ n },
    { exact EM_functor φ⁻¹ᵍ n },
    { intro x, refine (EM_functor_gcompose φ⁻¹ᵍ φ n)⁻¹* x ⬝ _,
      refine _ ⬝ EM_functor_gid G n x,
      refine EM_functor_phomotopy _ n x,
      rexact left_inv φ },
    { intro x, refine (EM_functor_gcompose φ φ⁻¹ᵍ n)⁻¹* x ⬝ _,
      refine _ ⬝ EM_functor_gid H n x,
      refine EM_functor_phomotopy _ n x,
      rexact right_inv φ }
  end

  definition is_equiv_EM_functor [constructor] {G H : AbGroup} (φ : G →g H) [H2 : is_equiv φ]
    (n : ℕ) : is_equiv (EM_functor φ n) :=
  to_is_equiv (EM_equiv_EM (isomorphism.mk φ H2) n)

  definition fundamental_group_EM1' (G : Group) : G ≃g π₁ (EM1 G) :=
  (fundamental_group_EM1 G)⁻¹ᵍ

  definition ghomotopy_group_EMadd1' (G : AbGroup) (n : ℕ) : G ≃g πg[n+1] (EMadd1 G n) :=
  begin
    change G ≃g π₁ (Ω[n] (EMadd1 G n)),
    refine _ ⬝g homotopy_group_isomorphism_of_pequiv 0 (loopn_EMadd1_pequiv_EM1 G n),
    apply fundamental_group_EM1'
  end

  definition homotopy_group_functor_EM1_functor {G H : Group} (φ : G →g H) :
    π→g[1] (EM1_functor φ) ∘ fundamental_group_EM1' G ~ fundamental_group_EM1' H ∘ φ :=
  begin
    intro g, apply ap tr, exact !idp_con ⬝ !elim_pth,
  end

  section

  definition ghomotopy_group_EMadd1'_0 (G : AbGroup) :
    ghomotopy_group_EMadd1' G 0 ~ fundamental_group_EM1' G :=
  begin
    refine _ ⬝hty id_compose _,
    unfold [ghomotopy_group_EMadd1'],
    apply hwhisker_right (fundamental_group_EM1' G),
    refine _ ⬝hty trunc_functor_id _ _,
    exact trunc_functor_homotopy _ ap1_pid,
  end

  definition loopn_EMadd1_pequiv_EM1_succ (G : AbGroup) (n : ℕ) :
    loopn_EMadd1_pequiv_EM1 G (succ n) ~* (loopn_succ_in n (EMadd1 G (succ n)))⁻¹ᵉ* ∘*
      Ω→[n] (loop_EMadd1 G n) ∘* loopn_EMadd1_pequiv_EM1 G n :=
  by reflexivity

  -- definition is_trunc_EMadd1' [instance] (G : AbGroup) (n : ℕ) : is_trunc (succ n) (EMadd1 G n) :=
  -- is_trunc_EMadd1 G n

  definition loop_EMadd1_succ (G : AbGroup) (n : ℕ) :
    loop_EMadd1 G (n+1) ~* (loop_ptrunc_pequiv (n+1+1) (susp (EMadd1 G (n+1))))⁻¹ᵉ* ∘*
    freudenthal_pequiv (add_mul_le_mul_add n 1 1) (EMadd1 G (n+1)) ∘*
    (ptrunc_pequiv (n+1+1) (EMadd1 G (n+1)))⁻¹ᵉ* :=
  by reflexivity

  definition loop_EMadd1_natural {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    psquare (loop_EMadd1 G n) (loop_EMadd1 H n)
            (EMadd1_functor φ n) (Ω→ (EMadd1_functor φ (succ n))) :=
  begin
    refine _ ⬝hp* Ω⇒ !EMadd1_functor_succ,
    induction n with n IH,
    { refine !hopf.to_pmap_delooping_pinv ⬝pv* _ ⬝vp* !hopf.to_pmap_delooping_pinv,
      exact !loop_susp_unit_natural ⬝h* ap1_psquare !ptr_natural },
    { refine !loop_EMadd1_succ ⬝pv* _ ⬝vp* !loop_EMadd1_succ,
      refine _ ⬝h* !ap1_ptrunc_functor,
      refine (@(ptrunc_pequiv_natural (n+1+1) _) _ _)⁻¹ʰ* ⬝h* _,
      refine !to_pmap_freudenthal_pequiv ⬝pv* _ ⬝vp* !to_pmap_freudenthal_pequiv,
      apply ptrunc_functor_psquare,
      exact !loop_susp_unit_natural }
  end

  definition apn_EMadd1_pequiv_EM1_natural {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    psquare (loopn_EMadd1_pequiv_EM1 G n) (loopn_EMadd1_pequiv_EM1 H n)
            (EM1_functor φ) (Ω→[n] (EMadd1_functor φ n)) :=
  begin
    induction n with n IH,
    { exact phomotopy.rfl },
    { refine pwhisker_left _ !loopn_EMadd1_pequiv_EM1_succ ⬝* _,
      refine _ ⬝* pwhisker_right _ !loopn_EMadd1_pequiv_EM1_succ⁻¹*,
      refine _ ⬝h* !loopn_succ_in_inv_natural,
      exact IH ⬝h* (apn_psquare n !loop_EMadd1_natural) }
  end

  definition homotopy_group_functor_EMadd1_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    hsquare (ghomotopy_group_EMadd1' G n) (ghomotopy_group_EMadd1' H n)
            φ (π→g[n+1] (EMadd1_functor φ n)) :=
  begin
    refine hwhisker_left _ (to_fun_isomorphism_trans _ _) ⬝hty _ ⬝hty
           hwhisker_right _ (to_fun_isomorphism_trans _ _)⁻¹ʰᵗʸ,
    refine _ ⬝htyh (homotopy_group_homomorphism_psquare 1 (apn_EMadd1_pequiv_EM1_natural φ n)),
    apply homotopy_group_functor_EM1_functor
  end

  definition homotopy_group_functor_EMadd1_functor' {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    hsquare (ghomotopy_group_EMadd1' G n)⁻¹ᵍ (ghomotopy_group_EMadd1' H n)⁻¹ᵍ
            (π→g[n+1] (EMadd1_functor φ n)) φ :=
  begin apply hhinverse, exact (homotopy_group_functor_EMadd1_functor φ n) end

  section infgroup
  open infgroup
  definition EM1_pmap_natural {G H : Group} {X Y : Type*} (f : X →* Y) (eX : G →∞g Ωg X)
    (eY : H →∞g Ωg Y) [H2 : is_trunc 1 X] [is_trunc 1 Y] (φ : G →g H)
    (p : hsquare eX eY φ (Ωg→ f)) : psquare (EM1_pmap eX) (EM1_pmap eY) (EM1_functor φ) f :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x using EM.set_rec,
      { exact respect_pt f },
      { apply eq_pathover,
        refine ap_compose f _ _ ⬝ph _ ⬝hp (ap_compose (EM1_pmap eY) _ _)⁻¹,
        refine ap02 _ !elim_pth ⬝ph _ ⬝hp ap02 _ !elim_pth⁻¹,
        refine _ ⬝hp !elim_pth⁻¹, apply transpose, exact square_of_eq_bot (p g) }},
    { exact !idp_con⁻¹ }
  end

  definition EM1_pequiv'_natural {G H : Group} {X Y : Type*} (f : X →* Y) (eX : G ≃∞g Ωg X)
    (eY : H ≃∞g Ωg Y) [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y]
    (φ : G →g H) (p : hsquare eX eY φ (Ω→ f)) :
    psquare (EM1_pequiv' eX) (EM1_pequiv' eY) (EM1_functor φ) f :=
  EM1_pmap_natural f eX eY φ p

  definition EM1_pequiv_natural {G H : Group} {X Y : Type*} (f : X →* Y) (eX : G ≃g π₁ X)
    (eY : H ≃g π₁ Y) [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y]
    (φ : G →g H) (p : hsquare eX eY φ (π→g[1] f)) :
    psquare (EM1_pequiv eX) (EM1_pequiv eY) (EM1_functor φ) f :=
  EM1_pequiv'_natural f _ _ φ
    begin
      assert p' : ptrunc_functor 0 (Ω→ f) ∘* pequiv_of_isomorphism eX ~*
                  pequiv_of_isomorphism eY ∘* pmap_of_homomorphism φ, exact phomotopy_of_homotopy p,
      exact p' ⬝h* (ptrunc_pequiv_natural 0 (Ω→ f)),
    end

  definition EM1_pequiv_type_natural {X Y : Type*} (f : X →* Y)
    [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [H3 : is_conn 0 Y] [H4 : is_trunc 1 Y] :
    psquare (EM1_pequiv_type X) (EM1_pequiv_type Y) (EM1_functor (π→g[1] f)) f :=
  begin refine EM1_pequiv_natural f _ _ _ _, exact homotopy.rfl end

  definition EM_up_natural {G H : AbGroup} (φ : G →g H) {X Y : Type*} (f : X →* Y) {n : ℕ}
    (eX : G →∞g Ωg[succ (succ n)] X) (eY : H →∞g Ωg[succ (succ n)] Y)
    (p : hsquare eX eY φ (Ωg→[succ (succ n)] f))
    : hsquare (EM_up eX) (EM_up eY) φ (Ω→[succ n] (Ω→ f)) :=
  p ⬝htyh hsquare_of_psquare (loopn_succ_in_natural (succ n) f)

  definition EMadd1_pmap_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ)
    (eX : G →∞g Ωg[succ n] X) (eY : H →∞g Ωg[succ n] Y)
    [HX : is_trunc (n.+1) X] [HY : is_trunc (n.+1) Y]
    (φ : G →g H) (p : hsquare eX eY φ (Ωg→[succ n] f)) :
    psquare (EMadd1_pmap n eX) (EMadd1_pmap n eY) (EMadd1_functor φ n) f :=
  begin
    revert X Y f eX eY HX HY p, induction n with n IH: intros,
    { apply EM1_pmap_natural, exact p },
    { do 2 rewrite [EMadd1_pmap_succ], refine _ ⬝* pwhisker_left _ !EMadd1_functor_succ⁻¹*,
      refine (ptrunc_elim_pcompose ((succ n).+1) _ _)⁻¹* ⬝* _ ⬝*
             (ptrunc_elim_ptrunc_functor ((succ n).+1) _ _)⁻¹*,
      apply ptrunc_elim_phomotopy,
      refine _ ⬝* !susp_elim_susp_functor⁻¹*,
      refine _ ⬝* susp_elim_phomotopy (IH _ _ _ _ _
                                           (@is_trunc_loop _ _ HX) _ (EM_up_natural φ f eX eY p)),
      apply susp_elim_natural }
  end

  definition EMadd1_pequiv'_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ)
    (eX : G ≃∞g Ωg[succ n] X) (eY : H ≃∞g Ωg[succ n] Y)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] [is_conn n Y] [is_trunc (n.+1) Y]
    (φ : G →g H) (p : hsquare eX eY φ (Ωg→[succ n] f)) :
     psquare (EMadd1_pequiv' n eX) (EMadd1_pequiv' n eY) (EMadd1_functor φ n) f :=
  EMadd1_pmap_natural f n eX eY φ p

  definition EMadd1_pequiv_natural_local_instance {X : Type*} (n : ℕ) [H : is_trunc (n.+1) X] :
    is_set (Ω[succ n] X) :=
  @(is_set_loopn (succ n) X) H

  local attribute EMadd1_pequiv_natural_local_instance [instance]

  definition EMadd1_pequiv_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ)
    (eX : G ≃g πg[n+1] X) (eY : H ≃g πg[n+1] Y)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] [H3 : is_conn n Y]
    [H4 : is_trunc (n.+1) Y] (φ : G →g H) (p : hsquare eX eY φ (π→g[n+1] f)) :
    psquare (EMadd1_pequiv n eX) (EMadd1_pequiv n eY) (EMadd1_functor φ n) f :=
  EMadd1_pequiv'_natural f n
    _ --(inf_isomorphism_of_isomorphism eX ⬝∞g gtrunc_isomorphism (Ω[succ n] X))
    _ --(inf_isomorphism_of_isomorphism eY ⬝∞g gtrunc_isomorphism (Ω[succ n] Y))
    φ (p ⬝htyh hsquare_of_psquare (ptrunc_pequiv_natural 0 (Ω→[succ n] f)))

  end infgroup

  definition EMadd1_pequiv_succ_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ)
    (eX : G ≃g πag[n+2] X) (eY : H ≃g πag[n+2] Y) [is_conn (n.+1) X] [is_trunc (n.+2) X]
    [is_conn (n.+1) Y] [is_trunc (n.+2) Y] (φ : G →g H) (p : hsquare eX eY φ (π→g[n+2] f)) :
    psquare (EMadd1_pequiv_succ n eX) (EMadd1_pequiv_succ n eY) (EMadd1_functor φ (n+1)) f :=
  @(EMadd1_pequiv_natural f (succ n) eX eY) _ _ _ _ φ p

  definition EMadd1_pequiv_type_natural {X Y : Type*} (f : X →* Y) (n : ℕ)
    [H1 : is_conn (n+1) X] [H2 : is_trunc (n+1+1) X]
    [H3 : is_conn (n+1) Y] [H4 : is_trunc (n+1+1) Y] :
    psquare (EMadd1_pequiv_type X n) (EMadd1_pequiv_type Y n)
            (EMadd1_functor (π→g[n+2] f) (succ n)) f :=
  EMadd1_pequiv_succ_natural f n !isomorphism.refl !isomorphism.refl (π→g[n+2] f)
    proof λa, idp qed

  definition EMadd1_pmap_equiv (n : ℕ) (X Y : Type*) [is_conn (n+1) X] [is_trunc (n+1+1) X]
    [H4 : is_trunc (n+1+1) Y] : (X →* Y) ≃ πag[n+2] X →g πag[n+2] Y :=
  begin
    have H4' : is_trunc ((n+1).+1) Y, from H4,
   have is_set (Ωg[succ (n+1)] Y), from is_set_loopn (n+1+1) Y,
    fapply equiv.MK,
    { exact π→g[n+2] },
    { intro φ, refine (_ ∘* EMadd1_functor φ (n+1)) ∘* (EMadd1_pequiv_type X n)⁻¹ᵉ*,
      exact EMadd1_pmap (n+1) (gtrunc_isomorphism (Ωg[succ (n+1)] Y)) },
    { intro φ, apply homomorphism_eq,
      refine homotopy_group_functor_pcompose (n+2) _ _ ⬝hty _, exact sorry }, -- easy but tedious
    { intro f, apply eq_of_phomotopy, refine (phomotopy_pinv_right_of_phomotopy _)⁻¹*,
      exact sorry /-apply EMadd1_pequiv_type_natural-/ }
  end

  definition EM1_functor_trivial_homomorphism [constructor] (G H : Group) :
    EM1_functor (trivial_homomorphism G H) ~* pconst (EM1 G) (EM1 H) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x using EM.set_rec,
      { reflexivity },
      { apply eq_pathover_constant_right, apply hdeg_square,
        refine !elim_pth ⬝ _, apply resp_one }},
    { reflexivity }
  end

  definition EMadd1_functor_trivial_homomorphism (G H : AbGroup) (n : ℕ) :
    EMadd1_functor (trivial_homomorphism G H) n ~* pconst (EMadd1 G n) (EMadd1 H n) :=
  begin
    induction n with n h,
    { exact EM1_functor_trivial_homomorphism G H },
    { refine !EMadd1_functor_succ ⬝* ptrunc_functor_phomotopy (n+2) _ ⬝* !ptrunc_functor_pconst,
      refine susp_functor_phomotopy h ⬝* !susp_functor_pconst }
  end

  definition EMadd1_pfunctor [constructor] (G H : AbGroup) (n : ℕ) :
    (G →gg H) →* EMadd1 G n →** EMadd1 H n :=
  pmap.mk (λφ, EMadd1_functor φ n) (eq_of_phomotopy (EMadd1_functor_trivial_homomorphism G H n))

  definition loopn_EMadd1_add (G : AbGroup) (n m : ℕ) : Ω[n] (EMadd1 G (m + n)) ≃* EMadd1 G m :=
  begin
    induction n with n e,
    { reflexivity },
    { refine !loopn_succ_in ⬝e* Ω≃[n] (loop_EMadd1 G (m + n))⁻¹ᵉ* ⬝e* e }
  end

  definition loopn_EMadd1_add_of_eq (G : AbGroup) {n m k : ℕ} (p : m + n = k) : Ω[n] (EMadd1 G k) ≃* EMadd1 G m :=
  by induction p; exact loopn_EMadd1_add G n m

  definition EM1_phomotopy {G : Group} {X : Type*} [is_trunc 1 X] {f g : EM1 G →* X} (h : Ω→ f ~ Ω→ g) :
    f ~* g :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x using EM.set_rec with a,
      { exact respect_pt f ⬝ (respect_pt g)⁻¹ },
      { apply eq_pathover, apply move_top_of_right, apply move_bot_of_right,
        apply move_top_of_left', apply move_bot_of_left, apply hdeg_square, exact h (pth a) }},
    { apply inv_con_cancel_right }
  end

  /- properties about EM -/

  definition deloopable_EM [instance] [constructor] (G : AbGroup) (n : ℕ) : deloopable (EM G n) :=
  deloopable.mk (EMadd1 G n) (loop_EM G n)

  definition gEM (G : AbGroup) (n : ℕ) : InfGroup :=
  InfGroup_of_deloopable (EM G n)

  definition gloop_EM1 [constructor] (G : Group) : Ωg (EM1 G) ≃∞g InfGroup_of_Group G :=
  inf_isomorphism_of_equiv (EM.base_eq_base_equiv G) groupoid_quotient.encode_con

  definition gloop_EMadd1 [constructor] (G : AbGroup) (n : ℕ) : Ωg (EMadd1 G n) ≃∞g gEM G n :=
  deloop_isomorphism (EM G n)

  definition gEM0_isomorphism (G : AbGroup) : gEM G 0 ≃∞g InfGroup_of_Group G :=
  (gloop_EMadd1 G 0)⁻¹ᵍ⁸ ⬝∞g gloop_EM1 G

  definition gEM_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) : gEM G n →∞g gEM H n :=
  gloop_EMadd1 H n ∘∞g Ωg→ (EMadd1_functor φ n) ∘∞g (gloop_EMadd1 G n)⁻¹ᵍ⁸

  definition EM_pmap [unfold 8] {G : AbGroup} (X : InfGroup) (n : ℕ)
    (e : AbInfGroup_of_AbGroup G →∞g Ωg'[n] X) [H : is_trunc n X] : EM G n →* X :=
  begin
    cases n with n,
    { exact pmap_of_inf_homomorphism e },
    { have is_trunc (n.+1) X, from H, exact EMadd1_pmap n e }
  end

  definition EM_homomorphism_gloop [unfold 8] {G : AbGroup} (X : Type*) (n : ℕ)
    (e : AbInfGroup_of_AbGroup G →∞g Ωg[succ n] X) [H : is_trunc (n+1) X] : gEM G n →∞g Ωg X :=
  Ωg→ (EMadd1_pmap n e) ∘∞g !InfGroup_equiv_closed_isomorphism⁻¹ᵍ⁸

  definition gloopn_succ_in' (n : ℕ) (A : Type*) : Ωg[succ n] A ≃∞g Ωg'[n] (Ωg A) :=
  inf_isomorphism_of_equiv (loopn_succ_in n A)
                           (by cases n with n; apply is_mul_hom_id; exact loopn_succ_in_con)

  definition EM_homomorphism_deloopable [unfold 8] {G : AbGroup} (X : Type*) (H : deloopable X) (n : ℕ)
    (e : AbInfGroup_of_AbGroup G →∞g Ωg'[n] (InfGroup_of_deloopable X)) (H : is_trunc (n+1) (deloop X)) :
    gEM G n →∞g InfGroup_of_deloopable X :=
  deloop_isomorphism X ∘∞g
  EM_homomorphism_gloop (deloop X) n
    ((gloopn_succ_in' n (deloop X))⁻¹ᵍ⁸ ∘∞g Ωg'→[n] (deloop_isomorphism X)⁻¹ᵍ⁸ ∘∞g e)

  definition is_mul_hom_EM_functor [constructor] (G H : AbGroup) (n : ℕ) :
    is_mul_hom (λ(φ : G →gg H), EM_functor φ n) :=
  begin
    intro φ ψ,
    apply eq_of_phomotopy,
    exact sorry
    -- exact sorry, exact sorry, exact sorry
--    refine idpath (φ 0 * ψ 0) ⬝ _,
  end

  /- an enriched homomorphism -/
  definition EM_ehomomorphism [constructor] (G H : AbGroup) (n : ℕ) :
    InfGroup_of_Group (G →gg H) →∞g InfGroup_of_deloopable (EM G n →** EM H n) :=
  inf_homomorphism.mk (λφ, EM_functor φ n) (is_mul_hom_EM_functor G H n)

  -- definition EM_homomorphism [unfold 8] {G : AbGroup} {X : Type*} (Y : Type*) (e : Ω Y ≃* X) (n : ℕ)
  --   (e : AbInfGroup_of_AbGroup G →∞g Ωg[succ n] X) [H : is_trunc n X] : gEM G n →∞g X :=
  -- _

  -- definition gEM_gfunctor {G H : AbGroup} (n : ℕ) : (G →gg H) →∞g (gEM G n →∞g gEM H n) :=
  -- inf_homomorphism.mk (EM_functor _ n) sorry

  /- The Eilenberg-MacLane space K(G,n) with the same homotopy group as X on level n.
     On paper this is written K(πₙ(X), n). The problem is that for
     * n = 0 the expression π₀(X) is a pointed set, and K(X,0) needs X to be a pointed set
     * n = 1 the expression π₁(X) is a group, and K(G,1) needs G to be a group
     * n ≥ 2 the expression πₙ(X) is an abelian, and K(G,n) needs X to be an abelian group

  -/
  definition EM_type (X : Type*) : ℕ → Type*
  | 0     := ptrunc 0 X
  | 1     := EM1 (π₁ X)
  | (n+2) := EMadd1 (πag[n+2] X) (n+1)

  definition EM_type_pequiv {X Y : pType.{u}} (n : ℕ) [Hn : is_succ n] (e : πg[n] Y ≃g πg[n] X)
    [H1 : is_conn (n.-1) X] [H2 : is_trunc n X] : EM_type Y n ≃* X :=
  begin
    induction Hn with n, cases n with n,
    { have is_conn 0 X, from H1,
      have is_trunc 1 X, from H2,
      exact EM1_pequiv e },
    { have is_conn (n+1) X, from H1,
      have is_trunc ((n+1).+1) X, from H2,
      exact EMadd1_pequiv (n+1) e }
  end

  -- definition EM1_functor_equiv' (X Y : Type*) [H1 : is_conn 0 X] [H2 : is_trunc 1 X]
  --   [H3 : is_conn 0 Y] [H4 : is_trunc 1 Y] : (X →* Y) ≃ (π₁ X →g π₁ Y) :=
  -- begin
  --   fapply equiv.MK,
  --   { intro f, exact π→g[1] f },
  --   { intro φ, exact EM1_pequiv_type Y ∘* EM1_functor φ ∘* (EM1_pequiv_type X)⁻¹ᵉ* },
  --   { intro φ, apply homomorphism_eq,
  --     refine homotopy_group_homomorphism_pcompose _ _ _ ⬝hty _,
  --     refine hwhisker_left _ (homotopy_group_homomorphism_pcompose _ _ _) ⬝hty _,
  --     refine (hassoc _ _ _)⁻¹ʰᵗʸ ⬝hty _, exact sorry },
  --   { intro f, apply eq_of_phomotopy, refine !passoc⁻¹* ⬝* _, apply pinv_right_phomotopy_of_phomotopy,
  --     exact sorry }
  -- end

  -- definition EMadd1_functor_equiv' (n : ℕ) (X Y : Type*) [H1 : is_conn (n+1) X] [H2 : is_trunc (n+1+1) X]
  --   [H3 : is_conn (n+1) Y] [H4 : is_trunc (n+1+1) Y] : (X →* Y) ≃ (πag[n+2] X →g πag[n+2] Y) :=
  -- begin
  --   fapply equiv.MK,
  --   { intro f, exact π→g[n+2] f },
  --   { intro φ, exact EMadd1_pequiv_type Y n ∘* EMadd1_functor φ (n+1) ∘* (EMadd1_pequiv_type X n)⁻¹ᵉ* },
  --   { intro φ, apply homomorphism_eq,
  --     refine homotopy_group_homomorphism_pcompose _ _ _ ⬝hty _,
  --     refine hwhisker_left _ (homotopy_group_homomorphism_pcompose _ _ _) ⬝hty _,
  --     intro g, exact sorry },
  --   { intro f, apply eq_of_phomotopy, refine !passoc⁻¹* ⬝* _, apply pinv_right_phomotopy_of_phomotopy,
  --     exact !EMadd1_pequiv_type_natural⁻¹* }
  -- end

  -- definition EM_functor_equiv (n : ℕ) (G H : AbGroup) : (G →g H) ≃ (EMadd1 G (n+1) →* EMadd1 H (n+1)) :=
  -- begin
  --   fapply equiv.MK,
  --   { intro φ, exact EMadd1_functor φ (n+1) },
  --   { intro f, exact ghomotopy_group_EMadd1 H (n+1) ∘g π→g[n+2] f ∘g (ghomotopy_group_EMadd1 G (n+1))⁻¹ᵍ },
  --   { intro f, apply homomorphism_eq, },
  --   { }
  -- end


  -- definition EMadd1_pmap {G : AbGroup} {X : Type*} (n : ℕ)
  --   (e : Ω[succ n] X ≃* G)
  --   (r : Πp q, e (p ⬝ q) = e p * e q)
  --   [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n →* X :=
  -- begin
  --   revert X e r H1 H2, induction n with n f: intro X e r H1 H2,
  --   { exact EM1_pmap e⁻¹ᵉ* (equiv.inv_preserve_binary e concat mul r) },
  --   rewrite [EMadd1_succ],
  --   exact ptrunc.elim ((succ n).+1)
  --           (susp.elim (f _ (EM_up e) (is_mul_hom_EM_up e r) _ _)),
  -- end

  -- definition is_set_pmap_ptruncconntype {n : ℕ₋₂} (X Y : (n.+1)-Type*[n]) : is_set (X →* Y) :=
  -- begin
  --   apply is_trunc_succ_intro,
  --   intro f g,
  --   apply @(is_trunc_equiv_closed_rev -1 (pmap_eq_equiv f g)),
  --   apply is_prop.mk,
  --   exact sorry
  -- end


  end

  section category
  /- category -/
  structure ptruncconntype' (n : ℕ₋₂) : Type :=
   (A : Type*)
   (H1 : is_conn n A)
   (H2 : is_trunc (n+1) A)

  attribute ptruncconntype'.A [coercion]
  attribute ptruncconntype'.H1 ptruncconntype'.H2 [instance]

  definition ptruncconntype'_equiv_ptruncconntype [constructor] (n : ℕ₋₂) :
    (ptruncconntype' n : Type.{u+1}) ≃ ((n+1)-Type*[n] : Type.{u+1}) :=
  begin
    fapply equiv.MK,
    { intro X, exact ptruncconntype.mk (ptruncconntype'.A X) _ pt _ },
    { intro X, exact ptruncconntype'.mk X _ _ },
    { intro X, induction X with X H1 x₀ H2, reflexivity },
    { intro X, induction X with X H1 H2, induction X with X x₀, reflexivity }
  end

  definition EM1_pequiv_ptruncconntype' (X : ptruncconntype' 0) : EM1 (πg[1] X) ≃* X :=
  @(EM1_pequiv_type X) _ (ptruncconntype'.H2 X)

  definition EMadd1_pequiv_ptruncconntype' {n : ℕ} (X : ptruncconntype' (n+1)) :
    EMadd1 (πag[n+2] X) (succ n) ≃* X :=
  @(EMadd1_pequiv_type X n) _ (ptruncconntype'.H2 X)

  open trunc_index
  definition is_set_pmap_ptruncconntype {n : ℕ₋₂} (X Y : ptruncconntype' n) : is_set (X →* Y) :=
  begin
    cases n with n, { exact _ },
    cases Y with Y H1 H2, cases Y with Y y₀,
    exact is_trunc_pmap_of_is_conn X n _ -1 _ (pointed.MK Y y₀) !le.refl H2,
  end

  open category functor nat_trans

  definition precategory_ptruncconntype' [constructor] (n : ℕ₋₂) :
    precategory.{u+1 u} (ptruncconntype' n) :=
  begin
    fapply precategory.mk,
    { exact λX Y, X →* Y },
    { exact is_set_pmap_ptruncconntype },
    { exact λX Y Z g f, g ∘* f },
    { exact λX, pid X },
    { intros, apply eq_of_phomotopy, exact !passoc⁻¹* },
    { intros, apply eq_of_phomotopy, apply pid_pcompose },
    { intros, apply eq_of_phomotopy, apply pcompose_pid }
  end

  definition cptruncconntype' [constructor] (n : ℕ₋₂) : Precategory :=
  precategory.Mk (precategory_ptruncconntype' n)

  notation `cType*[`:95 n `]`:0 := cptruncconntype' n

  definition tEM1 [constructor] (G : Group) : ptruncconntype' 0 :=
  ptruncconntype'.mk (EM1 G) _ !is_trunc_EM1

  definition tEM [constructor] (G : AbGroup) (n : ℕ) : ptruncconntype' (n.-1) :=
  ptruncconntype'.mk (EM G n) _ !is_trunc_EM

  definition EM1_cfunctor : Grp ⇒ cType*[0] :=
  functor.mk
    (λG, tEM1 G)
    (λG H φ, EM1_functor φ)
    begin intro, fapply eq_of_phomotopy, apply EM1_functor_gid end
    begin intros, fapply eq_of_phomotopy, apply EM1_functor_gcompose end

  definition EM_cfunctor (n : ℕ) : AbGrp ⇒ cType*[n.-1] :=
  functor.mk
    (λG, tEM G n)
    (λG H φ, EM_functor φ n)
    begin intro, fapply eq_of_phomotopy, apply EM_functor_gid end
    begin intros, fapply eq_of_phomotopy, apply EM_functor_gcompose end

  definition homotopy_group_cfunctor : cType*[0] ⇒ Grp :=
  functor.mk
    (λX, πg[1] X)
    (λX Y (f : X →* Y), π→g[1] f)
    begin intro, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pid end
    begin intros, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pcompose end

  definition ab_homotopy_group_cfunctor (n : ℕ) : cType*[n.+1] ⇒ AbGrp :=
  functor.mk
    (λX, πag[n+2] X)
    (λX Y (f : X →* Y), by rexact π→g[n+2] f)
    begin intro, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pid end
    begin intros, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pcompose end

  definition is_equivalence_EM1_cfunctor : is_equivalence EM1_cfunctor.{u} :=
  begin
    fapply is_equivalence.mk,
    { exact homotopy_group_cfunctor.{u} },
    { fapply natural_iso.mk,
      { fapply nat_trans.mk,
        { intro G, exact (fundamental_group_EM1' G)⁻¹ᵍ },
        { intro G H φ, apply homomorphism_eq, exact hhinverse (homotopy_group_functor_EM1_functor φ) }},
      { intro G, fapply iso.is_iso.mk,
        { exact fundamental_group_EM1' G },
        { apply homomorphism_eq,
          exact to_right_inv (equiv_of_isomorphism (fundamental_group_EM1' G)), },
        { apply homomorphism_eq,
          exact to_left_inv (equiv_of_isomorphism (fundamental_group_EM1' G)), }}},
    { fapply natural_iso.mk,
      { fapply nat_trans.mk,
        { intro X, exact EM1_pequiv_ptruncconntype' X },
        { intro X Y f, apply eq_of_phomotopy, apply EM1_pequiv_type_natural }},
      { intro X, fapply iso.is_iso.mk,
        { exact (EM1_pequiv_ptruncconntype' X)⁻¹ᵉ* },
        { apply eq_of_phomotopy, apply pleft_inv },
        { apply eq_of_phomotopy, apply pright_inv }}}
  end

  definition is_equivalence_EM_cfunctor (n : ℕ) : is_equivalence (EM_cfunctor.{u} (n+2)) :=
  begin
    fapply is_equivalence.mk,
    { exact ab_homotopy_group_cfunctor.{u} n },
    { fapply natural_iso.mk,
      { fapply nat_trans.mk,
        { intro G, exact (ghomotopy_group_EMadd1' G (n+1))⁻¹ᵍ },
        { intro G H φ, apply homomorphism_eq, exact homotopy_group_functor_EMadd1_functor' φ (n+1) }},
      { intro G, fapply iso.is_iso.mk,
        { exact ghomotopy_group_EMadd1' G (n+1) },
        { apply homomorphism_eq,
          exact to_right_inv (equiv_of_isomorphism (ghomotopy_group_EMadd1' G (n+1))), },
        { apply homomorphism_eq,
          exact to_left_inv (equiv_of_isomorphism (ghomotopy_group_EMadd1' G (n+1))), }}},
    { fapply natural_iso.mk,
      { fapply nat_trans.mk,
        { intro X, exact EMadd1_pequiv_ptruncconntype' X },
        { intro X Y f, apply eq_of_phomotopy, apply EMadd1_pequiv_type_natural }},
      { intro X, fapply iso.is_iso.mk,
        { exact (EMadd1_pequiv_ptruncconntype' X)⁻¹ᵉ* },
        { apply eq_of_phomotopy, apply pleft_inv },
        { apply eq_of_phomotopy, apply pright_inv }}}
  end

  definition Grp_equivalence_cptruncconntype' [constructor] : Grp.{u} ≃c cType*[0] :=
  equivalence.mk EM1_cfunctor.{u} is_equivalence_EM1_cfunctor.{u}

  definition AbGrp_equivalence_cptruncconntype' [constructor] (n : ℕ) : AbGrp.{u} ≃c cType*[n.+1] :=
  equivalence.mk (EM_cfunctor.{u} (n+2)) (is_equivalence_EM_cfunctor.{u} n)
  end category

  definition pequiv_EMadd1_of_loopn_pequiv_EM1 {G : AbGroup} {X : Type*} (n : ℕ)
    (e : Ω[n] X ≃* EM1 G) [H1 : is_conn n X] : X ≃* EMadd1 G n :=
  begin
    symmetry, apply EMadd1_pequiv, symmetry,
    refine isomorphism_of_eq (ap (λx, πg[x+1] X) !zero_add⁻¹) ⬝g homotopy_group_add X 0 n ⬝g _ ⬝g
      !fundamental_group_EM1,
    exact homotopy_group_isomorphism_of_pequiv 0 e,
    refine is_trunc_of_is_trunc_loopn n 1 X _ (@is_conn_of_is_conn_succ _ _ H1),
    exact is_trunc_equiv_closed_rev 1 e _
  end

  definition EM1_pequiv_EM1 {G H : Group} (φ : G ≃g H) : EM1 G ≃* EM1 H :=
  pequiv.MK (EM1_functor φ) (EM1_functor φ⁻¹ᵍ)
    abstract (EM1_functor_gcompose φ⁻¹ᵍ φ)⁻¹* ⬝* EM1_functor_phomotopy proof left_inv φ qed ⬝*
             EM1_functor_gid G end
    abstract (EM1_functor_gcompose φ φ⁻¹ᵍ)⁻¹* ⬝* EM1_functor_phomotopy proof right_inv φ qed ⬝*
             EM1_functor_gid H end

  definition is_contr_EM1 {G : Group} (H : is_contr G) : is_contr (EM1 G) :=
  begin
    refine is_contr_of_is_conn_of_is_trunc _ !is_conn_EM1,
    refine is_trunc_succ_succ_of_is_trunc_loop _ _ _ _,
    refine is_trunc_equiv_closed _ !loop_EM1 _,
    apply is_trunc_succ, exact H
  end

  definition is_contr_EMadd1 (n : ℕ) {G : AbGroup} (H : is_contr G) : is_contr (EMadd1 G n) :=
  begin
    induction n with n IH,
    { exact is_contr_EM1 H },
    { have is_contr (ptrunc (n+2) (susp (EMadd1 G n))), from _,
      exact this }
  end

  definition is_contr_EM (n : ℕ) {G : AbGroup} (H : is_contr G) : is_contr (K G n) :=
  begin
    cases n with n,
    { exact H },
    { exact is_contr_EMadd1 n H }
  end

  definition EMadd1_pequiv_EMadd1 (n : ℕ) {G H : AbGroup} (φ : G ≃g H) : EMadd1 G n ≃* EMadd1 H n :=
  pequiv.MK (EMadd1_functor φ n) (EMadd1_functor φ⁻¹ᵍ n)
    abstract (EMadd1_functor_gcompose φ⁻¹ᵍ φ n)⁻¹* ⬝* EMadd1_functor_phomotopy proof left_inv φ qed n ⬝*
             EMadd1_functor_gid G n end
    abstract (EMadd1_functor_gcompose φ φ⁻¹ᵍ n)⁻¹* ⬝* EMadd1_functor_phomotopy proof right_inv φ qed n ⬝*
             EMadd1_functor_gid H n end

  definition EM_pequiv_EM (n : ℕ) {G H : AbGroup} (φ : G ≃g H) : K G n ≃* K H n :=
  begin
    cases n with n,
    { exact pequiv_of_isomorphism φ },
    { exact EMadd1_pequiv_EMadd1 n φ }
  end

  definition ppi_EMadd1 {X : Type*} (Y : X → Type*) (n : ℕ) :
    (Π*(x : X), EMadd1 (πag[n+2] (Y x)) (n+1)) ≃* EMadd1 (πag[n+2] (Π*(x : X), Y x)) (n+1) :=
  begin
    exact sorry
  end
--EM_spectrum (πₛ[s] (spi X Y)) k ≃* spi X (λx, EM_spectrum (πₛ[s] (Y x))) k


  /- fiber of EM_functor -/
  open fiber
  definition is_trunc_fiber_EM1_functor {G H : Group} (φ : G →g H) :
    is_trunc 1 (pfiber (EM1_functor φ)) :=
  is_trunc_pfiber _ _ _ _

  definition is_conn_fiber_EM1_functor {G H : Group} (φ : G →g H) :
    is_conn -1 (pfiber (EM1_functor φ)) :=
  begin
    apply is_conn_fiber_of_is_conn
  end

  definition is_trunc_fiber_EMadd1_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    is_trunc (n+1) (pfiber (EMadd1_functor φ n)) :=
  is_trunc_pfiber _ _ _ _

  definition is_conn_fiber_EMadd1_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    is_conn (n.-1) (pfiber (EMadd1_functor φ n)) :=
  begin
    apply is_conn_fiber_of_is_conn, apply is_conn_of_is_conn_succ, apply is_conn_EMadd1,
    apply is_conn_EMadd1
  end

  definition is_trunc_fiber_EM_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    is_trunc n (pfiber (EM_functor φ n)) :=
  is_trunc_pfiber _ _ _ _

  definition is_conn_fiber_EM_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    is_conn (n.-2) (pfiber (EM_functor φ n)) :=
  begin
    apply is_conn_fiber_of_is_conn, apply is_conn_of_is_conn_succ
  end

  section
    open chain_complex prod fin

  /- TODO: other cases -/
  definition LES_isomorphism_kernel_of_trivial
    {X Y : pType.{u}} (f : X →* Y) (n : ℕ) [H : is_succ n]
    (H1 : is_contr (πg[n+1] Y)) : πg[n] (pfiber f) ≃g Kernel (π→g[n] f) :=
  begin
    induction H with n,
    have H2 : is_exact (π→g[n+1] (ppoint f)) (π→g[n+1] f),
    from is_exact_of_is_exact_at (is_exact_LES_of_homotopy_groups f (n+1, 0)),
    have H3 : is_exact (π→g[n+1] (boundary_map f) ∘g ghomotopy_group_succ_in n Y)
      (π→g[n+1] (ppoint f)),
    from is_exact_of_is_exact_at (is_exact_LES_of_homotopy_groups f (n+1, 1)),
    exact isomorphism_kernel_of_is_exact H3 H2 H1
  end

  end

  open group algebra is_trunc
  definition homotopy_group_fiber_EM1_functor {G H : Group.{u}} (φ : G →g H) :
    π₁ (pfiber (EM1_functor φ)) ≃g Kernel φ :=
  have H1 : is_trunc 1 (EM1 H), from sorry,
  have H2 : 1 <[ℕ] 1 + 1, from sorry,
  LES_isomorphism_kernel_of_trivial (EM1_functor φ) 1
    (@trivial_homotopy_group_of_is_trunc _ 1 2 H1 H2) ⬝g
  sorry

  definition homotopy_group_fiber_EMadd1_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    πg[n+1] (pfiber (EMadd1_functor φ n)) ≃g Kernel φ :=
  sorry

  /- TODO: move-/
  definition cokernel {G H : AbGroup} (φ : G →g H) : AbGroup :=
  quotient_ab_group (image φ)

  /- todo: in algebra/quotient_group, do the first steps without assuming that N is normal,
  then this is qg for (image φ) in H -/
  definition image_cosets {G H : Group} (φ : G →g H) : Set* :=
  sorry

  definition homotopy_group_EMadd1_functor1 {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    πg[n+1] (pfiber (EMadd1_functor φ (n+1))) ≃g cokernel φ :=
  sorry

  definition homotopy_group_EMadd1_functor2 {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    πg[n+1] (pfiber (EMadd1_functor φ n)) ≃g Kernel φ :=
  sorry

  definition trunc_fiber_EM1_functor {G H : Group} (φ : G →g H) :
    ptrunc 0 (pfiber (EM1_functor φ)) ≃* image_cosets φ :=
  sorry

end EM
