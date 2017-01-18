-- Authors: Floris van Doorn

import homotopy.EM ..move_to_lib algebra.category.functor.equivalence ..pointed_pi

open eq equiv is_equiv algebra group nat pointed EM.ops is_trunc trunc susp function is_conn

namespace EM

  definition EMadd1_functor_succ [unfold_full] {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    EMadd1_functor φ (succ n) ~* ptrunc_functor (n+2) (psusp_functor (EMadd1_functor φ n)) :=
  by reflexivity

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
      refine ptrunc_functor_phomotopy _ (psusp_functor_phomotopy p ⬝* !psusp_functor_pid) ⬝* _,
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
      refine ptrunc_functor_phomotopy _ (psusp_functor_phomotopy p ⬝* !psusp_functor_pcompose) ⬝* _,
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
    { exact ptrunc_functor_phomotopy _ (psusp_functor_phomotopy q) }
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
    fapply pequiv.MK,
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
    loopn_EMadd1_pequiv_EM1 G (succ n) ~* (loopn_succ_in (EMadd1 G (succ n)) n)⁻¹ᵉ* ∘*
      Ω→[n] (loop_EMadd1 G n) ∘* loopn_EMadd1_pequiv_EM1 G n :=
  by reflexivity

  -- definition is_trunc_EMadd1' [instance] (G : AbGroup) (n : ℕ) : is_trunc (succ n) (EMadd1 G n) :=
  -- is_trunc_EMadd1 G n

  definition loop_EMadd1_succ (G : AbGroup) (n : ℕ) :
    loop_EMadd1 G (n+1) ~* (loop_ptrunc_pequiv (n+1+1) (psusp (EMadd1 G (n+1))))⁻¹ᵉ* ∘*
    freudenthal_pequiv (EMadd1 G (n+1)) (add_mul_le_mul_add n 1 1) ∘*
    (ptrunc_pequiv (n+1+1) (EMadd1 G (n+1)))⁻¹ᵉ* :=
  by reflexivity

  definition ap1_EMadd1_natural {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    Ω→ (EMadd1_functor φ (succ n)) ∘* loop_EMadd1 G n ~* loop_EMadd1 H n ∘* EMadd1_functor φ n :=
  begin
    refine pwhisker_right _ (ap1_phomotopy !EMadd1_functor_succ) ⬝* _,
    induction n with n IH,
    { refine pwhisker_left _ !hopf.to_pmap_delooping_pinv ⬝* _ ⬝*
             pwhisker_right _ !hopf.to_pmap_delooping_pinv⁻¹*,
      refine !loop_psusp_unit_natural⁻¹* ⬝h* _,
      apply ap1_psquare,
      apply ptr_natural },
    { refine pwhisker_left _ !loop_EMadd1_succ ⬝* _ ⬝* pwhisker_right _ !loop_EMadd1_succ⁻¹*,
      refine _ ⬝h* !ap1_ptrunc_functor,
      refine (@(ptrunc_pequiv_natural (n+1+1) _) _ _)⁻¹ʰ* ⬝h* _,
      refine pwhisker_left _ !to_pmap_freudenthal_pequiv ⬝* _ ⬝*
             pwhisker_right _ !to_pmap_freudenthal_pequiv⁻¹*,
      apply ptrunc_functor_psquare,
      exact !loop_psusp_unit_natural⁻¹* }
  end

  definition apn_EMadd1_pequiv_EM1_natural {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    Ω→[n] (EMadd1_functor φ n) ∘* loopn_EMadd1_pequiv_EM1 G n ~*
    loopn_EMadd1_pequiv_EM1 H n ∘* EM1_functor φ :=
  begin
    induction n with n IH,
    { reflexivity },
    { refine pwhisker_left _ !loopn_EMadd1_pequiv_EM1_succ ⬝* _,
      refine _ ⬝* pwhisker_right _ !loopn_EMadd1_pequiv_EM1_succ⁻¹*,
      refine _ ⬝h* !loopn_succ_in_inv_natural,
      exact IH ⬝h* (apn_psquare n !ap1_EMadd1_natural) }
  end

  definition homotopy_group_functor_EMadd1_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    π→g[n+1] (EMadd1_functor φ n) ∘ ghomotopy_group_EMadd1' G n ~
    ghomotopy_group_EMadd1' H n ∘ φ :=
  begin
    refine hwhisker_left _ (to_fun_isomorphism_trans _ _) ⬝hty _ ⬝hty
           hwhisker_right _ (to_fun_isomorphism_trans _ _)⁻¹ʰᵗʸ,
    refine htyhcompose _ (homotopy_group_homomorphism_psquare 1 (apn_EMadd1_pequiv_EM1_natural φ n)),
    apply homotopy_group_functor_EM1_functor
  end

  definition homotopy_group_functor_EMadd1_functor' {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    φ ∘ (ghomotopy_group_EMadd1' G n)⁻¹ᵍ ~
      (ghomotopy_group_EMadd1' H n)⁻¹ᵍ ∘ π→g[n+1] (EMadd1_functor φ n) :=
  htyhinverse (homotopy_group_functor_EMadd1_functor φ n)

  definition EM1_pmap_natural {G H : Group} {X Y : Type*} (f : X →* Y) (eX : G → Ω X)
    (eY : H → Ω Y) (rX : Πg h, eX (g * h) = eX g ⬝ eX h) (rY : Πg h, eY (g * h) = eY g ⬝ eY h)
    [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y]
    (φ : G →g H) (p : Ω→ f ∘ eX ~ eY ∘ φ) :
    f ∘* EM1_pmap eX rX ~* EM1_pmap eY rY ∘* EM1_functor φ :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x using EM.set_rec,
      { exact respect_pt f },
      { apply eq_pathover,
        refine ap_compose f _ _ ⬝ph _ ⬝hp (ap_compose (EM1_pmap eY rY) _ _)⁻¹,
        refine ap02 _ !elim_pth ⬝ph _ ⬝hp ap02 _ !elim_pth⁻¹,
        refine _ ⬝hp !elim_pth⁻¹, apply transpose, exact square_of_eq_bot (p g) }},
    { exact !idp_con⁻¹ }
  end

  definition EM1_pequiv'_natural {G H : Group} {X Y : Type*} (f : X →* Y) (eX : G ≃* Ω X)
    (eY : H ≃* Ω Y) (rX : Πg h, eX (g * h) = eX g ⬝ eX h)  (rY : Πg h, eY (g * h) = eY g ⬝ eY h)
    [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y]
    (φ : G →g H) (p : Ω→ f ∘ eX ~ eY ∘ φ) :
    f ∘* EM1_pequiv' eX rX ~* EM1_pequiv' eY rY ∘* EM1_functor φ :=
  EM1_pmap_natural f eX eY rX rY φ p

  definition EM1_pequiv_natural {G H : Group} {X Y : Type*} (f : X →* Y) (eX : G ≃g π₁ X)
    (eY : H ≃g π₁ Y) [H1 : is_conn 0 X] [H2 : is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y]
    (φ : G →g H) (p : π→g[1] f ∘ eX ~ eY ∘ φ) :
    f ∘* EM1_pequiv eX ~* EM1_pequiv eY ∘* EM1_functor φ :=
  EM1_pequiv'_natural f _ _ _ _ φ
    begin
      assert p' : ptrunc_functor 0 (Ω→ f) ∘* pequiv_of_isomorphism eX ~*
                  pequiv_of_isomorphism eY ∘* pmap_of_homomorphism φ, exact phomotopy_of_homotopy p,
      exact phcompose p' (ptrunc_pequiv_natural 0 (Ω→ f)),
    end

  definition EM1_pequiv_type_natural {X Y : Type*} (f : X →* Y) [H1 : is_conn 0 X] [H2 : is_trunc 1 X]
    [H3 : is_conn 0 Y] [H4 : is_trunc 1 Y] :
    f ∘* EM1_pequiv_type X ~* EM1_pequiv_type Y ∘* EM1_functor (π→g[1] f) :=
  begin refine EM1_pequiv_natural f _ _ _ _, reflexivity end

  definition EM_up_natural {G H : AbGroup} (φ : G →g H) {X Y : Type*} (f : X →* Y) {n : ℕ}
    (eX : Ω[succ (succ n)] X ≃* G) (eY : Ω[succ (succ n)] Y ≃* H) (p : φ ∘ eX ~ eY ∘ Ω→[succ (succ n)] f)
    : φ ∘ EM_up eX ~ EM_up eY ∘ Ω→[succ n] (Ω→ f) :=
  begin
    refine htyhcompose _ p,
    exact to_homotopy (phinverse (loopn_succ_in_natural (succ n) f)⁻¹*)
  end

  definition EMadd1_pmap_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ) (eX : Ω[succ n] X ≃* G)
    (eY : Ω[succ n] Y ≃* H) (rX : Πp q, eX (p ⬝ q) = eX p * eX q) (rY : Πp q, eY (p ⬝ q) = eY p * eY q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] [H3 : is_conn n Y] [H4 : is_trunc (n.+1) Y]
    (φ : G →g H) (p : φ ∘ eX ~ eY ∘ Ω→[succ n] f) :
    f ∘* EMadd1_pmap n eX rX ~* EMadd1_pmap n eY rY ∘* EMadd1_functor φ n :=
  begin
    revert X Y f eX eY rX rY H1 H2 H3 H4 p, induction n with n IH: intros,
    { apply EM1_pmap_natural, exact @htyhinverse _ _ _ _ eX eY _ _ p },
    { do 2 rewrite [EMadd1_pmap_succ], refine _ ⬝* pwhisker_left _ !EMadd1_functor_succ⁻¹*,
      refine (ptrunc_elim_pcompose ((succ n).+1) _ _)⁻¹* ⬝* _ ⬝*
             (ptrunc_elim_ptrunc_functor ((succ n).+1) _ _)⁻¹*,
      apply ptrunc_elim_phomotopy,
      refine _ ⬝* !psusp_elim_psusp_functor⁻¹*,
      refine _ ⬝* psusp_elim_phomotopy (IH _ _ _ _ _ (is_mul_hom_EM_up eX rX) _ (@is_conn_loop _ _ H1)
                                           (@is_trunc_loop _ _ H2) _ _ (EM_up_natural φ f eX eY p)),
      apply psusp_elim_natural }
  end

  definition EMadd1_pequiv'_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ) (eX : Ω[succ n] X ≃* G)
    (eY : Ω[succ n] Y ≃* H) (rX : Πp q, eX (p ⬝ q) = eX p * eX q) (rY : Πp q, eY (p ⬝ q) = eY p * eY q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] [is_conn n Y] [is_trunc (n.+1) Y]
    (φ : G →g H) (p : φ ∘ eX ~ eY ∘ Ω→[succ n] f) :
     f ∘* EMadd1_pequiv' n eX rX ~* EMadd1_pequiv' n eY rY ∘* EMadd1_functor φ n :=
  begin rexact EMadd1_pmap_natural f n eX eY rX rY φ p end

  definition EMadd1_pequiv_natural_local_instance {X : Type*} (n : ℕ) [H : is_trunc (n.+1) X] :
    is_set (Ω[succ n] X) :=
  @(is_set_loopn (succ n) X) H
  local attribute EMadd1_pequiv_natural_local_instance [instance]

  definition EMadd1_pequiv_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ) (eX : πg[n+1] X ≃g G)
    (eY : πg[n+1] Y ≃g H) [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] [H3 : is_conn n Y]
    [H4 : is_trunc (n.+1) Y] (φ : G →g H) (p : φ ∘ eX ~ eY ∘ π→g[n+1] f) :
    f ∘* EMadd1_pequiv n eX ~* EMadd1_pequiv n eY ∘* EMadd1_functor φ n :=
  EMadd1_pequiv'_natural f n
    ((ptrunc_pequiv 0 (Ω[succ n] X))⁻¹ᵉ* ⬝e* pequiv_of_isomorphism eX)
    ((ptrunc_pequiv 0 (Ω[succ n] Y))⁻¹ᵉ* ⬝e* pequiv_of_isomorphism eY)
    _ _ φ (htyhcompose (to_homotopy (phinverse (ptrunc_pequiv_natural 0 (Ω→[succ n] f)))) p)

  definition EMadd1_pequiv_succ_natural {G H : AbGroup} {X Y : Type*} (f : X →* Y) (n : ℕ)
    (eX : πag[n+2] X ≃g G) (eY : πag[n+2] Y ≃g H) [is_conn (n.+1) X] [is_trunc (n.+2) X]
    [is_conn (n.+1) Y] [is_trunc (n.+2) Y] (φ : G →g H) (p : φ ∘ eX ~ eY ∘ π→g[n+2] f) :
    f ∘* EMadd1_pequiv_succ n eX ~* EMadd1_pequiv_succ n eY ∘* EMadd1_functor φ (n+1) :=
  @(EMadd1_pequiv_natural f (succ n) eX eY) _ _ _ _ φ p

  definition EMadd1_pequiv_type_natural {X Y : Type*} (f : X →* Y) (n : ℕ)
    [H1 : is_conn (n+1) X] [H2 : is_trunc (n+1+1) X] [H3 : is_conn (n+1) Y] [H4 : is_trunc (n+1+1) Y] :
    f ∘* EMadd1_pequiv_type X n ~* EMadd1_pequiv_type Y n ∘* EMadd1_functor (π→g[n+2] f) (succ n) :=
  EMadd1_pequiv_succ_natural f n !isomorphism.refl !isomorphism.refl (π→g[n+2] f)
    proof λa, idp qed

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
  --           (psusp.elim (f _ (EM_up e) (is_mul_hom_EM_up e r) _ _)),
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

  /- category -/
  structure ptruncconntype' (n : ℕ₋₂) : Type :=
   (A : Type*)
   (H1 : is_conn n A)
   (H2 : is_trunc (n+1) A)

  attribute ptruncconntype'.A [coercion]
  attribute ptruncconntype'.H1 ptruncconntype'.H2 [instance]

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
    exact is_trunc_pmap X n -1 (ptrunctype.mk Y _ y₀),
  end

  open category
  definition precategory_ptruncconntype'.{u} [constructor] (n : ℕ₋₂) :
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

  open functor

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
    (λX Y f, π→g[1] f)
    begin intro, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pid end
    begin intros, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_compose end

  definition ab_homotopy_group_cfunctor (n : ℕ) : cType*[n+2.-1] ⇒ AbGrp :=
  functor.mk
    (λX, πag[n+2] X)
    (λX Y f, π→g[n+2] f)
    begin intro, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pid end
    begin intros, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_compose end

  open nat_trans category

  definition is_equivalence_EM1_cfunctor.{u} : is_equivalence EM1_cfunctor.{u} :=
  begin
    fapply is_equivalence.mk,
    { exact homotopy_group_cfunctor.{u} },
    { fapply natural_iso.mk,
      { fapply nat_trans.mk,
        { intro G, exact (fundamental_group_EM1' G)⁻¹ᵍ },
        { intro G H φ, apply homomorphism_eq, exact htyhinverse (homotopy_group_functor_EM1_functor φ) }},
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

  definition is_equivalence_EM_cfunctor (n : ℕ) : is_equivalence (EM_cfunctor (n+2)) :=
  begin
    fapply is_equivalence.mk,
    { exact ab_homotopy_group_cfunctor n },
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

  definition Grp_equivalence_cptruncconntype'.{u} [constructor] : Grp.{u} ≃c cType*[0] :=
  equivalence.mk EM1_cfunctor.{u} is_equivalence_EM1_cfunctor.{u}

  definition AbGrp_equivalence_cptruncconntype' [constructor] (n : ℕ) : AbGrp ≃c cType*[n+2.-1] :=
  equivalence.mk (EM_cfunctor (n+2)) (is_equivalence_EM_cfunctor n)

end EM
