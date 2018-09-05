/- equalities between pointed homotopies and other facts about pointed types/functions/homotopies -/

-- Author: Floris van Doorn

import types.pointed2 .move_to_lib

open pointed eq equiv function is_equiv unit is_trunc trunc nat algebra sigma group lift option

namespace pointed

  definition phomotopy_mk_eq {A B : Type*} {f g : A →* B} {h k : f ~ g}
    {h₀ : h pt ⬝ respect_pt g = respect_pt f} {k₀ : k pt ⬝ respect_pt g = respect_pt f} (p : h ~ k)
    (q : whisker_right (respect_pt g) (p pt) ⬝ k₀ = h₀) : phomotopy.mk h h₀ = phomotopy.mk k k₀ :=
  phomotopy_eq p (idp ◾ to_right_inv !eq_con_inv_equiv_con_eq _ ⬝
    q ⬝ (to_right_inv !eq_con_inv_equiv_con_eq _)⁻¹)


  section phsquare
  /-
    Squares of pointed homotopies
  -/

  variables {A : Type*} {P : A → Type} {p₀ : P pt}
            {f f' f₀₀ f₂₀ f₄₀ f₀₂ f₂₂ f₄₂ f₀₄ f₂₄ f₄₄ : ppi P p₀}
            {p₁₀ : f₀₀ ~* f₂₀} {p₃₀ : f₂₀ ~* f₄₀}
            {p₀₁ : f₀₀ ~* f₀₂} {p₂₁ : f₂₀ ~* f₂₂} {p₄₁ : f₄₀ ~* f₄₂}
            {p₁₂ : f₀₂ ~* f₂₂} {p₃₂ : f₂₂ ~* f₄₂}
            {p₀₃ : f₀₂ ~* f₀₄} {p₂₃ : f₂₂ ~* f₂₄} {p₄₃ : f₄₂ ~* f₄₄}
            {p₁₄ : f₀₄ ~* f₂₄} {p₃₄ : f₂₄ ~* f₄₄}

  definition phtranspose (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₀₁ p₂₁ p₁₀ p₁₂ :=
  p⁻¹

  definition eq_top_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ = p₀₁ ⬝* p₁₂ ⬝* p₂₁⁻¹* :=
  eq_trans_symm_of_trans_eq p

  definition eq_bot_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₁₂ = p₀₁⁻¹* ⬝* p₁₀ ⬝* p₂₁ :=
  eq_symm_trans_of_trans_eq p⁻¹ ⬝ !trans_assoc⁻¹

  definition eq_left_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₀₁ = p₁₀ ⬝* p₂₁ ⬝* p₁₂⁻¹* :=
  eq_top_of_phsquare (phtranspose p)

  definition eq_right_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₂₁ = p₁₀⁻¹* ⬝* p₀₁ ⬝* p₁₂ :=
  eq_bot_of_phsquare (phtranspose p)

  end phsquare

  -- /- the pointed type of (unpointed) dependent maps -/
  -- definition pupi [constructor] {A : Type} (P : A → Type*) : Type* :=
  -- pointed.mk' (Πa, P a)

  -- definition loop_pupi_commute {A : Type} (B : A → Type*) : Ω(pupi B) ≃* pupi (λa, Ω (B a)) :=
  -- pequiv_of_equiv eq_equiv_homotopy rfl

  -- definition equiv_pupi_right {A : Type} {P Q : A → Type*} (g : Πa, P a ≃* Q a)
  --   : pupi P ≃* pupi Q :=
  -- pequiv_of_equiv (pi_equiv_pi_right g)
  --   begin esimp, apply eq_of_homotopy, intros a, esimp, exact (respect_pt (g a)) end


  -- definition pmap_eq_equiv {X Y : Type*} (f g : X →* Y) : (f = g) ≃ (f ~* g) :=
  -- begin
  --   refine eq_equiv_fn_eq_of_equiv (@pmap.sigma_char X Y) f g ⬝e _,
  --   refine !sigma_eq_equiv ⬝e _,
  --   refine _ ⬝e (phomotopy.sigma_char f g)⁻¹ᵉ,
  --   fapply sigma_equiv_sigma,
  --   { esimp, apply eq_equiv_homotopy },
  --   { induction g with g gp, induction Y with Y y0, esimp, intro p, induction p, esimp at *,
  --     refine !pathover_idp ⬝e _, refine _ ⬝e !eq_equiv_eq_symm,
  --     apply equiv_eq_closed_right, exact !idp_con⁻¹ }
  -- end


  /- todo: make type argument explicit in ppcompose_left and ppcompose_left_* -/
  /- todo: delete papply_pcompose -/
  /- todo: pmap_pbool_equiv is a special case of ppmap_pbool_pequiv. -/

  definition ppcompose_left_pid [constructor] (A B : Type*) : ppcompose_left (pid B) ~* pid (ppmap A B) :=
  phomotopy_mk_ppmap (λf, pid_pcompose f) (!trans_refl ⬝ !phomotopy_of_eq_of_phomotopy⁻¹)

  definition ppcompose_right_pid [constructor] (A B : Type*) : ppcompose_right (pid A) ~* pid (ppmap A B) :=
  phomotopy_mk_ppmap (λf, pcompose_pid f) (!trans_refl ⬝ !phomotopy_of_eq_of_phomotopy⁻¹)

  section
  variables {A A' : Type*} {P : A → Type} {P' : A' → Type} {p₀ : P pt} {p₀' : P' pt} {k l : ppi P p₀}
  definition phomotopy_of_eq_inv (p : k = l) :
    phomotopy_of_eq p⁻¹ = (phomotopy_of_eq p)⁻¹* :=
  begin induction p, exact !refl_symm⁻¹ end

  /- todo: replace regular pap -/
  definition pap' (f : ppi P p₀ → ppi P' p₀') (p : k ~* l) : f k ~* f l :=
  by induction p using phomotopy_rec_idp; reflexivity

  definition phomotopy_of_eq_ap (f : ppi P p₀ → ppi P' p₀') (p : k = l) :
    phomotopy_of_eq (ap f p) = pap' f (phomotopy_of_eq p) :=
  begin induction p, exact !phomotopy_rec_idp_refl⁻¹ end
  end

  /- remove some duplicates: loop_ppmap_commute, loop_ppmap_pequiv, loop_ppmap_pequiv', pfunext -/
  definition pfunext (X Y : Type*) : ppmap X (Ω Y) ≃* Ω (ppmap X Y) :=
  (loop_ppmap_commute X Y)⁻¹ᵉ*

  definition loop_phomotopy [constructor] {A B : Type*} (f : A →* B) : Type* :=
  pointed.MK (f ~* f) phomotopy.rfl

  definition ppcompose_left_loop_phomotopy [constructor] {A B C : Type*} (g : B →* C) {f : A →* B}
    {h : A →* C} (p : g ∘* f ~* h) : loop_phomotopy f →* loop_phomotopy h :=
  pmap.mk (λq, p⁻¹* ⬝* pwhisker_left g q ⬝* p)
    (idp ◾** !pwhisker_left_refl ◾** idp ⬝ !trans_refl ◾** idp ⬝ !trans_left_inv)

  definition ppcompose_left_loop_phomotopy' [constructor] {A B C : Type*} (g : B →* C) (f : A →* B)
    : loop_phomotopy f →* loop_phomotopy (g ∘* f) :=
  pmap.mk (λq, pwhisker_left g q) !pwhisker_left_refl

  definition loop_ppmap_pequiv' [constructor] (A B : Type*) :
    Ω(ppmap A B) ≃* loop_phomotopy (pconst A B) :=
  pequiv_of_equiv (pmap_eq_equiv _ _) idp

  definition ppmap_loop_pequiv' [constructor] (A B : Type*) :
    loop_phomotopy (pconst A B) ≃* ppmap A (Ω B) :=
  pequiv_of_equiv (!phomotopy.sigma_char ⬝e !pmap.sigma_char⁻¹ᵉ) idp

  definition loop_ppmap_pequiv [constructor] (A B : Type*) : Ω(ppmap A B) ≃* ppmap A (Ω B) :=
  loop_ppmap_pequiv' A B ⬝e* ppmap_loop_pequiv' A B

  definition loop_ppmap_pequiv'_natural_right' {X X' : Type} (x₀ : X) (A : Type*) (f : X → X') :
    psquare (loop_ppmap_pequiv' A _) (loop_ppmap_pequiv' A _)
            (Ω→ (ppcompose_left (pmap_of_map f x₀)))
            (ppcompose_left_loop_phomotopy' (pmap_of_map f x₀) !pconst) :=
  begin
    fapply phomotopy.mk,
    { esimp, intro p,
     refine _ ⬝ ap011 (λx y, phomotopy_of_eq (ap1_gen _ x y _))
                 proof !eq_of_phomotopy_refl⁻¹ qed proof !eq_of_phomotopy_refl⁻¹ qed,
     refine _ ⬝ ap phomotopy_of_eq !ap1_gen_idp_left⁻¹,
     exact !phomotopy_of_eq_pcompose_left⁻¹ },
    { refine _ ⬝ !idp_con⁻¹, exact sorry }
  end

  definition loop_ppmap_pequiv'_natural_right {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (loop_ppmap_pequiv' A X) (loop_ppmap_pequiv' A X')
            (Ω→ (ppcompose_left f)) (ppcompose_left_loop_phomotopy f !pcompose_pconst) :=
  begin
    induction X' with X' x₀', induction f with f f₀, esimp at f, esimp at f₀, induction f₀,
    apply psquare_of_phomotopy,
    exact sorry
  end

  definition ppmap_loop_pequiv'_natural_right {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (ppmap_loop_pequiv' A X) (ppmap_loop_pequiv' A X')
            (ppcompose_left_loop_phomotopy f !pcompose_pconst) (ppcompose_left (Ω→ f)) :=
  begin
    exact sorry
  end

  definition loop_pmap_commute_natural_right_direct {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (loop_ppmap_pequiv A X) (loop_ppmap_pequiv A X')
            (Ω→ (ppcompose_left f)) (ppcompose_left (Ω→ f)) :=
  begin
    induction X' with X' x₀', induction f with f f₀, esimp at f, esimp at f₀, induction f₀,
--    refine _ ⬝* _ ◾* _, rotate 4,
    fapply phomotopy.mk,
    { intro p, esimp, esimp [pmap_eq_equiv, pcompose_pconst], exact sorry },
    { exact sorry }
  end

  definition loop_pmap_commute_natural_left {A A' : Type*} (X : Type*) (f : A' →* A) :
    psquare (loop_ppmap_commute A X) (loop_ppmap_commute A' X)
            (Ω→ (ppcompose_right f)) (ppcompose_right f) :=
  sorry

  definition loop_pmap_commute_natural_right {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (loop_ppmap_commute A X) (loop_ppmap_commute A X')
            (Ω→ (ppcompose_left f)) (ppcompose_left (Ω→ f)) :=
  loop_ppmap_pequiv'_natural_right A f ⬝h* ppmap_loop_pequiv'_natural_right A f

  /-
    Do we want to use a structure of homotopies between pointed homotopies? Or are equalities fine?
    If we set up things more generally, we could define this as
    "pointed homotopies between the dependent pointed maps p and q"
  -/
  structure phomotopy2 {A B : Type*} {f g : A →* B} (p q : f ~* g) : Type :=
    (homotopy_eq : p ~ q)
    (homotopy_pt_eq : whisker_right (respect_pt g) (homotopy_eq pt) ⬝ to_homotopy_pt q =
      to_homotopy_pt p)

  /- this sets it up more generally, for illustrative purposes -/
  structure ppi' (A : Type*) (P : A → Type) (p : P pt) :=
    (to_fun : Π a : A, P a)
    (resp_pt : to_fun (Point A) = p)
  attribute ppi'.to_fun [coercion]
  definition phomotopy' {A : Type*} {P : A → Type} {x : P pt} (f g : ppi' A P x) : Type :=
  ppi' A (λa, f a = g a) (ppi'.resp_pt f ⬝ (ppi'.resp_pt g)⁻¹)
  definition phomotopy2' {A : Type*} {P : A → Type} {x : P pt} {f g : ppi' A P x}
    (p q : phomotopy' f g) : Type :=
  phomotopy' p q

  -- infix ` ~*2 `:50 := phomotopy2

  -- variables {A B : Type*} {f g : A →* B} (p q : f ~* g)

  -- definition phomotopy_eq_equiv_phomotopy2 : p = q ≃ p ~*2 q :=
  -- sorry

  definition pconst_pcompose_phomotopy {A B C : Type*} {f f' : A →* B} (p : f ~* f') :
    pwhisker_left (pconst B C) p ⬝* pconst_pcompose f' = pconst_pcompose f :=
  begin
    fapply phomotopy_eq,
    { intro a, apply ap_constant },
    { induction p using phomotopy_rec_idp, induction B with B b₀, induction f with f f₀,
      esimp at *, induction f₀, reflexivity }
  end

/- Homotopy between a function and its eta expansion -/

  definition papply_point [constructor] (A B : Type*) : papply B pt ~* pconst (ppmap A B) B :=
  phomotopy.mk (λf, respect_pt f) idp

  definition pmap_swap_map [constructor] {A B C : Type*} (f : A →* ppmap B C) :
    ppmap B (ppmap A C) :=
  begin
    fapply pmap.mk,
    { intro b, exact papply C b ∘* f },
    { apply eq_of_phomotopy, exact pwhisker_right f (papply_point B C) ⬝* !pconst_pcompose }
  end

  definition pmap_swap_map_pconst (A B C : Type*) :
    pmap_swap_map (pconst A (ppmap B C)) ~* pconst B (ppmap A C) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro b, reflexivity },
    { refine !refl_trans ⬝ !phomotopy_of_eq_of_phomotopy⁻¹ }
  end

  definition papply_pmap_swap_map [constructor] {A B C : Type*} (f : A →* ppmap B C) (a : A) :
    papply C a ∘* pmap_swap_map f ~* f a :=
  begin
    fapply phomotopy.mk,
    { intro b, reflexivity },
    { exact !idp_con ⬝ !ap_eq_of_phomotopy⁻¹ }
  end

  definition pmap_swap_map_pmap_swap_map {A B C : Type*} (f : A →* ppmap B C) :
    pmap_swap_map (pmap_swap_map f) ~* f :=
  begin
    fapply phomotopy_mk_ppmap,
    { exact papply_pmap_swap_map f },
    { refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      fapply phomotopy_mk_eq, intro b, exact !idp_con,
      refine !whisker_right_idp ◾ (!idp_con ◾ idp) ⬝ _ ⬝ !idp_con⁻¹ ◾ idp,
      symmetry, exact sorry }
  end

  definition pmap_swap [constructor] (A B C : Type*) : ppmap A (ppmap B C) →* ppmap B (ppmap A C) :=
  begin
    fapply pmap.mk,
    { exact pmap_swap_map },
    { exact eq_of_phomotopy (pmap_swap_map_pconst A B C) }
  end

  definition pmap_swap_pequiv [constructor] (A B C : Type*) :
    ppmap A (ppmap B C) ≃* ppmap B (ppmap A C) :=
  begin
    fapply pequiv_of_pmap,
    { exact pmap_swap A B C },
    fapply adjointify,
    { exact pmap_swap B A C },
    { intro f, apply eq_of_phomotopy, exact pmap_swap_map_pmap_swap_map f },
    { intro f, apply eq_of_phomotopy, exact pmap_swap_map_pmap_swap_map f }
  end

  -- this should replace pnatural_square
  definition pnatural_square2 {A B : Type} (X : B → Type*) (Y : B → Type*) {f g : A → B}
    (h : Πa, X (f a) →* Y (g a)) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X (ap f p) ~* ptransport Y (ap g p) ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  definition ptransport_ap {A B : Type} (X : B → Type*) (f : A → B) {a a' : A} (p : a = a') :
    ptransport X (ap f p) ~* ptransport (X ∘ f) p :=
  by induction p; reflexivity

  definition ptransport_constant (A : Type) (B : Type*) {a a' : A} (p : a = a') :
    ptransport (λ(a : A), B) p ~* pid B :=
  by induction p; reflexivity

  definition ptransport_natural {A : Type} (X : A → Type*) (Y : A → Type*)
    (h : Πa, X a →* Y a) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X p ~* ptransport Y p ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  section psquare
  variables {A A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type*}
            {f₁₀ f₁₀' : A₀₀ →* A₂₀} {f₃₀ : A₂₀ →* A₄₀}
            {f₀₁ f₀₁' : A₀₀ →* A₀₂} {f₂₁ f₂₁' : A₂₀ →* A₂₂} {f₄₁ f₄₁' : A₄₀ →* A₄₂}
            {f₁₂ f₁₂' : A₀₂ →* A₂₂} {f₃₂ : A₂₂ →* A₄₂}
            {f₀₃ : A₀₂ →* A₀₄} {f₂₃ : A₂₂ →* A₂₄} {f₄₃ : A₄₂ →* A₄₄}
            {f₁₄ f₁₄' : A₀₄ →* A₂₄} {f₃₄ : A₂₄ →* A₄₄}

  definition phconst_square (f₀₁ : A₀₀ →* A₀₂) (f₂₁ : A₂₀ →* A₂₂) :
    psquare (pconst A₀₀ A₂₀) (pconst A₀₂ A₂₂) f₀₁ f₂₁ :=
  !pcompose_pconst ⬝* !pconst_pcompose⁻¹*

  definition pvconst_square (f₁₀ : A₀₀ →* A₂₀) (f₁₂ : A₀₂ →* A₂₂) :
    psquare f₁₀ f₁₂ (pconst A₀₀ A₀₂) (pconst A₂₀ A₂₂) :=
  !pconst_pcompose ⬝* !pcompose_pconst⁻¹*

  definition pvconst_square_pcompose (f₃₀ : A₂₀ →* A₄₀) (f₁₀ : A₀₀ →* A₂₀)
    (f₃₂ : A₂₂ →* A₄₂) (f₁₂ : A₀₂ →* A₂₂) :
    pvconst_square (f₃₀ ∘* f₁₀) (f₃₂ ∘* f₁₂) = pvconst_square f₁₀ f₁₂ ⬝h* pvconst_square f₃₀ f₃₂ :=
  begin
    refine eq_right_of_phsquare !passoc_pconst_left ◾** !passoc_pconst_right⁻¹⁻²** ⬝ idp ◾**
      (!trans_symm ⬝ !trans_symm ◾** idp) ⬝ !trans_assoc⁻¹ ⬝ _ ◾** idp,
    refine !trans_assoc⁻¹ ⬝ _ ◾** !pwhisker_left_symm⁻¹ ⬝ !trans_assoc ⬝
      idp ◾** !pwhisker_left_trans⁻¹,
    apply trans_symm_eq_of_eq_trans,
    refine _ ⬝ idp ◾** !passoc_pconst_middle⁻¹ ⬝ !trans_assoc⁻¹ ⬝ !trans_assoc⁻¹,
    refine _ ◾** idp ⬝ !trans_assoc,
    refine idp ◾** _ ⬝ !trans_assoc⁻¹,
    refine ap (pwhisker_right f₁₀) _ ⬝ !pwhisker_right_trans,
    refine !trans_refl⁻¹ ⬝ idp ◾** !trans_left_inv⁻¹ ⬝ !trans_assoc⁻¹,
  end

  definition phconst_square_pcompose (f₀₃ : A₀₂ →* A₀₄) (f₁₀ : A₀₀ →* A₂₀)
    (f₂₃ : A₂₂ →* A₂₄) (f₂₁ : A₂₀ →* A₂₂) :
    phconst_square (f₀₃ ∘* f₀₁) (f₂₃ ∘* f₁₂) = phconst_square f₀₁ f₁₂ ⬝v* phconst_square f₀₃ f₂₃ :=
  sorry

  definition ptranspose (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : psquare f₀₁ f₂₁ f₁₀ f₁₂ :=
  p⁻¹*

  definition hsquare_of_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : hsquare f₁₀ f₁₂ f₀₁ f₂₁ :=
  p

  definition rfl_phomotopy_hconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : phomotopy.rfl ⬝ph* p = p :=
  idp ◾** (ap (pwhisker_left f₁₂) !refl_symm ⬝ !pwhisker_left_refl) ⬝ !trans_refl

  definition hconcat_phomotopy_rfl (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : p ⬝hp* phomotopy.rfl = p :=
  !pwhisker_right_refl ◾** idp ⬝ !refl_trans

  definition rfl_phomotopy_vconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : phomotopy.rfl ⬝pv* p = p :=
  !pwhisker_left_refl ◾** idp ⬝ !refl_trans

  definition vconcat_phomotopy_rfl (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : p ⬝vp* phomotopy.rfl = p :=
  idp ◾** (ap (pwhisker_right f₀₁) !refl_symm ⬝ !pwhisker_right_refl) ⬝ !trans_refl

  definition phomotopy_hconcat_phconcat (p : f₀₁' ~* f₀₁) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (r : psquare f₃₀ f₃₂ f₂₁ f₄₁) : (p ⬝ph* q) ⬝h* r = p ⬝ph* (q ⬝h* r) :=
  begin
    induction p using phomotopy_rec_idp,
    exact !refl_phomotopy_hconcat ◾h* idp ⬝ !refl_phomotopy_hconcat⁻¹
  end

  definition phconcat_hconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (q : psquare f₃₀ f₃₂ f₂₁ f₄₁) (r : f₄₁' ~* f₄₁) : (p ⬝h* q) ⬝hp* r = p ⬝h* (q ⬝hp* r) :=
  begin
    induction r using phomotopy_rec_idp,
    exact !hconcat_phomotopy_rfl ⬝ idp ◾h* !hconcat_phomotopy_rfl⁻¹
  end

  definition phomotopy_hconcat_phomotopy (p : f₀₁' ~* f₀₁) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (r : f₂₁' ~* f₂₁) : (p ⬝ph* q) ⬝hp* r = p ⬝ph* (q ⬝hp* r) :=
  begin
    induction r using phomotopy_rec_idp,
    exact !hconcat_phomotopy_rfl ⬝ idp ◾ph* !hconcat_phomotopy_rfl⁻¹
  end

  definition hconcat_phomotopy_phconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (q : f₂₁' ~* f₂₁) (r : psquare f₃₀ f₃₂ f₂₁' f₄₁) : (p ⬝hp* q) ⬝h* r = p ⬝h* (q⁻¹* ⬝ph* r) :=
  begin
    induction q using phomotopy_rec_idp,
    exact !hconcat_phomotopy_rfl ◾h* idp ⬝ idp ◾h* (!refl_symm ◾ph* idp ⬝ !refl_phomotopy_hconcat)⁻¹
  end

  definition phconcat_phomotopy_hconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (q : f₂₁ ~* f₂₁') (r : psquare f₃₀ f₃₂ f₂₁' f₄₁) : p ⬝h* (q ⬝ph* r) = (p ⬝hp* q⁻¹*) ⬝h* r :=
  begin
    induction q using phomotopy_rec_idp,
    exact idp ◾h* !refl_phomotopy_hconcat ⬝ (idp ◾hp* !refl_symm ⬝ !hconcat_phomotopy_rfl)⁻¹ ◾h* idp
  end

  definition hconcat_phomotopy_hconcat_cancel (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (q : f₂₁' ~* f₂₁) (r : psquare f₃₀ f₃₂ f₂₁ f₄₁) : (p ⬝hp* q) ⬝h* (q ⬝ph* r) = p ⬝h* r :=
  begin
    induction q using phomotopy_rec_idp,
    exact !hconcat_phomotopy_rfl ◾h* !refl_phomotopy_hconcat
  end

  definition phomotopy_hconcat_phinverse {f₁₀ : A₀₀ ≃* A₂₀} {f₁₂ : A₀₂ ≃* A₂₂}
    (p : f₀₁' ~* f₀₁) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁) : (p ⬝ph* q)⁻¹ʰ* = q⁻¹ʰ* ⬝hp* p :=
  begin
    induction p using phomotopy_rec_idp,
    exact !refl_phomotopy_hconcat⁻²ʰ* ⬝ !hconcat_phomotopy_rfl⁻¹
  end

  definition hconcat_phomotopy_phinverse {f₁₀ : A₀₀ ≃* A₂₀} {f₁₂ : A₀₂ ≃* A₂₂}
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₂₁' ~* f₂₁) : (p ⬝hp* q)⁻¹ʰ* = q ⬝ph* p⁻¹ʰ* :=
  begin
    induction q using phomotopy_rec_idp,
    exact !hconcat_phomotopy_rfl⁻²ʰ* ⬝ !refl_phomotopy_hconcat⁻¹
  end

  definition pvconst_square_phinverse (f₁₀ : A₀₀ ≃* A₂₀) (f₁₂ : A₀₂ ≃* A₂₂) :
    (pvconst_square f₁₀ f₁₂)⁻¹ʰ* = pvconst_square f₁₀⁻¹ᵉ* f₁₂⁻¹ᵉ* :=
  begin
    exact sorry
  end

  definition ppcompose_left_phomotopy_hconcat (A : Type*) (p : f₀₁' ~* f₀₁)
    (q : psquare f₁₀ f₁₂ f₀₁ f₂₁) : ppcompose_left_psquare (p ⬝ph* q) =
    @ppcompose_left_phomotopy A _ _ _ _ p ⬝ph* ppcompose_left_psquare q :=
  sorry --used

  definition ppcompose_left_hconcat_phomotopy (A : Type*) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (q : f₂₁' ~* f₂₁) : ppcompose_left_psquare (p ⬝hp* q) =
    ppcompose_left_psquare p ⬝hp* @ppcompose_left_phomotopy A _ _ _ _ q :=
  sorry

  definition ppcompose_left_pvconst_square (A : Type*) (f₁₀ : A₀₀ →* A₂₀) (f₁₂ : A₀₂ →* A₂₂) :
    ppcompose_left_psquare (pvconst_square f₁₀ f₁₂) =
    !ppcompose_left_pconst ⬝ph* pvconst_square (ppcompose_left f₁₀) (@ppcompose_left A _ _ f₁₂) ⬝hp*
    !ppcompose_left_pconst :=
  sorry

  end psquare

  definition ap1_pequiv_ap {A : Type} (B : A → Type*) {a a' : A} (p : a = a') :
    Ω→ (pequiv_ap B p) ~* pequiv_ap (Ω ∘ B) p :=
  begin induction p, apply ap1_pid end

  definition pequiv_ap_natural {A : Type} (B C : A → Type*) {a a' : A} (p : a = a')
    (f : Πa, B a →* C a) :
    psquare (pequiv_ap B p) (pequiv_ap C p) (f a) (f a') :=
  begin induction p, exact phrfl end

  definition is_contr_loop (A : Type*) [is_set A] : is_contr (Ω A) :=
  is_contr.mk idp (λa, !is_prop.elim)

  definition is_contr_loop_of_is_contr {A : Type*} (H : is_contr A) : is_contr (Ω A) :=
  is_contr_loop A

  definition is_contr_punit [instance] : is_contr punit :=
  is_contr_unit

  definition pequiv_of_is_contr (A B : Type*) (HA : is_contr A) (HB : is_contr B) : A ≃* B :=
  pequiv_punit_of_is_contr A _ ⬝e* (pequiv_punit_of_is_contr B _)⁻¹ᵉ*

  definition loop_pequiv_punit_of_is_set (X : Type*) [is_set X] : Ω X ≃* punit :=
  pequiv_punit_of_is_contr _ (is_contr_loop X)

  definition loop_punit : Ω punit ≃* punit :=
  loop_pequiv_punit_of_is_set punit

  definition add_point_functor' [unfold 4] {A B : Type} (e : A → B) (a : A₊) : B₊ :=
  begin induction a with a, exact none, exact some (e a) end

  definition add_point_functor [constructor] {A B : Type} (e : A → B) : A₊ →* B₊ :=
  pmap.mk (add_point_functor' e) idp

  definition add_point_functor_compose {A B C : Type} (f : B → C) (e : A → B) :
    add_point_functor (f ∘ e) ~* add_point_functor f ∘* add_point_functor e :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x: reflexivity },
    reflexivity
  end

  definition add_point_functor_id (A : Type) :
    add_point_functor id ~* pid A₊ :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x: reflexivity },
    reflexivity
  end

  definition add_point_functor_phomotopy {A B : Type} {e e' : A → B} (p : e ~ e') :
    add_point_functor e ~* add_point_functor e' :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with a, reflexivity, exact ap some (p a) },
    reflexivity
  end

  definition add_point_pequiv {A B : Type} (e : A ≃ B) : A₊ ≃* B₊ :=
  pequiv.MK (add_point_functor e) (add_point_functor e⁻¹ᵉ)
    abstract !add_point_functor_compose⁻¹* ⬝* add_point_functor_phomotopy (left_inv e) ⬝*
      !add_point_functor_id end
    abstract !add_point_functor_compose⁻¹* ⬝* add_point_functor_phomotopy (right_inv e) ⬝*
      !add_point_functor_id end

  definition add_point_over [unfold 3] {A : Type} (B : A → Type*) : A₊ → Type*
  | (some a) := B a
  | none     := plift punit

  definition add_point_over_pequiv {A : Type} {B B' : A → Type*} (e : Πa, B a ≃* B' a) :
    Π(a : A₊), add_point_over B a ≃* add_point_over B' a
  | (some a) := e a
  | none     := pequiv.rfl

  definition phomotopy_group_plift_punit.{u} (n : ℕ) [H : is_at_least_two n] :
    πag[n] (plift.{0 u} punit) ≃g trivial_ab_group_lift.{u} :=
  begin
    induction H with n,
    have H : 0 <[ℕ] n+2, from !zero_lt_succ,
    have is_set unit, from _,
    have is_trunc (trunc_index.of_nat 0) punit, from this,
    exact isomorphism_of_is_contr (@trivial_homotopy_group_of_is_trunc _ _ _ !is_trunc_lift H)
      !is_trunc_lift
  end

  definition pmap_of_map_pt [constructor] {A : Type*} {B : Type} (f : A → B) :
    A →* pointed.MK B (f pt) :=
  pmap.mk f idp

  definition papply_natural_right [constructor] {A B B' : Type*} (f : B →* B') (a : A) :
    psquare (papply B a) (papply B' a) (ppcompose_left f) f :=
  begin
    fapply phomotopy.mk,
    { intro g, reflexivity },
    { refine !idp_con ⬝ !ap_eq_of_phomotopy ⬝ !idp_con⁻¹ }
  end

  -- definition foo {A B : Type} {f : A → B} {a₀ a₁ a₂ : A} {b₀ b₁ b₂ : B}
  --   {p₀ : a₀ = a₀} {p₁ : a₀ = a₀} (q₀ : ap f p₀ = idp) (q₁ : ap f p₁ = idp) :
  --   whisker_right (ap f p₁) (idp_con (ap f p₀⁻¹) ⬝ !ap_inv ⬝ q₀⁻²)⁻¹ ⬝ !con.assoc ⬝
  --   whisker_left idp (con_eq_of_eq_con_inv (eq_con_inv_of_con_eq _)) ⬝ _
  --   = !idp_con ⬝ q₁ :=
  -- _

/-
whisker_right
    (ap (λ f, pppi.to_fun f a)
       (eq_of_phomotopy (pcompose_pconst (pconst B B'))))
    (idp_con
       (ap (λ y, pppi.to_fun y a)
          (eq_of_phomotopy
             (pconst_pcompose (ppi_const (λ a, B))))⁻¹) ⬝ ap_inv
       (λ y, pppi.to_fun y a)
       (eq_of_phomotopy
          (pconst_pcompose (ppi_const (λ a, B)))) ⬝ inverse2
       (ap_eq_of_phomotopy (pconst_pcompose (ppi_const (λ a, B)))
          a))⁻¹ ⬝ (con.assoc
     (ppi.to_fun (pvconst_square (papply B a) (papply B' a))
        (ppi_const (λ a, B)))
     (ap (λ f, pppi.to_fun f a)
        (eq_of_phomotopy (pconst_pcompose (ppi_const (λ a, B))))⁻¹)
     (ap (λ f, pppi.to_fun f a)
        (eq_of_phomotopy
           (pcompose_pconst (pconst B B')))) ⬝ whisker_left
     (ppi.to_fun (pvconst_square (papply B a) (papply B' a))
        (ppi_const (λ a, B)))
     (con_eq_of_eq_con_inv
        (eq_con_inv_of_con_eq
           (pwhisker_left_1 B' (ppmap A B) (ppmap A B') (papply B' a)
              (pconst (ppmap A B) (ppmap A B'))
              (ppcompose_left (pconst B B'))
              (ppcompose_left_pconst A B B')⁻¹*))) ⬝ respect_pt
     (pvconst_square (papply B a) (papply B' a))) = idp_con
    (ap (λ f, pppi.to_fun f a)
       (eq_of_phomotopy
          (pcompose_pconst (pconst B B')))) ⬝ ap_eq_of_phomotopy
    (pcompose_pconst (pconst B B'))
    a
-/



  definition papply_natural_right_pconst {A : Type*} (B B' : Type*) (a : A) :
    papply_natural_right (pconst B B') a = !ppcompose_left_pconst ⬝ph* !pvconst_square :=
  begin
    fapply phomotopy_mk_eq,
    { intro g, symmetry, refine !idp_con ⬝ !ap_inv ⬝ !ap_eq_of_phomotopy⁻² },
    {

      esimp [pvconst_square],
    --esimp [inv_con_eq_of_eq_con, pwhisker_left_1]
      exact sorry }
  end


  /- TODO: computation rule -/
  open pi
  definition fiberwise_pointed_map_rec {A : Type} {B : A → Type*}
    (P : Π(C : A → Type*) (g : Πa, B a →* C a), Type)
    (H : Π(C : A → Type) (g : Πa, B a → C a), P _ (λa, pmap_of_map_pt (g a))) :
    Π⦃C : A → Type*⦄ (g : Πa, B a →* C a), P C g :=
  begin
    refine equiv_rect (!sigma_pi_equiv_pi_sigma ⬝e
             arrow_equiv_arrow_right A !pType.sigma_char⁻¹ᵉ) _ _,
    intro R, cases R with R r₀,
    refine equiv_rect (!sigma_pi_equiv_pi_sigma ⬝e
            pi_equiv_pi_right (λa, !pmap.sigma_char⁻¹ᵉ)) _ _,
    intro g, cases g with g g₀, esimp at (g, g₀),
    revert g₀, change (Π(g : (λa, g a (Point (B a))) ~ r₀), _),
    refine homotopy.rec_idp _ _, esimp,
    apply H
  end

definition ap1_gen_idp_eq {A B : Type} (f : A → B) {a : A} (q : f a = f a) (r : q = idp) :
  ap1_gen_idp f q = ap (λx, ap1_gen f x x idp) r :=
begin cases r, reflexivity end

definition pointed_change_point [constructor] (A : Type*) {a : A} (p : a = pt) :
  pointed.MK A a ≃* A :=
pequiv_of_eq_pt p ⬝e* (pointed_eta_pequiv A)⁻¹ᵉ*

definition change_path_psquare {A B : Type*} (f : A →* B)
  {a' : A} {b' : B} (p : a' = pt) (q : pt = b') :
  psquare (pointed_change_point _ p)
          (pointed_change_point _ q⁻¹)
          (pmap.mk f (ap f p ⬝ respect_pt f ⬝ q)) f :=
begin
  fapply phomotopy.mk, exact homotopy.rfl,
  exact !idp_con ⬝ !ap_id ◾ !ap_id ⬝ !con_inv_cancel_right ⬝ whisker_right _ (ap02 f !ap_id⁻¹)
end

definition change_path_psquare_cod {A B : Type*} (f : A →* B) {b' : B} (p : pt = b') :
  f ~* pointed_change_point _ p⁻¹ ∘* pmap.mk f (respect_pt f ⬝ p) :=
begin
  fapply phomotopy.mk, exact homotopy.rfl, exact !idp_con ⬝ !ap_id ◾ !ap_id ⬝ !con_inv_cancel_right
end

definition change_path_psquare_cod' {A B : Type} (f : A → B) (a : A) {b' : B} (p : f a = b') :
  pointed_change_point _ p ∘* pmap_of_map f a ~* pmap.mk f p :=
begin
  fapply phomotopy.mk, exact homotopy.rfl, refine whisker_left idp (ap_id p)⁻¹
end


end pointed
