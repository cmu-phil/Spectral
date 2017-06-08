/- equalities between pointed homotopies and other facts about pointed types/functions/homotopies -/

-- Author: Floris van Doorn

import types.pointed2

open pointed eq equiv function is_equiv unit is_trunc trunc nat algebra sigma group

namespace pointed

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

  definition pmap_eq_idp {X Y : Type*} (f : X →* Y) :
    pmap_eq (λx, idpath (f x)) !idp_con⁻¹ = idpath f :=
  ap (λx, eq_of_phomotopy (phomotopy.mk _ x)) !inv_inv ⬝ eq_of_phomotopy_refl f

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
  definition ppi_homotopy' {A : Type*} {P : A → Type} {x : P pt} (f g : ppi' A P x) : Type :=
  ppi' A (λa, f a = g a) (ppi'.resp_pt f ⬝ (ppi'.resp_pt g)⁻¹)
  definition ppi_homotopy2' {A : Type*} {P : A → Type} {x : P pt} {f g : ppi' A P x}
    (p q : ppi_homotopy' f g) : Type :=
  ppi_homotopy' p q

  -- infix ` ~*2 `:50 := phomotopy2

  -- variables {A B : Type*} {f g : A →* B} (p q : f ~* g)

  -- definition phomotopy_eq_equiv_phomotopy2 : p = q ≃ p ~*2 q :=
  -- sorry

/- Homotopy between a function and its eta expansion -/

  definition pmap_eta {X Y : Type*} (f : X →* Y) : f ~* pmap.mk f (pmap.resp_pt f) :=
  begin
    fapply phomotopy.mk,
    reflexivity,
    esimp, exact !idp_con
  end

end pointed
