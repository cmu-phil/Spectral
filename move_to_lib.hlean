-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2

open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group

attribute equiv.symm equiv.trans is_equiv.is_equiv_ap fiber.equiv_postcompose fiber.equiv_precompose pequiv.to_pmap pequiv._trans_of_to_pmap ghomotopy_group_succ_in isomorphism_of_eq [constructor]
attribute is_equiv.eq_of_fn_eq_fn' [unfold 3]
attribute isomorphism._trans_of_to_hom [unfold 3]
attribute homomorphism.struct [unfold 3]
attribute pequiv.trans pequiv.symm [constructor]

namespace sigma

  definition sigma_equiv_sigma_left' [constructor] {A A' : Type} {B : A' → Type} (Hf : A ≃ A') : (Σa, B (Hf a)) ≃ (Σa', B a') :=
    sigma_equiv_sigma Hf (λa, erfl)

end sigma
open sigma

namespace group
  open is_trunc
  definition pSet_of_Group (G : Group) : Set* := ptrunctype.mk G _ 1

  definition pmap_of_isomorphism [constructor] {G₁ : Group} {G₂ : Group}
    (φ : G₁ ≃g G₂) : pType_of_Group G₁ →* pType_of_Group G₂ :=
  pequiv_of_isomorphism φ

  definition pequiv_of_isomorphism_of_eq {G₁ G₂ : Group} (p : G₁ = G₂) :
    pequiv_of_isomorphism (isomorphism_of_eq p) = pequiv_of_eq (ap pType_of_Group p) :=
  begin
    induction p,
    apply pequiv_eq,
    fapply pmap_eq,
    { intro g, reflexivity},
    { apply is_prop.elim}
  end

  definition homomorphism_change_fun [constructor] {G₁ G₂ : Group}
    (φ : G₁ →g G₂) (f : G₁ → G₂) (p : φ ~ f) : G₁ →g G₂ :=
  homomorphism.mk f (λg h, (p (g * h))⁻¹ ⬝ to_respect_mul φ g h ⬝ ap011 mul (p g) (p h))

end group open group

namespace pi -- move to types.arrow

  definition pmap_eq_idp {X Y : Type*} (f : X →* Y) :
    pmap_eq (λx, idpath (f x)) !idp_con⁻¹ = idpath f :=
  begin
    cases f with f p, esimp [pmap_eq],
    refine apd011 (apd011 pmap.mk) !eq_of_homotopy_idp _,
    exact sorry
  end

  definition pfunext [constructor] (X Y : Type*) : ppmap X (Ω Y) ≃* Ω (ppmap X Y) :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK: esimp,
      { intro f, fapply pmap_eq,
        { intro x, exact f x },
        { exact (respect_pt f)⁻¹ }},
      { intro p, fapply pmap.mk,
        { intro x, exact ap010 pmap.to_fun p x },
        { note z := apd respect_pt p,
          note z2 := square_of_pathover z,
          refine eq_of_hdeg_square z2 ⬝ !ap_constant }},
      { intro p, exact sorry },
      { intro p, exact sorry }},
    { apply pmap_eq_idp}
  end


end pi open pi

namespace eq

  definition pathover_eq_Fl' {A B : Type} {f : A → B} {a₁ a₂ : A} {b : B} (p : a₁ = a₂) (q : f a₂ = b) : (ap f p) ⬝ q =[p] q :=
  by induction p; induction q; exact idpo

end eq open eq

namespace pointed

  definition pequiv_compose {A B C : Type*} (g : B ≃* C) (f : A ≃* B) : A ≃* C :=
    pequiv_of_pmap (g ∘* f) (is_equiv_compose g f)

  infixr ` ∘*ᵉ `:60 := pequiv_compose

  definition pmap.sigma_char [constructor] {A B : Type*} : (A →* B) ≃ Σ(f : A → B), f pt = pt :=
  begin
    fapply equiv.MK : intros f,
    { exact ⟨to_fun f , resp_pt f⟩ },
    all_goals cases f with f p,
    { exact pmap.mk f p },
    all_goals reflexivity
  end

  definition phomotopy.sigma_char [constructor] {A B : Type*} (f g : A →* B) : (f ~* g) ≃ Σ(p : f ~ g), p pt ⬝ resp_pt g = resp_pt f :=
  begin
    fapply equiv.MK : intros h,
    { exact ⟨h , to_homotopy_pt h⟩ },
    all_goals cases h with h p,
    { exact phomotopy.mk h p },
    all_goals reflexivity
  end

  definition pmap_eq_equiv {A B : Type*} (f g : A →* B) : (f = g) ≃ (f ~* g) :=
    calc (f = g) ≃ pmap.sigma_char f = pmap.sigma_char g
                   : eq_equiv_fn_eq pmap.sigma_char f g
            ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), pathover (λh, h pt = pt) (resp_pt f) p (resp_pt g)
                   : sigma_eq_equiv _ _
            ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), resp_pt f = ap (λh, h pt) p ⬝ resp_pt g
                   : sigma_equiv_sigma_right (λp, pathover_eq_equiv_Fl p (resp_pt f) (resp_pt g))
            ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), resp_pt f = ap10 p pt ⬝ resp_pt g
                   : sigma_equiv_sigma_right (λp, equiv_eq_closed_right _ (whisker_right (ap_eq_apd10 p _) _))
            ...  ≃ Σ(p : pmap.to_fun f ~ pmap.to_fun g), resp_pt f = p pt ⬝ resp_pt g
                   : sigma_equiv_sigma_left' eq_equiv_homotopy
            ...  ≃ Σ(p : pmap.to_fun f ~ pmap.to_fun g), p pt ⬝ resp_pt g = resp_pt f
                   : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
            ...  ≃ (f ~* g) : phomotopy.sigma_char f g

  definition loop_pmap_commute (A B : Type*) : Ω(ppmap A B) ≃* (ppmap A (Ω B)) :=
    pequiv_of_equiv
      (calc Ω(ppmap A B) /- ≃ (pconst A B = pconst A B)                        : erfl
                     ... -/ ≃ (pconst A B ~* pconst A B)                       : pmap_eq_equiv _ _
                     ...    ≃ Σ(p : pconst A B ~ pconst A B), p pt ⬝ rfl = rfl : phomotopy.sigma_char
                     ... /- ≃ Σ(f : A → Ω B), f pt = pt                        : erfl
                     ... -/ ≃ (A →* Ω B)                                       : pmap.sigma_char)
      (by reflexivity)

  -- definition ppcompose_left {A B C : Type*} (g : B →* C) : ppmap A B →* ppmap A C :=
  --   pmap.mk (pcompose g) (eq_of_phomotopy (phomotopy.mk (λa, resp_pt g) (idp_con _)⁻¹))

  -- definition is_equiv_ppcompose_left [instance] {A B C : Type*} (g : B →* C) [H : is_equiv g] : is_equiv (@ppcompose_left A B C g) :=
  -- begin
  --   fapply is_equiv.adjointify,
  --   { exact (ppcompose_left (pequiv_of_pmap g H)⁻¹ᵉ*) },
  --   all_goals (intros f; esimp; apply eq_of_phomotopy),
  --   { exact calc g ∘* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* f) ~* (g ∘* (pequiv_of_pmap g H)⁻¹ᵉ*) ∘* f : passoc
  --                                                 ... ~* pid _ ∘* f : pwhisker_right f (pright_inv (pequiv_of_pmap g H))
  --                                                 ... ~* f : pid_pcompose f },
  --   { exact calc (pequiv_of_pmap g H)⁻¹ᵉ* ∘* (g ∘* f) ~* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* g) ∘* f : passoc
  --                                                 ... ~* pid _ ∘* f : pwhisker_right f (pleft_inv (pequiv_of_pmap g H))
  --                                                 ... ~* f : pid_pcompose f }
  -- end

  -- definition pequiv_ppcompose_left {A B C : Type*} (g : B ≃* C) : ppmap A B ≃* ppmap A C :=
  --   pequiv_of_pmap (ppcompose_left g) _

  -- definition pcompose_pconst {A B C : Type*} (f : B →* C) : f ∘* pconst A B ~* pconst A C :=
  --   phomotopy.mk (λa, respect_pt f) (idp_con _)⁻¹

  -- definition pconst_pcompose {A B C : Type*} (f : A →* B) : pconst B C ∘* f ~* pconst A C :=
  --   phomotopy.mk (λa, rfl) (ap_constant _ _)⁻¹

  definition ap1_pconst (A B : Type*) : Ω→(pconst A B) ~* pconst (Ω A) (Ω B) :=
    phomotopy.mk (λp, idp_con _ ⬝ ap_constant p pt) rfl

  definition loop_ppi_commute {A : Type} (B : A → Type*) : Ω(ppi B) ≃* Π*a, Ω (B a) :=
    pequiv_of_equiv eq_equiv_homotopy rfl

  definition equiv_ppi_right {A : Type} {P Q : A → Type*} (g : Πa, P a ≃* Q a)
    : (Π*a, P a) ≃* (Π*a, Q a) :=
    pequiv_of_equiv (pi_equiv_pi_right g)
      begin esimp, apply eq_of_homotopy, intros a, esimp, exact (respect_pt (g a)) end

  definition pcast_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pcast (ap C p) ∘* f a₁ ~* f a₂ ∘* pcast (ap B p) :=
  phomotopy.mk
    begin induction p, reflexivity end
    begin induction p, esimp, refine !idp_con ⬝ !idp_con ⬝ !ap_id⁻¹ end

  definition pequiv_of_eq_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pequiv_of_eq (ap C p) ∘* f a₁ ~* f a₂ ∘* pequiv_of_eq (ap B p) :=
  pcast_commute f p

end pointed

namespace fiber

  definition pfiber_loop_space {A B : Type*} (f : A →* B) : pfiber (Ω→ f) ≃* Ω (pfiber f) :=
    pequiv_of_equiv
    (calc pfiber (Ω→ f) ≃ Σ(p : Point A = Point A), ap1 f p = rfl                                : (fiber.sigma_char (ap1 f) (Point (Ω B)))
                    ... ≃ Σ(p : Point A = Point A), (respect_pt f) = ap f p ⬝ (respect_pt f)      : (sigma_equiv_sigma_right (λp,
                              calc (ap1 f p = rfl) ≃ !respect_pt⁻¹ ⬝ (ap f p ⬝ !respect_pt) = rfl : equiv_eq_closed_left _ (con.assoc _ _ _)
                                               ... ≃ ap f p ⬝ (respect_pt f) = (respect_pt f)     : eq_equiv_inv_con_eq_idp
                                               ... ≃ (respect_pt f) = ap f p ⬝ (respect_pt f)     : eq_equiv_eq_symm))
                    ... ≃ fiber.mk (Point A) (respect_pt f) = fiber.mk pt (respect_pt f)          : fiber_eq_equiv
                    ... ≃ Ω (pfiber f)                                                            : erfl)
    (begin cases f with f p, cases A with A a, cases B with B b, esimp at p, esimp at f, induction p, reflexivity end)

  definition pfiber_equiv_of_phomotopy {A B : Type*} {f g : A →* B} (h : f ~* g) : pfiber f ≃* pfiber g :=
  begin
    fapply pequiv_of_equiv,
    { refine (fiber.sigma_char f pt ⬝e _ ⬝e (fiber.sigma_char g pt)⁻¹ᵉ),
      apply sigma_equiv_sigma_right, intros a,
      apply equiv_eq_closed_left, apply (to_homotopy h) },
    { refine (fiber_eq rfl _),
      change (h pt)⁻¹ ⬝ respect_pt f = idp ⬝ respect_pt g,
      rewrite idp_con, apply inv_con_eq_of_eq_con, symmetry, exact (to_homotopy_pt h) }
  end

  definition transport_fiber_equiv [constructor] {A B : Type} (f : A → B) {b1 b2 : B} (p : b1 = b2) : fiber f b1 ≃ fiber f b2 :=
    calc fiber f b1 ≃ Σa, f a = b1 : fiber.sigma_char
               ...  ≃ Σa, f a = b2 : sigma_equiv_sigma_right (λa, equiv_eq_closed_right (f a) p)
               ...  ≃ fiber f b2   : fiber.sigma_char

  definition pequiv_postcompose {A B B' : Type*} (f : A →* B) (g : B ≃* B') : pfiber (g ∘* f) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine transport_fiber_equiv (g ∘* f) (respect_pt g)⁻¹ ⬝e fiber.equiv_postcompose f g (Point B),
    esimp, apply (ap (fiber.mk (Point A))), refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
    rewrite [con.assoc, con.right_inv, con_idp, -ap_compose'], apply ap_con_eq_con
  end

  definition pequiv_precompose {A A' B : Type*} (f : A →* B) (g : A' ≃* A) : pfiber (f ∘* g) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine fiber.equiv_precompose f g (Point B),
    esimp, apply (eq_of_fn_eq_fn (fiber.sigma_char _ _)), fapply sigma_eq: esimp,
    { apply respect_pt g },
    { apply pathover_eq_Fl' }
  end

  definition pfiber_equiv_of_square {A B C D : Type*} {f : A →* B} {g : C →* D} {h : A ≃* C} {k : B ≃* D} (s : k ∘* f ~* g ∘* h)
    : pfiber f ≃* pfiber g :=
    calc pfiber f ≃* pfiber (k ∘* f) : pequiv_postcompose
              ... ≃* pfiber (g ∘* h) : pfiber_equiv_of_phomotopy s
              ... ≃* pfiber g : pequiv_precompose

end fiber

namespace eq --algebra.homotopy_group

  definition phomotopy_group_functor_pid (n : ℕ) (A : Type*) : π→[n] (pid A) ~* pid (π[n] A) :=
  ptrunc_functor_phomotopy 0 !apn_pid ⬝* !ptrunc_functor_pid

end eq
