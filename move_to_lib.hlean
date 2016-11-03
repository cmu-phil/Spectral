-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2

open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     is_trunc function sphere

attribute equiv.symm equiv.trans is_equiv.is_equiv_ap fiber.equiv_postcompose
          fiber.equiv_precompose pequiv.to_pmap pequiv._trans_of_to_pmap ghomotopy_group_succ_in
          isomorphism_of_eq pmap_bool_equiv sphere_equiv_bool psphere_pequiv_pbool fiber_eq_equiv int.equiv_succ
          [constructor]
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

  -- some extra instances for type class inference
  definition is_homomorphism_comm_homomorphism [instance] {G G' : CommGroup} (φ : G →g G')
    : @is_homomorphism G G' (@comm_group.to_group _ (CommGroup.struct G))
                            (@comm_group.to_group _ (CommGroup.struct G')) φ :=
  homomorphism.struct φ

  definition is_homomorphism_comm_homomorphism1 [instance] {G G' : CommGroup} (φ : G →g G')
    : @is_homomorphism G G' _
                            (@comm_group.to_group _ (CommGroup.struct G')) φ :=
  homomorphism.struct φ

  definition is_homomorphism_comm_homomorphism2 [instance] {G G' : CommGroup} (φ : G →g G')
    : @is_homomorphism G G' (@comm_group.to_group _ (CommGroup.struct G)) _ φ :=
  homomorphism.struct φ

  theorem inv_eq_one {A : Type} [group A] {a : A} (H : a = 1) : a⁻¹ = 1 :=
  iff.mpr (inv_eq_one_iff_eq_one a) H

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

  definition Group_of_pgroup (G : Type*) [pgroup G] : Group :=
  Group.mk G _

  definition pgroup_pType_of_Group [instance] (G : Group) : pgroup (pType_of_Group G) :=
  ⦃ pgroup, Group.struct G,
    pt_mul := one_mul,
    mul_pt := mul_one,
    mul_left_inv_pt := mul.left_inv ⦄

  definition comm_group_pType_of_Group [instance] (G : CommGroup) : comm_group (pType_of_Group G) :=
  CommGroup.struct G

  abbreviation gid [constructor] := @homomorphism_id

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

  -- types.eq
  definition loop_equiv_eq_closed [constructor] {A : Type} {a a' : A} (p : a = a')
    : (a = a) ≃ (a' = a') :=
  eq_equiv_eq_closed p p

  -- init.path
  definition tr_ap {A B : Type} {x y : A} (P : B → Type) (f : A → B) (p : x = y) (z : P (f x)) :
    transport P (ap f p) z = transport (P ∘ f) p z :=
  (tr_compose P f p z)⁻¹


  definition pathover_eq_Fl' {A B : Type} {f : A → B} {a₁ a₂ : A} {b : B} (p : a₁ = a₂) (q : f a₂ = b) : (ap f p) ⬝ q =[p] q :=
  by induction p; induction q; exact idpo

  -- this should be renamed square_pathover. The one in cubical.cube should be renamed
  definition square_pathover' {A B : Type} {a a' : A} {b₁ b₂ b₃ b₄ : A → B}
    {f₁ : b₁ ~ b₂} {f₂ : b₃ ~ b₄} {f₃ : b₁ ~ b₃} {f₄ : b₂ ~ b₄} {p : a = a'}
    {q : square (f₁ a) (f₂ a) (f₃ a) (f₄ a)}
    {r : square (f₁ a') (f₂ a') (f₃ a') (f₄ a')}
    (s : cube (natural_square_tr f₁ p) (natural_square_tr f₂ p)
              (natural_square_tr f₃ p) (natural_square_tr f₄ p) q r) : q =[p] r :=
  by induction p; apply pathover_idp_of_eq; exact eq_of_deg12_cube s

  -- define natural_square_tr this way. Also, natural_square_tr and natural_square should swap names
  definition natural_square_tr_eq {A B : Type} {a a' : A} {f g : A → B}
    (p : f ~ g) (q : a = a') : natural_square_tr p q = square_of_pathover (apd p q) :=
  by induction q; reflexivity

  section
  variables {A : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
            {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
            {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
            {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
            {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
            {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
            {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
            {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
            {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
            {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
            {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}

  -- move to cubical.cube
  definition eq_concat1 {s₀₁₁' : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} (r : s₀₁₁' = s₀₁₁)
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube s₀₁₁' s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂ :=
  by induction r; exact c

  definition concat1_eq {s₂₁₁' : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) (r : s₂₁₁ = s₂₁₁')
    : cube s₀₁₁ s₂₁₁' s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂ :=
  by induction r; exact c

  definition eq_concat2 {s₁₀₁' : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁} (r : s₁₀₁' = s₁₀₁)
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube s₀₁₁ s₂₁₁ s₁₀₁' s₁₂₁ s₁₁₀ s₁₁₂ :=
  by induction r; exact c

  definition concat2_eq {s₁₂₁' : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) (r : s₁₂₁ = s₁₂₁')
    : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁' s₁₁₀ s₁₁₂ :=
  by induction r; exact c

  definition eq_concat3 {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (r : s₁₁₀' = s₁₁₀)
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀' s₁₁₂ :=
  by induction r; exact c

  definition concat3_eq {s₁₁₂' : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) (r : s₁₁₂ = s₁₁₂')
    : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂' :=
  by induction r; exact c

  end

  infix ` ⬝1 `:75 := cube_concat1
  infix ` ⬝2 `:75 := cube_concat2
  infix ` ⬝3 `:75 := cube_concat3
  infix ` ⬝p1 `:75 := eq_concat1
  infix ` ⬝1p `:75 := concat1_eq
  infix ` ⬝p2 `:75 := eq_concat3
  infix ` ⬝2p `:75 := concat2_eq
  infix ` ⬝p3 `:75 := eq_concat3
  infix ` ⬝3p `:75 := concat3_eq

end eq open eq

namespace pointed
  -- in init.pointed `pointed_carrier` should be [unfold 1] instead of [constructor]

  definition ptransport [constructor] {A : Type} (B : A → Type*) {a a' : A} (p : a = a')
    : B a →* B a' :=
  pmap.mk (transport B p) (apdt (λa, Point (B a)) p)

  definition ptransport_change_eq [constructor] {A : Type} (B : A → Type*) {a a' : A} {p q : a = a'}
    (r : p = q) : ptransport B p ~* ptransport B q :=
  phomotopy.mk (λb, ap (λp, transport B p b) r) begin induction r, exact !idp_con end

  definition pnatural_square {A B : Type} (X : B → Type*) {f g : A → B}
    (h : Πa, X (f a) →* X (g a)) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X (ap f p) ~* ptransport X (ap g p) ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  definition pequiv_ap [constructor] {A : Type} (B : A → Type*) {a a' : A} (p : a = a')
    : B a ≃* B a' :=
  pequiv_of_pmap (ptransport B p) !is_equiv_tr

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

  definition is_trunc_pmap [instance] (n : ℕ₋₂) (A B : Type*) [is_trunc n B] : is_trunc n (A →* B) :=
  is_trunc_equiv_closed_rev _ !pmap.sigma_char

  definition is_trunc_ppmap [instance] (n : ℕ₋₂) {A B : Type*} [is_trunc n B] :
    is_trunc n (ppmap A B) :=
  !is_trunc_pmap

  definition pmap_eq_of_homotopy {A B : Type*} {f g : A →* B} [is_set B] (p : f ~ g) : f = g :=
  pmap_eq p !is_set.elim

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

  definition apn_pconst (A B : Type*) (n : ℕ) :
    apn n (pconst A B) ~* pconst (Ω[n] A) (Ω[n] B) :=
  begin
    induction n with n IH,
    { reflexivity },
    { exact ap1_phomotopy IH ⬝* !ap1_pconst }
  end

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

  definition papply [constructor] {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  definition papply_pcompose [constructor] {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  open bool --also rename pmap_bool_equiv -> pmap_pbool_equiv

  definition pbool_pmap [constructor] {A : Type*} (a : A) : pbool →* A :=
  pmap.mk (bool.rec pt a) idp

  definition pmap_pbool_pequiv [constructor] (B : Type*) : ppmap pbool B ≃* B :=
  begin
    fapply pequiv.MK,
    { exact papply B tt },
    { exact pbool_pmap },
    { intro f, fapply pmap_eq,
      { intro b, cases b, exact !respect_pt⁻¹, reflexivity },
      { exact !con.left_inv⁻¹ }},
    { intro b, reflexivity },
  end

  definition papn_pt [constructor] (n : ℕ) (A B : Type*) : ppmap A B →* ppmap (Ω[n] A) (Ω[n] B) :=
  pmap.mk (λf, apn n f) (eq_of_phomotopy !apn_pconst)

  definition papn_fun [constructor] {n : ℕ} {A : Type*} (B : Type*) (p : Ω[n] A) :
    ppmap A B →* Ω[n] B :=
  papply _ p ∘* papn_pt n A B

  definition loopn_succ_in_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    loopn_succ_in B n ∘* Ω→[n+1] f ~* Ω→[n] (Ω→ f) ∘* loopn_succ_in A n :=
  !apn_succ_phomotopy_in

  definition loopn_succ_in_inv_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    Ω→[n + 1] f ∘* (loopn_succ_in A n)⁻¹ᵉ* ~* (loopn_succ_in B n)⁻¹ᵉ* ∘* Ω→[n] (Ω→ f):=
  begin
    apply pinv_right_phomotopy_of_phomotopy,
    refine _ ⬝* !passoc⁻¹*,
    apply phomotopy_pinv_left_of_phomotopy,
    apply apn_succ_phomotopy_in
  end

end pointed open pointed

namespace fiber

  definition pfiber.sigma_char [constructor] {A B : Type*} (f : A →* B)
    : pfiber f ≃* pointed.MK (Σa, f a = pt) ⟨pt, respect_pt f⟩ :=
  pequiv_of_equiv (fiber.sigma_char f pt) idp

  definition ppoint_sigma_char [constructor] {A B : Type*} (f : A →* B)
    : ppoint f ~* pmap.mk pr1 idp ∘* pfiber.sigma_char f :=
  !phomotopy.refl

  definition pfiber_loop_space {A B : Type*} (f : A →* B) : pfiber (Ω→ f) ≃* Ω (pfiber f) :=
    pequiv_of_equiv
    (calc pfiber (Ω→ f) ≃ Σ(p : Point A = Point A), ap1 f p = rfl
                          : (fiber.sigma_char (ap1 f) (Point (Ω B)))
                    ... ≃ Σ(p : Point A = Point A), (respect_pt f) = ap f p ⬝ (respect_pt f)
                          : (sigma_equiv_sigma_right (λp,
                              calc (ap1 f p = rfl) ≃ !respect_pt⁻¹ ⬝ (ap f p ⬝ !respect_pt) = rfl
                                                     : equiv_eq_closed_left _ (con.assoc _ _ _)
                                               ... ≃ ap f p ⬝ (respect_pt f) = (respect_pt f)
                                                     : eq_equiv_inv_con_eq_idp
                                               ... ≃ (respect_pt f) = ap f p ⬝ (respect_pt f)
                                                     : eq_equiv_eq_symm))
                    ... ≃ fiber.mk (Point A) (respect_pt f) = fiber.mk pt (respect_pt f)
                          : fiber_eq_equiv
                    ... ≃ Ω (pfiber f)
                          : erfl)
    (begin cases f with f p, cases A with A a, cases B with B b, esimp at p, esimp at f,
           induction p, reflexivity end)

  definition pfiber_equiv_of_phomotopy {A B : Type*} {f g : A →* B} (h : f ~* g)
    : pfiber f ≃* pfiber g :=
  begin
    fapply pequiv_of_equiv,
    { refine (fiber.sigma_char f pt ⬝e _ ⬝e (fiber.sigma_char g pt)⁻¹ᵉ),
      apply sigma_equiv_sigma_right, intros a,
      apply equiv_eq_closed_left, apply (to_homotopy h) },
    { refine (fiber_eq rfl _),
      change (h pt)⁻¹ ⬝ respect_pt f = idp ⬝ respect_pt g,
      rewrite idp_con, apply inv_con_eq_of_eq_con, symmetry, exact (to_homotopy_pt h) }
  end

  definition transport_fiber_equiv [constructor] {A B : Type} (f : A → B) {b1 b2 : B} (p : b1 = b2)
    : fiber f b1 ≃ fiber f b2 :=
    calc fiber f b1 ≃ Σa, f a = b1 : fiber.sigma_char
               ...  ≃ Σa, f a = b2 : sigma_equiv_sigma_right (λa, equiv_eq_closed_right (f a) p)
               ...  ≃ fiber f b2   : fiber.sigma_char

  definition pequiv_postcompose {A B B' : Type*} (f : A →* B) (g : B ≃* B')
    : pfiber (g ∘* f) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine transport_fiber_equiv (g ∘* f) (respect_pt g)⁻¹ ⬝e fiber.equiv_postcompose f g (Point B),
    esimp, apply (ap (fiber.mk (Point A))), refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
    rewrite [con.assoc, con.right_inv, con_idp, -ap_compose'], apply ap_con_eq_con
  end

  definition pequiv_precompose {A A' B : Type*} (f : A →* B) (g : A' ≃* A)
    : pfiber (f ∘* g) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine fiber.equiv_precompose f g (Point B),
    esimp, apply (eq_of_fn_eq_fn (fiber.sigma_char _ _)), fapply sigma_eq: esimp,
    { apply respect_pt g },
    { apply pathover_eq_Fl' }
  end

  definition pfiber_equiv_of_square {A B C D : Type*} {f : A →* B} {g : C →* D} (h : A ≃* C)
    (k : B ≃* D) (s : k ∘* f ~* g ∘* h) : pfiber f ≃* pfiber g :=
    calc pfiber f ≃* pfiber (k ∘* f) : pequiv_postcompose
              ... ≃* pfiber (g ∘* h) : pfiber_equiv_of_phomotopy s
              ... ≃* pfiber g : pequiv_precompose

  definition ap1_ppoint_phomotopy {A B : Type*} (f : A →* B)
    : Ω→ (ppoint f) ∘* pfiber_loop_space f ~* ppoint (Ω→ f) :=
  begin
    exact sorry
  end

  definition pfiber_equiv_of_square_ppoint {A B C D : Type*} {f : A →* B} {g : C →* D}
    (h : A ≃* C) (k : B ≃* D) (s : k ∘* f ~* g ∘* h)
    : ppoint g ∘* pfiber_equiv_of_square h k s ~* h ∘* ppoint f :=
  sorry

end fiber

namespace eq --algebra.homotopy_group

  definition phomotopy_group_functor_pid (n : ℕ) (A : Type*) : π→[n] (pid A) ~* pid (π[n] A) :=
  ptrunc_functor_phomotopy 0 !apn_pid ⬝* !ptrunc_functor_pid

end eq

namespace susp

  definition iterate_psusp_functor (n : ℕ) {A B : Type*} (f : A →* B) :
    iterate_psusp n A →* iterate_psusp n B :=
  begin
    induction n with n g,
    { exact f },
    { exact psusp_functor g }
  end

end susp

namespace is_conn -- homotopy.connectedness

  structure conntype (n : ℕ₋₂) : Type :=
    (carrier : Type)
    (struct : is_conn n carrier)

  notation `Type[`:95  n:0 `]`:0 := conntype n

  attribute conntype.carrier [coercion]
  attribute conntype.struct [instance] [priority 1300]

  section
    universe variable u
    structure pconntype (n : ℕ₋₂) extends conntype.{u} n, pType.{u}

    notation `Type*[`:95  n:0 `]`:0 := pconntype n

    /-
      There are multiple coercions from pconntype to Type. Type class inference doesn't recognize
      that all of them are definitionally equal (for performance reasons). One instance is
      automatically generated, and we manually add the missing instances.
    -/

    definition is_conn_pconntype [instance] {n : ℕ₋₂} (X : Type*[n]) : is_conn n X :=
    conntype.struct X

    /- Now all the instances work -/
    example {n : ℕ₋₂} (X : Type*[n]) : is_conn n X := _
    example {n : ℕ₋₂} (X : Type*[n]) : is_conn n (pconntype.to_pType X) := _
    example {n : ℕ₋₂} (X : Type*[n]) : is_conn n (pconntype.to_conntype X) := _
    example {n : ℕ₋₂} (X : Type*[n]) : is_conn n (pconntype._trans_of_to_pType X) := _
    example {n : ℕ₋₂} (X : Type*[n]) : is_conn n (pconntype._trans_of_to_conntype X) := _

    structure truncconntype (n k : ℕ₋₂) extends trunctype.{u} n,
                                                conntype.{u} k renaming struct→conn_struct

    notation n `-Type[`:95  k:0 `]`:0 := truncconntype n k

    definition is_conn_truncconntype [instance] {n k : ℕ₋₂} (X : n-Type[k]) :
      is_conn k (truncconntype._trans_of_to_trunctype X) :=
    conntype.struct X

    definition is_trunc_truncconntype [instance] {n k : ℕ₋₂} (X : n-Type[k]) : is_trunc n X :=
    trunctype.struct X

    structure ptruncconntype (n k : ℕ₋₂) extends ptrunctype.{u} n,
                                                 pconntype.{u} k renaming struct→conn_struct

    notation n `-Type*[`:95  k:0 `]`:0 := ptruncconntype n k

    attribute ptruncconntype._trans_of_to_pconntype ptruncconntype._trans_of_to_ptrunctype
              ptruncconntype._trans_of_to_pconntype_1 ptruncconntype._trans_of_to_ptrunctype_1
              ptruncconntype._trans_of_to_pconntype_2 ptruncconntype._trans_of_to_ptrunctype_2
              ptruncconntype.to_pconntype ptruncconntype.to_ptrunctype
              truncconntype._trans_of_to_conntype truncconntype._trans_of_to_trunctype
              truncconntype.to_conntype truncconntype.to_trunctype [unfold 3]
    attribute pconntype._trans_of_to_conntype pconntype._trans_of_to_pType
              pconntype.to_pType pconntype.to_conntype [unfold 2]

    definition is_conn_ptruncconntype [instance] {n k : ℕ₋₂} (X : n-Type*[k]) :
      is_conn k (ptruncconntype._trans_of_to_ptrunctype X) :=
    conntype.struct X

    definition is_trunc_ptruncconntype [instance] {n k : ℕ₋₂} (X : n-Type*[k]) :
      is_trunc n (ptruncconntype._trans_of_to_pconntype X) :=
    trunctype.struct X

    definition ptruncconntype_eq {n k : ℕ₋₂} {X Y : n-Type*[k]} (p : X ≃* Y) : X = Y :=
    begin
      induction X with X Xt Xp Xc, induction Y with Y Yt Yp Yc,
      note q := pType_eq_elim (eq_of_pequiv p),
      cases q with r s, esimp at *, induction r,
      exact ap0111 (ptruncconntype.mk X) !is_prop.elim (eq_of_pathover_idp s) !is_prop.elim
    end

  end


end is_conn

namespace succ_str
  variables {N : succ_str}

  protected definition add [reducible] (n : N) (k : ℕ) : N :=
  iterate S k n

  infix ` +' `:65 := succ_str.add

  definition add_succ (n : N) (k : ℕ) : n +' (k + 1) = (S n) +' k :=
  by induction k with k p; reflexivity; exact ap S p


end succ_str

namespace join

  definition pjoin [constructor] (A B : Type*) : Type* := pointed.MK (join A B) (inl pt)

end join

namespace circle


/-
  Suppose for `f, g : A -> B` I prove a homotopy `H : f ~ g` by induction on the element in `A`.
  And suppose `p : a = a'` is a path constructor in `A`.
  Then `natural_square_tr H p` has type `square (H a) (H a') (ap f p) (ap g p)` and is equal
  to the square which defined H on the path constructor
-/

  definition natural_square_tr_elim_loop {A : Type} {f g : S¹ → A} (p : f base = g base)
    (q : square p p (ap f loop) (ap g loop))
    : natural_square_tr (circle.rec p (eq_pathover q)) loop = q :=
  begin
    refine !natural_square_tr_eq ⬝ _,
    refine ap square_of_pathover !rec_loop ⬝ _,
    exact to_right_inv !eq_pathover_equiv_square q
  end


end circle

-- this should replace various definitions in homotopy.susp, lines 241 - 338
namespace new_susp

  variables {X Y Z : Type*}

  definition loop_psusp_unit [constructor] (X : Type*) : X →* Ω(psusp X) :=
  begin
    fconstructor,
    { intro x, exact merid x ⬝ (merid pt)⁻¹ },
    { apply con.right_inv },
  end

  definition loop_psusp_unit_natural (f : X →* Y)
    : loop_psusp_unit Y ∘* f ~* ap1 (psusp_functor f) ∘* loop_psusp_unit X :=
  begin
    induction X with X x, induction Y with Y y, induction f with f pf, esimp at *, induction pf,
    fconstructor,
    { intro x', esimp [psusp_functor], symmetry,
      exact
        !idp_con ⬝
        (!ap_con ⬝
        whisker_left _ !ap_inv) ⬝
        (!elim_merid ◾ (inverse2 !elim_merid)) },
    { rewrite [▸*,idp_con (con.right_inv _)],
      apply inv_con_eq_of_eq_con,
      refine _ ⬝ !con.assoc',
      rewrite inverse2_right_inv,
      refine _ ⬝ !con.assoc',
      rewrite [ap_con_right_inv],
      xrewrite [idp_con_idp, -ap_compose (concat idp)] },
  end

  definition loop_psusp_counit [constructor] (X : Type*) : psusp (Ω X) →* X :=
  begin
    fconstructor,
    { intro x, induction x, exact pt, exact pt, exact a },
    { reflexivity },
  end

  definition loop_psusp_counit_natural (f : X →* Y)
    : f ∘* loop_psusp_counit X ~* loop_psusp_counit Y ∘* (psusp_functor (ap1 f)) :=
  begin
    induction X with X x, induction Y with Y y, induction f with f pf, esimp at *, induction pf,
    fconstructor,
    { intro x', induction x' with p,
      { reflexivity },
      { reflexivity },
      { esimp, apply eq_pathover, apply hdeg_square,
        xrewrite [ap_compose' f, ap_compose' (susp.elim (f x) (f x) (λ (a : f x = f x), a)),▸*],
        xrewrite [+elim_merid,▸*,idp_con] }},
    { reflexivity }
  end

  definition loop_psusp_counit_unit (X : Type*)
    : ap1 (loop_psusp_counit X) ∘* loop_psusp_unit (Ω X) ~* pid (Ω X) :=
  begin
    induction X with X x, fconstructor,
    { intro p, esimp,
      refine !idp_con ⬝
             (!ap_con ⬝
             whisker_left _ !ap_inv) ⬝
             (!elim_merid ◾ inverse2 !elim_merid) },
    { rewrite [▸*,inverse2_right_inv (elim_merid id idp)],
      refine !con.assoc ⬝ _,
      xrewrite [ap_con_right_inv (susp.elim x x (λa, a)) (merid idp),idp_con_idp,-ap_compose] }
  end

  definition loop_psusp_unit_counit (X : Type*)
    : loop_psusp_counit (psusp X) ∘* psusp_functor (loop_psusp_unit X) ~* pid (psusp X) :=
  begin
    induction X with X x, fconstructor,
    { intro x', induction x',
      { reflexivity },
      { exact merid pt },
      { apply eq_pathover,
        xrewrite [▸*, ap_id, ap_compose' (susp.elim north north (λa, a)), +elim_merid,▸*],
        apply square_of_eq, exact !idp_con ⬝ !inv_con_cancel_right⁻¹ }},
    { reflexivity }
  end

  -- TODO: rename to psusp_adjoint_loop (also in above lemmas)
  definition psusp_adjoint_loop_unpointed [constructor] (X Y : Type*) : psusp X →* Y ≃ X →* Ω Y :=
  begin
    fapply equiv.MK,
    { intro f, exact ap1 f ∘* loop_psusp_unit X },
    { intro g, exact loop_psusp_counit Y ∘* psusp_functor g },
    { intro g, apply eq_of_phomotopy, esimp,
      refine !pwhisker_right !ap1_pcompose ⬝* _,
      refine !passoc ⬝* _,
      refine !pwhisker_left !loop_psusp_unit_natural⁻¹* ⬝* _,
      refine !passoc⁻¹* ⬝* _,
      refine !pwhisker_right !loop_psusp_counit_unit ⬝* _,
      apply pid_pcompose },
    { intro f, apply eq_of_phomotopy, esimp,
      refine !pwhisker_left !psusp_functor_compose ⬝* _,
      refine !passoc⁻¹* ⬝* _,
      refine !pwhisker_right !loop_psusp_counit_natural⁻¹* ⬝* _,
      refine !passoc ⬝* _,
      refine !pwhisker_left !loop_psusp_unit_counit ⬝* _,
      apply pcompose_pid },
  end

  definition psusp_adjoint_loop_pconst (X Y : Type*) :
    psusp_adjoint_loop_unpointed X Y (pconst (psusp X) Y) ~* pconst X (Ω Y) :=
  begin
    refine pwhisker_right _ !ap1_pconst ⬝* _,
    apply pconst_pcompose
  end

  definition psusp_adjoint_loop [constructor] (X Y : Type*) : ppmap (psusp X) Y ≃* ppmap X (Ω Y) :=
  begin
    apply pequiv_of_equiv (psusp_adjoint_loop_unpointed X Y),
    apply eq_of_phomotopy,
    apply psusp_adjoint_loop_pconst
  end

end new_susp open new_susp

-- this should replace corresponding definitions in homotopy.sphere
namespace new_sphere

  open sphere sphere.ops

  -- the definition was wrong for n = 0
  definition new.surf {n : ℕ} : Ω[n] (S* n) :=
  begin
    induction n with n s,
    { exact south },
    { exact (loopn_succ_in (S* (succ n)) n)⁻¹ᵉ* (apn n (equator n) s), }
  end


  definition psphere_pmap_pequiv' (A : Type*) (n : ℕ) : ppmap (S* n) A ≃* Ω[n] A :=
  begin
    revert A, induction n with n IH: intro A,
    { refine _ ⬝e* !pmap_pbool_pequiv, exact pequiv_ppcompose_right psphere_pequiv_pbool⁻¹ᵉ* },
    { refine psusp_adjoint_loop (S* n) A ⬝e* IH (Ω A) ⬝e* !loopn_succ_in⁻¹ᵉ*  }
  end

  definition psphere_pmap_pequiv (A : Type*) (n : ℕ) : ppmap (S* n) A ≃* Ω[n] A :=
  begin
    fapply pequiv_change_fun,
    { exact psphere_pmap_pequiv' A n },
    { exact papn_fun A new.surf },
    { revert A, induction n with n IH: intro A,
      { reflexivity },
      { intro f, refine ap !loopn_succ_in⁻¹ᵉ* (IH (Ω A) _ ⬝ !apn_pcompose _) ⬝ _,
        exact !loopn_succ_in_inv_natural⁻¹* _ }}
  end

end new_sphere

namespace sphere

  open sphere.ops new_sphere

  -- definition constant_sphere_map_sphere {n m : ℕ} (H : n < m) (f : S* n →* S* m) :
  --   f ~* pconst (S* n) (S* m) :=
  -- begin
  --   assert H : is_contr (Ω[n] (S* m)),
  --   { apply homotopy_group_sphere_le, },
  --   apply phomotopy_of_eq,
  --   apply eq_of_fn_eq_fn !psphere_pmap_pequiv,
  --   apply @is_prop.elim
  -- end

end sphere
