-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2 homotopy.cofiber homotopy.wedge

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

namespace equiv

  variables {A B : Type} (f : A ≃ B) {a : A} {b : B}
  definition to_eq_of_eq_inv (p : a = f⁻¹ b) : f a = b :=
  ap f p ⬝ right_inv f b

  definition to_eq_of_inv_eq (p : f⁻¹ b = a) : b = f a :=
  (eq_of_eq_inv p⁻¹)⁻¹

  definition to_inv_eq_of_eq (p : b = f a) : f⁻¹ b = a :=
  ap f⁻¹ p ⬝ left_inv f a

  definition to_eq_inv_of_eq (p : f a = b) : a = f⁻¹ b :=
  (inv_eq_of_eq p⁻¹)⁻¹

end equiv open equiv

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

  definition comm_group.to_has_mul {A : Type} (H : comm_group A) : has_mul A := _
  local attribute comm_group.to_has_mul [coercion]

  definition comm_group_eq {A : Type} {G H : comm_group A}
    (same_mul : Π(g h : A), @mul A G g h = @mul A H g h)
    : G = H :=
  begin
    have g_eq : @comm_group.to_group A G = @comm_group.to_group A H, from group_eq same_mul,
    cases G with Gm Gs Gh1 G1 Gh2 Gh3 Gi Gh4 Gh5,
    cases H with Hm Hs Hh1 H1 Hh2 Hh3 Hi Hh4 Hh5,
    have pm : Gm = Hm, from ap (@mul _ ∘ _) g_eq,
    have pi : Gi = Hi, from ap (@inv _ ∘ _) g_eq,
    have p1 : G1 = H1, from ap (@one _ ∘ _) g_eq,
    induction pm, induction pi, induction p1,
    have ps  : Gs  = Hs,  from !is_prop.elim,
    have ph1 : Gh1 = Hh1, from !is_prop.elim,
    have ph2 : Gh2 = Hh2, from !is_prop.elim,
    have ph3 : Gh3 = Hh3, from !is_prop.elim,
    have ph4 : Gh4 = Hh4, from !is_prop.elim,
    have ph5 : Gh5 = Hh5, from !is_prop.elim,
    induction ps, induction ph1, induction ph2, induction ph3, induction ph4, induction ph5,
    reflexivity
  end

  definition comm_group_pathover {A B : Type} {G : comm_group A} {H : comm_group B} {p : A = B}
    (resp_mul : Π(g h : A), cast p (g * h) = cast p g * cast p h) : G =[p] H :=
  begin
    induction p,
    apply pathover_idp_of_eq, exact comm_group_eq (resp_mul)
  end

  definition CommGroup_eq_of_isomorphism {G₁ G₂ : CommGroup} (φ : G₁ ≃g G₂) : G₁ = G₂ :=
  begin
    induction G₁, induction G₂,
    apply apd011 CommGroup.mk (ua (equiv_of_isomorphism φ)),
    apply comm_group_pathover,
    intro g h, exact !cast_ua ⬝ respect_mul φ g h ⬝ ap011 mul !cast_ua⁻¹ !cast_ua⁻¹
  end

end group open group

namespace trunc

  -- TODO: make argument in ptrunc_pequiv implicit

  definition ptr [constructor] (n : ℕ₋₂) (A : Type*) : A →* ptrunc n A :=
  pmap.mk tr idp

  definition puntrunc [constructor] (n : ℕ₋₂) (A : Type*) [is_trunc n A] : ptrunc n A →* A :=
  pmap.mk untrunc_of_is_trunc idp

  definition ptrunc.elim [constructor] (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] (f : X →* Y) :
    ptrunc n X →* Y :=
  pmap.mk (trunc.elim f) (respect_pt f)

  definition ptrunc_elim_ptr [constructor] (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] (f : X →* Y) :
    ptrunc.elim n f ∘* ptr n X ~* f :=
  begin
    fapply phomotopy.mk,
    { reflexivity },
    { reflexivity }
  end

  definition ptrunc_elim_phomotopy (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] {f g : X →* Y}
    (H : f ~* g) : ptrunc.elim n f ~* ptrunc.elim n g :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with x, exact H x },
    { exact to_homotopy_pt H }
  end

  definition ap1_ptrunc_functor (n : ℕ₋₂) {A B : Type*} (f : A →* B) :
    Ω→ (ptrunc_functor (n.+1) f) ∘* (loop_ptrunc_pequiv n A)⁻¹ᵉ* ~*
    (loop_ptrunc_pequiv n B)⁻¹ᵉ* ∘* ptrunc_functor n (Ω→ f) :=
  begin
    fapply phomotopy.mk,
    { intro p, induction p with p,
      refine (!ap_inv⁻¹ ◾ !ap_compose⁻¹ ◾ idp) ⬝ _ ⬝ !ap_con⁻¹,
      apply whisker_right, refine _ ⬝ !ap_con⁻¹, exact whisker_left _ !ap_compose },
    { induction B with B b, induction f with f p, esimp at f, esimp at p, induction p, reflexivity }
  end

  definition ap1_ptrunc_elim (n : ℕ₋₂) {A B : Type*} (f : A →* B) [is_trunc (n.+1) B] :
    Ω→ (ptrunc.elim (n.+1) f) ∘* (loop_ptrunc_pequiv n A)⁻¹ᵉ* ~*
    ptrunc.elim n (Ω→ f) :=
  begin
    fapply phomotopy.mk,
    { intro p, induction p with p, exact idp ◾ !ap_compose⁻¹ ◾ idp },
    { reflexivity }
  end

  definition ap1_ptr (n : ℕ₋₂) (A : Type*) :
    Ω→ (ptr (n.+1) A) ~* (loop_ptrunc_pequiv n A)⁻¹ᵉ* ∘* ptr n (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, apply idp_con },
    { reflexivity }
  end

  -- definition ap1_ptr' (n : ℕ₋₂) (A : Type*) :
  --   loop_ptrunc_pequiv n A ∘* Ω→ (ptr (n.+1) A) ~* ptr n (Ω A) :=
  -- begin
  --   fapply phomotopy.mk,
  --   { intro p, refine ap trunc.encode !idp_con ⬝ _, esimp, },
  --   { reflexivity }
  -- end

  definition ptrunc_elim_ptrunc_functor (n : ℕ₋₂) {A B C : Type*} (g : B →* C) (f : A →* B)
    [is_trunc n C] :
    ptrunc.elim n g ∘* ptrunc_functor n f ~* ptrunc.elim n (g ∘* f) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with a, reflexivity },
    { esimp, exact !idp_con ⬝ whisker_right !ap_compose _ },
  end

end trunc open trunc

namespace pi -- move to types.arrow

  definition pmap_eq_idp {X Y : Type*} (f : X →* Y) :
    pmap_eq (λx, idpath (f x)) !idp_con⁻¹ = idpath f :=
  begin
    cases f with f p, esimp [pmap_eq],
    refine apd011 (apd011 pmap.mk) !eq_of_homotopy_idp _,
    induction Y with Y y0, esimp at *, induction p, esimp, exact sorry
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

  definition pcompose2 {A B C : Type*} {g g' : B →* C} {f f' : A →* B} (p : f ~* f') (q : g ~* g') :
    g ∘* f ~* g' ∘* f' :=
  pwhisker_right f q ⬝* pwhisker_left g' p

  infixr ` ◾* `:80 := pcompose2

  definition phomotopy_pinv_of_phomotopy_pid {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : g ∘* f ~* pid A) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_left_of_phomotopy p ⬝* !pcompose_pid

  definition phomotopy_pinv_of_phomotopy_pid' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : f ∘* g ~* pid B) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_right_of_phomotopy p ⬝* !pid_pcompose

  definition pinv_phomotopy_of_pid_phomotopy {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid A ~* g ∘* f) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid p⁻¹*)⁻¹*

  definition pinv_phomotopy_of_pid_phomotopy' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid B ~* f ∘* g) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid' p⁻¹*)⁻¹*

  definition pinv_pinv {A B : Type*} (f : A ≃* B) : (f⁻¹ᵉ*)⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid (pleft_inv f))⁻¹*

  definition pinv2 {A B : Type*} {f f' : A ≃* B} (p : f ~* f') : f⁻¹ᵉ* ~* f'⁻¹ᵉ* :=
  phomotopy_pinv_of_phomotopy_pid (pinv_right_phomotopy_of_phomotopy (!pid_pcompose ⬝* p)⁻¹*)

  postfix [parsing_only] `⁻²*`:(max+10) := pinv2

  definition trans_pinv {A B C : Type*} (f : A ≃* B) (g : B ≃* C) :
    (f ⬝e* g)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g⁻¹ᵉ* :=
  begin
    refine (phomotopy_pinv_of_phomotopy_pid _)⁻¹*,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (!passoc⁻¹* ⬝* pwhisker_right _ !pright_inv ⬝* !pid_pcompose) ⬝* _,
    apply pright_inv
  end

  definition pinv_trans_pinv_left {A B C : Type*} (f : B ≃* A) (g : B ≃* C) :
    (f⁻¹ᵉ* ⬝e* g)⁻¹ᵉ* ~* f ∘* g⁻¹ᵉ* :=
  !trans_pinv ⬝* pwhisker_right _ !pinv_pinv

  definition pinv_trans_pinv_right {A B C : Type*} (f : A ≃* B) (g : C ≃* B) :
    (f ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g :=
  !trans_pinv ⬝* pwhisker_left _ !pinv_pinv

  definition pinv_trans_pinv_pinv {A B C : Type*} (f : B ≃* A) (g : C ≃* B) :
    (f⁻¹ᵉ* ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f ∘* g :=
  !trans_pinv ⬝* !pinv_pinv ◾* !pinv_pinv

  definition pinv_pcompose_cancel_left {A B C : Type*} (g : B ≃* C) (f : A →* B) :
    g⁻¹ᵉ* ∘* (g ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pleft_inv ⬝* !pid_pcompose

  definition pcompose_pinv_cancel_left {A B C : Type*} (g : C ≃* B) (f : A →* B) :
    g ∘* (g⁻¹ᵉ* ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pright_inv ⬝* !pid_pcompose

  definition pinv_pcompose_cancel_right {A B C : Type*} (g : B →* C) (f : B ≃* A) :
    (g ∘* f⁻¹ᵉ*) ∘* f ~* g :=
  !passoc ⬝* pwhisker_left g !pleft_inv ⬝* !pcompose_pid

  definition pcompose_pinv_cancel_right {A B C : Type*} (g : B →* C) (f : A ≃* B) :
    (g ∘* f) ∘* f⁻¹ᵉ* ~* g :=
  !passoc ⬝* pwhisker_left g !pright_inv ⬝* !pcompose_pid

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

  definition iterate_psusp_succ_in (n : ℕ) (A : Type*) :
    iterate_psusp (succ n) A ≃* iterate_psusp n (psusp A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact psusp_equiv IH}
  end

  definition is_conn_psusp [instance] (n : trunc_index) (A : Type*)
    [H : is_conn n A] : is_conn (n .+1) (psusp A) :=
  is_conn_susp n A

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

  definition psusp.elim [constructor] {X Y : Type*} (f : X →* Ω Y) : psusp X →* Y :=
  loop_psusp_counit Y ∘* psusp_functor f

  definition loop_psusp_intro [constructor] {X Y : Type*} (f : psusp X →* Y) : X →* Ω Y :=
  ap1 f ∘* loop_psusp_unit X

  definition psusp_adjoint_loop_right_inv {X Y : Type*} (g : X →* Ω Y) :
    loop_psusp_intro (psusp.elim g) ~* g :=
  begin
    refine !pwhisker_right !ap1_pcompose ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !loop_psusp_unit_natural⁻¹* ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !loop_psusp_counit_unit ⬝* _,
    apply pid_pcompose
  end

  definition psusp_adjoint_loop_left_inv {X Y : Type*} (f : psusp X →* Y) :
    psusp.elim (loop_psusp_intro f) ~* f :=
  begin
    refine !pwhisker_left !psusp_functor_compose ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine !pwhisker_right !loop_psusp_counit_natural⁻¹* ⬝* _,
    refine !passoc ⬝* _,
    refine !pwhisker_left !loop_psusp_unit_counit ⬝* _,
    apply pcompose_pid
  end

  definition ap1_psusp_elim {A : Type*} {X : Type*} (p : A →* Ω X) :
    Ω→(psusp.elim p) ∘* loop_psusp_unit A ~* p :=
  psusp_adjoint_loop_right_inv p

  -- TODO: rename to psusp_adjoint_loop (also in above lemmas)
  definition psusp_adjoint_loop_unpointed [constructor] (X Y : Type*) : psusp X →* Y ≃ X →* Ω Y :=
  begin
    fapply equiv.MK,
    { exact loop_psusp_intro },
    { exact psusp.elim },
    { intro g, apply eq_of_phomotopy, exact psusp_adjoint_loop_right_inv g },
    { intro f, apply eq_of_phomotopy, exact psusp_adjoint_loop_left_inv f }
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

  -- in freudenthal
  open trunc
  local attribute ptrunc_pequiv_ptrunc_of_le [constructor]
  definition to_pmap_freudenthal_pequiv {A : Type*} (n k : ℕ) [is_conn n A] (H : k ≤ 2 * n)
    : freudenthal_pequiv A H ~* ptrunc_functor k (loop_psusp_unit A) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with a, reflexivity },
    { refine !idp_con ⬝ _, refine _ ⬝ ap02 _ !idp_con⁻¹, refine _ ⬝ !ap_compose, apply ap_compose }
  end

  definition ptrunc_elim_freudenthal_pequiv {A B : Type*} (n k : ℕ) [is_conn n A] (H : k ≤ 2 * n)
    (f : A →* Ω B) [is_trunc (k.+1) (B)] :
    ptrunc.elim k (Ω→ (psusp.elim f)) ∘* freudenthal_pequiv A H ~* ptrunc.elim k f :=
  begin
    refine pwhisker_left _ !to_pmap_freudenthal_pequiv ⬝* _,
    refine !ptrunc_elim_ptrunc_functor ⬝* _,
    exact ptrunc_elim_phomotopy k !ap1_psusp_elim,
  end

  open susp
  definition iterated_freudenthal_pequiv (A : Type*) {n k m : ℕ} [HA : is_conn n A] (H : k ≤ 2 * n)
    : ptrunc k A ≃* ptrunc k (Ω[m] (iterate_psusp m A)) :=
  begin
    revert A n k HA H, induction m with m IH: intro A n k HA H,
    { reflexivity},
    { have H2 : succ k ≤ 2 * succ n,
      from calc
        succ k ≤ succ (2 * n) : succ_le_succ H
           ... ≤ 2 * succ n   : self_le_succ,
      exact calc
        ptrunc k A ≃* ptrunc k (Ω (psusp A))   : freudenthal_pequiv A H
          ... ≃* Ω (ptrunc (succ k) (psusp A)) : loop_ptrunc_pequiv
          ... ≃* Ω (ptrunc (succ k) (Ω[m] (iterate_psusp m (psusp A)))) :
                   loop_pequiv_loop (IH (psusp A) (succ n) (succ k) _ H2)
          ... ≃* ptrunc k (Ω[succ m] (iterate_psusp m (psusp A))) : loop_ptrunc_pequiv
          ... ≃* ptrunc k (Ω[succ m] (iterate_psusp (succ m) A)) :
                   ptrunc_pequiv_ptrunc _ (loopn_pequiv_loopn _ !iterate_psusp_succ_in)}
  end

  definition iterate_psusp_adjoint_loopn [constructor] (X Y : Type*) (n : ℕ) :
    ppmap (iterate_psusp n X) Y ≃* ppmap X (Ω[n] Y) :=
  begin
    revert X Y, induction n with n IH: intro X Y,
    { reflexivity },
    { refine !psusp_adjoint_loop ⬝e* !IH ⬝e* _, apply pequiv_ppcompose_left,
      symmetry, apply loopn_succ_in }
  end

end new_susp open new_susp

namespace hopf

  definition my_transport_codes_merid.{u} (A : Type.{u}) [T : is_trunc 1 A] [K : is_conn 0 A]
    [H : h_space A] (a a' : A) : transport (hopf A) (merid a) a' = a * a' :> A :=
  ap10 (elim_type_merid _ _ _ a) a'

  definition my_transport_codes_merid_one_inv.{u} (A : Type.{u}) [T : is_trunc 1 A]
    [K : is_conn 0 A] [H : h_space A] (a : A) : transport (hopf A) (merid 1)⁻¹ a = a :=
  ap10 (elim_type_merid_inv _ _ _ 1) a ⬝
  begin apply to_inv_eq_of_eq, esimp, refine !one_mul⁻¹ end

  definition my_encode_decode' (A : Type) [T : is_trunc 1 A] [K : is_conn 0 A]
    [H : h_space A] (a : A) : encode A (decode' A a) = a :=
  begin
    esimp [encode, decode', encode₀],
--    refine ap (λp, transport (hopf A) p a) _ ⬝ _
    refine !con_tr ⬝ _,
    refine (ap (transport _ _) !my_transport_codes_merid ⬝ !my_transport_codes_merid_one_inv) ⬝ _,
    apply mul_one
  end

  definition to_pmap_main_lemma_point_pinv (A : Type) [T : is_trunc 1 A] [K : is_conn 0 A]
    [H : h_space A] (coh : one_mul 1 = mul_one 1 :> (1 * 1 = 1 :> A))
    : (main_lemma_point A coh)⁻¹ᵉ* ~* !ptr ∘* loop_psusp_unit (pointed.MK A 1) :=
  begin
    apply pinv_phomotopy_of_pid_phomotopy,
    fapply phomotopy.mk,
    { intro a, exact (my_encode_decode' A a)⁻¹ },
    { esimp [main_lemma_point, main_lemma, encode],
      apply inv_con_eq_of_eq_con,
      refine !ap_compose'⁻¹ ⬝ _, esimp,
      esimp [my_encode_decode'],
      unfold [encode₀],
      exact sorry
     --  assert p : Π(A : Type) (a a' : A) (p : a = a') (B : A → Type) (b : B a),
     --    ap (λ p, p ▸ b) (con.right_inv p) = con_tr p p⁻¹ b ⬝ (ap (transport B p⁻¹)
     -- (transport_codes_merid A b b ⬝ mul_one 1) ⬝ transport_codes_merid_one_inv A 1),

      }
  end

  definition to_pmap_delooping_pinv (A : Type) [T : is_trunc 1 A] [K : is_conn 0 A] [H : h_space A]
    (coh : one_mul 1 = mul_one 1 :> (1 * 1 = 1 :> A))
    : (hopf.delooping A coh)⁻¹ᵉ* ~* Ω→ !ptr ∘* loop_psusp_unit (pointed.MK A 1) :=
  begin
    refine !trans_pinv ⬝* _,
    refine pwhisker_left _ !to_pmap_main_lemma_point_pinv ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !ap1_ptr⁻¹*,
  end

  definition hopf_delooping_elim {A : Type} {B : Type*} [T : is_trunc 1 A] [K : is_conn 0 A]
    [H : h_space A] (coh : one_mul 1 = mul_one 1 :> (1 * 1 = 1 :> A)) (f : pointed.MK A 1 →* Ω B)
    /-[H1 : is_conn 1 B]-/ [H2 : is_trunc 2 B] :
    Ω→(ptrunc.elim 2 (psusp.elim f)) ∘* (hopf.delooping A coh)⁻¹ᵉ* ~* f :=
  begin
    refine pwhisker_left _ !to_pmap_delooping_pinv ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (!ap1_pcompose⁻¹* ⬝* ap1_phomotopy !ptrunc_elim_ptr) ⬝* _,
    apply ap1_psusp_elim
  end

end hopf
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

namespace cofiber

  -- replace with the definition of pcofiber (and remove primes in homotopy.smash)
  definition pcofiber' [constructor] {A B : Type*} (f : A →* B) : Type* :=
  pointed.MK (cofiber f) !cofiber.base
  attribute pcofiber [constructor]
  -- move ppushout attribute out namespace

  protected definition elim {A : Type} {B : Type} {f : A → B} {P : Type}
    (Pinl : P) (Pinr : B → P) (Pglue : Π (x : A), Pinl = Pinr (f x)) (y : cofiber f) : P :=
  begin
    induction y using pushout.elim with x x x, induction x, exact Pinl, exact Pinr x, exact Pglue x,
  end

end cofiber
attribute cofiber.rec cofiber.elim [recursor 8] [unfold 8]

namespace wedge
  open pushout unit
  definition wedge (A B : Type*) : Type := ppushout (pconst punit A) (pconst punit B)
  local attribute wedge [reducible]
  definition pwedge' (A B : Type*) : Type* := pointed.mk' (wedge A B)

  protected definition rec {A B : Type*} {P : wedge A B → Type} (Pinl : Π(x : A), P (inl x))
    (Pinr : Π(x : B), P (inr x)) (Pglue : pathover P (Pinl pt) (glue ⋆) (Pinr pt))
    (y : wedge A B) : P y :=
  by induction y; apply Pinl; apply Pinr; induction x; exact Pglue

  protected definition elim {A B : Type*} {P : Type} (Pinl : A → P)
    (Pinr : B → P) (Pglue : Pinl pt = Pinr pt) (y : wedge A B) : P :=
  by induction y with a b x; exact Pinl a; exact Pinr b; induction x; exact Pglue

end wedge

attribute wedge.rec wedge.elim [recursor 7] [unfold 7]
