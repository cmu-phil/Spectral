-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2 homotopy.cofiber homotopy.wedge

open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     is_trunc function sphere

attribute equiv_unit_of_is_contr [constructor]
attribute pwedge pushout.symm pushout.equiv pushout.is_equiv_functor [constructor]
attribute is_succ_add_right is_succ_add_left is_succ_bit0 [constructor]
attribute pushout.functor [unfold 16]
attribute pushout.transpose [unfold 6]

namespace eq

  definition compose_id {A B : Type} (f : A → B) : f ∘ id ~ f :=
  by reflexivity

  definition id_compose {A B : Type} (f : A → B) : id ∘ f ~ f :=
  by reflexivity

  -- move
  definition ap_eq_ap011 {A B C X : Type} (f : A → B → C) (g : X → A) (h : X → B) {x x' : X}
    (p : x = x') : ap (λx, f (g x) (h x)) p = ap011 f (ap g p) (ap h p) :=
  by induction p; reflexivity

end eq

namespace cofiber

  -- replace the one in homotopy.cofiber, which has an superfluous argument
  protected theorem elim_glue' {A B : Type} {f : A → B} {P : Type} (Pbase : P) (Pcod : B → P)
    (Pglue : Π (x : A), Pbase = Pcod (f x)) (a : A)
    : ap (cofiber.elim Pbase Pcod Pglue) (cofiber.glue a) = Pglue a :=
  !pushout.elim_glue

end cofiber

namespace wedge
  open pushout unit
  protected definition glue (A B : Type*) : inl pt = inr pt :> wedge A B :=
  pushout.glue ⋆

end wedge

namespace pointed

  definition to_fun_pequiv_trans {X Y Z : Type*} (f : X ≃* Y) (g :Y ≃* Z) : f ⬝e* g ~ g ∘ f :=
  λx, idp

  definition pcompose2' {A B C : Type*} {g g' : B →* C} {f f' : A →* B} (q : g ~* g') (p : f ~* f') :
    g ∘* f ~* g' ∘* f' :=
  pwhisker_right f q ⬝* pwhisker_left g' p

  infixr ` ◾*' `:80 := pcompose2'

  definition phomotopy_of_homotopy {X Y : Type*} {f g : X →* Y} (h : f ~ g) [is_set Y] : f ~* g :=
  begin
    fapply phomotopy.mk,
    { exact h },
    { apply is_set.elim }
  end

  -- /- the pointed type of (unpointed) dependent maps -/
  -- definition pupi [constructor] {A : Type} (P : A → Type*) : Type* :=
  -- pointed.mk' (Πa, P a)

  -- definition loop_pupi_commute {A : Type} (B : A → Type*) : Ω(pupi B) ≃* pupi (λa, Ω (B a)) :=
  -- pequiv_of_equiv eq_equiv_homotopy rfl

  -- definition equiv_pupi_right {A : Type} {P Q : A → Type*} (g : Πa, P a ≃* Q a)
  --   : pupi P ≃* pupi Q :=
  -- pequiv_of_equiv (pi_equiv_pi_right g)
  --   begin esimp, apply eq_of_homotopy, intros a, esimp, exact (respect_pt (g a)) end

  /-
    Squares of pointed homotopies

    We treat expressions of the form
      k ∘* f ~* g ∘* h
    as squares, where f is the top, g is the bottom, h is the left face and k is the right face.
    Then the following are operations on squares
  -/

  definition psquare {A B C D : Type*} (f : A →* B) (g : C →* D) (h : A ≃* C) (k : B ≃* D) : Type :=
  k ∘* f ~* g ∘* h

  definition phcompose {A B C D B' D' : Type*} {f : A →* B} {g : C →* D} {h : A →* C} {k : B →* D}
    {f' : B →* B'} {g' : D →* D'} {k' : B' →* D'} (p : k ∘* f ~* g ∘* h)
    (q : k' ∘* f' ~* g' ∘* k) : k' ∘* (f' ∘* f) ~* (g' ∘* g) ∘* h :=
  !passoc⁻¹* ⬝* pwhisker_right f q ⬝* !passoc ⬝* pwhisker_left g' p ⬝* !passoc⁻¹*

  definition pvcompose {A B C D C' D' : Type*} {f : A →* B} {g : C →* D} {h : A →* C} {k : B →* D}
    {g' : C' →* D'} {h' : C →* C'} {k' : D →* D'} (p : k ∘* f ~* g ∘* h)
    (q : k' ∘* g ~* g' ∘* h') : (k' ∘* k) ∘* f ~* g' ∘* (h' ∘* h) :=
  (phcompose p⁻¹* q⁻¹*)⁻¹*

  definition phinverse {A B C D : Type*} {f : A ≃* B} {g : C ≃* D} {h : A →* C} {k : B →* D}
    (p : k ∘* f ~* g ∘* h) : h ∘* f⁻¹ᵉ* ~* g⁻¹ᵉ* ∘* k :=
  !pid_pcompose⁻¹* ⬝* pwhisker_right _ (pleft_inv g)⁻¹* ⬝* !passoc ⬝*
  pwhisker_left _
    (!passoc⁻¹* ⬝* pwhisker_right _ p⁻¹* ⬝* !passoc ⬝* pwhisker_left _ !pright_inv ⬝* !pcompose_pid)

  definition pvinverse {A B C D : Type*} {f : A →* B} {g : C →* D} {h : A ≃* C} {k : B ≃* D}
    (p : k ∘* f ~* g ∘* h) : k⁻¹ᵉ* ∘* g ~* f ∘* h⁻¹ᵉ* :=
  (phinverse p⁻¹*)⁻¹*

  infix ` ⬝h* `:73 := phcompose
  infix ` ⬝v* `:73 := pvcompose
  postfix `⁻¹ʰ*`:(max+1) := phinverse
  postfix `⁻¹ᵛ*`:(max+1) := pvinverse

  definition ap1_psquare {A B C D : Type*} {f : A →* B} {g : C →* D} {h : A →* C} {k : B →* D}
    (p : k ∘* f ~* g ∘* h) : Ω→ k ∘* Ω→ f ~* Ω→ g ∘* Ω→ h :=
  !ap1_pcompose⁻¹* ⬝* ap1_phomotopy p ⬝* !ap1_pcompose

  definition apn_psquare (n : ℕ) {A B C D : Type*} {f : A →* B} {g : C →* D} {h : A →* C} {k : B →* D}
    (p : k ∘* f ~* g ∘* h) : Ω→[n] k ∘* Ω→[n] f ~* Ω→[n] g ∘* Ω→[n] h :=
  !apn_pcompose⁻¹* ⬝* apn_phomotopy n p ⬝* !apn_pcompose

  definition ptrunc_functor_psquare (n : ℕ₋₂) {A B C D : Type*} {f : A →* B} {g : C →* D} {h : A →* C}
    {k : B →* D} (p : k ∘* f ~* g ∘* h) :
    ptrunc_functor n k ∘* ptrunc_functor n f ~* ptrunc_functor n g ∘* ptrunc_functor n h :=
  !ptrunc_functor_pcompose⁻¹* ⬝* ptrunc_functor_phomotopy n p ⬝* !ptrunc_functor_pcompose

  definition homotopy_group_homomorphism_psquare (n : ℕ) [H : is_succ n] {A B C D : Type*}
    {f : A →* B} {g : C →* D} {h : A →* C} {k : B →* D} (p : k ∘* f ~* g ∘* h) :
    π→g[n] k ∘ π→g[n] f ~ π→g[n] g ∘ π→g[n] h :=
  begin
    induction H with n, exact to_homotopy (ptrunc_functor_psquare 0 (apn_psquare (succ n) p))
  end

  definition htyhcompose {A B C D B' D' : Type} {f : A → B} {g : C → D} {h : A → C} {k : B → D}
    {f' : B → B'} {g' : D → D'} {k' : B' → D'} (p : k ∘ f ~ g ∘ h)
    (q : k' ∘ f' ~ g' ∘ k) : k' ∘ (f' ∘ f) ~ (g' ∘ g) ∘ h :=
  λa, q (f a) ⬝ ap g' (p a)

  definition htyhinverse {A B C D : Type} {f : A ≃ B} {g : C ≃ D} {h : A → C} {k : B → D}
    (p : k ∘ f ~ g ∘ h) : h ∘ f⁻¹ᵉ ~ g⁻¹ᵉ ∘ k :=
  λb, eq_inv_of_eq ((p (f⁻¹ᵉ b))⁻¹ ⬝ ap k (to_right_inv f b))

end pointed open pointed

namespace trunc

  -- TODO: redefine loopn_ptrunc_pequiv
  definition apn_ptrunc_functor (n : ℕ₋₂) (k : ℕ) {A B : Type*} (f : A →* B) :
    Ω→[k] (ptrunc_functor (n+k) f) ∘* (loopn_ptrunc_pequiv n k A)⁻¹ᵉ* ~*
    (loopn_ptrunc_pequiv n k B)⁻¹ᵉ* ∘* ptrunc_functor n (Ω→[k] f) :=
  begin
    revert n, induction k with k IH: intro n,
    { reflexivity },
    { exact sorry }
  end

  definition ptrunc_pequiv_natural [constructor] (n : ℕ₋₂) {A B : Type*} (f : A →* B) [is_trunc n A]
    [is_trunc n B] : f ∘* ptrunc_pequiv n A ~* ptrunc_pequiv n B ∘* ptrunc_functor n f :=
  begin
    fapply phomotopy.mk,
    { intro a, induction a with a, reflexivity },
    { refine !idp_con ⬝ _ ⬝ !idp_con⁻¹, refine !ap_compose'⁻¹ ⬝ _, apply ap_id }
  end

  definition ptr_natural [constructor] (n : ℕ₋₂) {A B : Type*} (f : A →* B) :
    ptrunc_functor n f ∘* ptr n A ~* ptr n B ∘* f :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity },
    { reflexivity }
  end

  definition ptrunc_elim_pcompose (n : ℕ₋₂) {A B C : Type*} (g : B →* C) (f : A →* B) [is_trunc n B]
    [is_trunc n C] : ptrunc.elim n (g ∘* f) ~* g ∘* ptrunc.elim n f :=
  begin
    fapply phomotopy.mk,
    { intro a, induction a with a, reflexivity },
    { apply idp_con }
  end

end trunc

namespace is_equiv

  definition inv_homotopy_inv {A B : Type} {f g : A → B} [is_equiv f] [is_equiv g] (p : f ~ g)
    : f⁻¹ ~ g⁻¹ :=
  λb, (left_inv g (f⁻¹ b))⁻¹ ⬝ ap g⁻¹ ((p (f⁻¹ b))⁻¹ ⬝ right_inv f b)

  definition to_inv_homotopy_to_inv {A B : Type} {f g : A ≃ B} (p : f ~ g) : f⁻¹ᵉ ~ g⁻¹ᵉ :=
  inv_homotopy_inv p

end is_equiv

namespace prod

  open prod.ops
  definition prod_pathover_equiv {A : Type} {B C : A → Type} {a a' : A} (p : a = a')
    (x : B a × C a) (x' : B a' × C a') : x =[p] x' ≃ x.1 =[p] x'.1 × x.2 =[p] x'.2 :=
  begin
    fapply equiv.MK,
    { intro q, induction q, constructor: constructor },
    { intro v, induction v with q r, exact prod_pathover _ _ _ q r },
    { intro v, induction v with q r, induction x with b c, induction x' with b' c',
      esimp at *, induction q, refine idp_rec_on r _, reflexivity },
    { intro q, induction q, induction x with b c, reflexivity }
  end

end prod open prod

namespace sigma

  -- set_option pp.notation false
  -- set_option pp.binder_types true

  open sigma.ops
  definition pathover_pr1 [unfold 9] {A : Type} {B : A → Type} {C : Πa, B a → Type}
    {a a' : A} {p : a = a'} {x : Σb, C a b} {x' : Σb', C a' b'}
    (q : x =[p] x') : x.1 =[p] x'.1 :=
  begin induction q, constructor end

  definition is_prop_elimo_self {A : Type} (B : A → Type) {a : A} (b : B a) {H : is_prop (B a)} :
    @is_prop.elimo A B a a idp b b H = idpo :=
  !is_prop.elim

  definition sigma_pathover_equiv_of_is_prop {A : Type} {B : A → Type} (C : Πa, B a → Type)
    {a a' : A} (p : a = a') (x : Σb, C a b) (x' : Σb', C a' b')
    [Πa b, is_prop (C a b)] : x =[p] x' ≃ x.1 =[p] x'.1 :=
  begin
    fapply equiv.MK,
    { exact pathover_pr1 },
    { intro q, induction x with b c, induction x' with b' c', esimp at q, induction q,
      apply pathover_idp_of_eq, exact sigma_eq idp !is_prop.elimo },
    { intro q, induction x with b c, induction x' with b' c', esimp at q, induction q,
      have c = c', from !is_prop.elim, induction this,
      rewrite [▸*, is_prop_elimo_self (C a) c] },
    { intro q, induction q, induction x with b c, rewrite [▸*, is_prop_elimo_self (C a) c] }
  end

  definition sigma_ua {A B : Type} (C : A ≃ B → Type) :
    (Σ(p : A = B), C (equiv_of_eq p)) ≃ Σ(e : A ≃ B), C e :=
  sigma_equiv_sigma_left' !eq_equiv_equiv

  -- definition sigma_pathover_equiv_of_is_prop {A : Type} {B : A → Type} {C : Πa, B a → Type}
  --   {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'}
  --   [Πa b, is_prop (C a b)] : ⟨b, c⟩ =[p] ⟨b', c'⟩ ≃ b =[p] b' :=
  -- begin
  --   fapply equiv.MK,
  --   { exact pathover_pr1 },
  --   { intro q, induction q, apply pathover_idp_of_eq, exact sigma_eq idp !is_prop.elimo },
  --   { intro q, induction q,
  --     have c = c', from !is_prop.elim, induction this,
  --     rewrite [▸*, is_prop_elimo_self (C a) c] },
  --   { esimp, generalize ⟨b, c⟩, intro x q, }
  -- end
--rexact @(ap pathover_pr1) _ idpo _,

end sigma open sigma

namespace group
  open is_trunc

  definition to_fun_isomorphism_trans {G H K : Group} (φ : G ≃g H) (ψ : H ≃g K) :
    φ ⬝g ψ ~ ψ ∘ φ :=
  by reflexivity

  definition pmap_of_homomorphism_gid (G : Group) : pmap_of_homomorphism (gid G) ~* pid G :=
  begin
    fapply phomotopy_of_homotopy, reflexivity
  end

  definition pmap_of_homomorphism_gcompose {G H K : Group} (ψ : H →g K) (φ : G →g H)
    : pmap_of_homomorphism (ψ ∘g φ) ~* pmap_of_homomorphism ψ ∘* pmap_of_homomorphism φ :=
  begin
    fapply phomotopy_of_homotopy, reflexivity
  end

  definition pmap_of_homomorphism_phomotopy {G H : Group} {φ ψ : G →g H} (H : φ ~ ψ)
    : pmap_of_homomorphism φ ~* pmap_of_homomorphism ψ :=
  begin
    fapply phomotopy_of_homotopy, exact H
  end

  definition pequiv_of_isomorphism_trans {G₁ G₂ G₃ : Group} (φ : G₁ ≃g G₂) (ψ : G₂ ≃g G₂) :
    pequiv_of_isomorphism (φ ⬝g ψ) ~* pequiv_of_isomorphism ψ ∘* pequiv_of_isomorphism φ :=
  begin
    apply phomotopy_of_homotopy, reflexivity
  end

  definition isomorphism_eq {G H : Group} {φ ψ : G ≃g H} (p : φ ~ ψ) : φ = ψ :=
  begin
    induction φ with φ φe, induction ψ with ψ ψe,
    exact apd011 isomorphism.mk (homomorphism_eq p) !is_prop.elimo
  end

  definition is_set_isomorphism [instance] (G H : Group) : is_set (G ≃g H) :=
  begin
    have H : G ≃g H ≃ Σ(f : G →g H), is_equiv f,
    begin
      fapply equiv.MK,
      { intro φ, induction φ, constructor, assumption },
      { intro v, induction v, constructor, assumption },
      { intro v, induction v, reflexivity },
      { intro φ, induction φ, reflexivity }
    end,
    apply is_trunc_equiv_closed_rev, exact H
  end


--  definition is_equiv_isomorphism


  -- some extra instances for type class inference
  -- definition is_homomorphism_comm_homomorphism [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_homomorphism G G' (@ab_group.to_group _ (AbGroup.struct G))
  --                           (@ab_group.to_group _ (AbGroup.struct G')) φ :=
  -- homomorphism.struct φ

  -- definition is_homomorphism_comm_homomorphism1 [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_homomorphism G G' _
  --                           (@ab_group.to_group _ (AbGroup.struct G')) φ :=
  -- homomorphism.struct φ

  -- definition is_homomorphism_comm_homomorphism2 [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_homomorphism G G' (@ab_group.to_group _ (AbGroup.struct G)) _ φ :=
  -- homomorphism.struct φ

end group open group


namespace pi -- move to types.arrow

  definition pmap_eq_equiv {X Y : Type*} (f g : X →* Y) : (f = g) ≃ (f ~* g) :=
  begin
    refine eq_equiv_fn_eq_of_equiv (@pmap.sigma_char X Y) f g ⬝e _,
    refine !sigma_eq_equiv ⬝e _,
    refine _ ⬝e (phomotopy.sigma_char f g)⁻¹ᵉ,
    fapply sigma_equiv_sigma,
    { esimp, apply eq_equiv_homotopy },
    { induction g with g gp, induction Y with Y y0, esimp, intro p, induction p, esimp at *,
      refine !pathover_idp ⬝e _, refine _ ⬝e !eq_equiv_eq_symm,
      apply equiv_eq_closed_right, exact !idp_con⁻¹ }
  end

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

  infix ` ⬝hty `:75 := homotopy.trans
  postfix `⁻¹ʰᵗʸ`:(max+1) := homotopy.symm

  definition hassoc {A B C D : Type} (h : C → D) (g : B → C) (f : A → B) : (h ∘ g) ∘ f ~ h ∘ (g ∘ f) :=
  λa, idp

  -- to algebra.homotopy_group
  definition homotopy_group_homomorphism_pcompose (n : ℕ) [H : is_succ n] {A B C : Type*} (g : B →* C)
    (f : A →* B) : π→g[n] (g ∘* f) ~ π→g[n] g ∘ π→g[n] f :=
  begin
    induction H with n, exact to_homotopy (homotopy_group_functor_compose (succ n) g f)
  end

  definition apn_pinv (n : ℕ) {A B : Type*} (f : A ≃* B) :
    Ω→[n] f⁻¹ᵉ* ~* (loopn_pequiv_loopn n f)⁻¹ᵉ* :=
  begin
    refine !to_pinv_pequiv_MK2⁻¹*
  end

  -- definition homotopy_group_homomorphism_pinv (n : ℕ) {A B : Type*} (f : A ≃* B) :
  --   π→g[n+1] f⁻¹ᵉ* ~ (homotopy_group_isomorphism_of_pequiv n f)⁻¹ᵍ :=
  -- begin
  --   -- refine ptrunc_functor_phomotopy 0 !apn_pinv ⬝hty _,
  --   -- intro x, esimp,
  -- end

  -- definition natural_square_tr_eq {A B : Type} {a a' : A} {f g : A → B}
  --   (p : f ~ g) (q : a = a') : natural_square p q = square_of_pathover (apd p q) :=
  -- idp

end eq open eq

namespace fiber


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

namespace is_trunc

  definition center' {A : Type} (H : is_contr A) : A := center A

end is_trunc

namespace is_conn

  open unit trunc_index nat is_trunc pointed.ops

  definition is_contr_of_trivial_homotopy' (n : ℕ₋₂) (A : Type) [is_trunc n A] [is_conn -1 A]
    (H : Πk a, is_contr (π[k] (pointed.MK A a))) : is_contr A :=
  begin
    assert aa : trunc -1 A,
    { apply center },
    assert H3 : is_conn 0 A,
    { induction aa with a, exact H 0 a },
    exact is_contr_of_trivial_homotopy n A H
  end

  -- don't make is_prop_is_trunc an instance
  definition is_trunc_succ_is_trunc [instance] (n m : ℕ₋₂) (A : Type) : is_trunc (n.+1) (is_trunc m A) :=
  is_trunc_of_le _ !minus_one_le_succ

  definition is_conn_of_trivial_homotopy (n : ℕ₋₂) (m : ℕ) (A : Type) [is_trunc n A] [is_conn 0 A]
    (H : Π(k : ℕ) a, k ≤ m → is_contr (π[k] (pointed.MK A a))) : is_conn m A :=
  begin
    apply is_contr_of_trivial_homotopy_nat m (trunc m A),
    intro k a H2,
    induction a with a,
    apply is_trunc_equiv_closed_rev,
      exact equiv_of_pequiv (homotopy_group_trunc_of_le (pointed.MK A a) _ _ H2),
    exact H k a H2
  end

  definition is_conn_of_trivial_homotopy_pointed (n : ℕ₋₂) (m : ℕ) (A : Type*) [is_trunc n A]
    (H : Π(k : ℕ), k ≤ m → is_contr (π[k] A)) : is_conn m A :=
  begin
    have is_conn 0 A, proof H 0 !zero_le qed,
    apply is_conn_of_trivial_homotopy n m A,
    intro k a H2, revert a, apply is_conn.elim -1,
    cases A with A a, exact H k H2
  end

end is_conn

namespace circle


/-
  Suppose for `f, g : A -> B` I prove a homotopy `H : f ~ g` by induction on the element in `A`.
  And suppose `p : a = a'` is a path constructor in `A`.
  Then `natural_square_tr H p` has type `square (H a) (H a') (ap f p) (ap g p)` and is equal
  to the square which defined H on the path constructor
-/

  definition natural_square_elim_loop {A : Type} {f g : S¹ → A} (p : f base = g base)
    (q : square p p (ap f loop) (ap g loop))
    : natural_square (circle.rec p (eq_pathover q)) loop = q :=
  begin
    -- refine !natural_square_eq ⬝ _,
    refine ap square_of_pathover !rec_loop ⬝ _,
    exact to_right_inv !eq_pathover_equiv_square q
  end


end circle

namespace susp

  definition psusp_functor_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) :
    psusp_functor f ~* psusp_functor g :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square, esimp, refine !elim_merid ⬝ _ ⬝ !elim_merid⁻¹ᵖ,
        exact ap merid (p a), }},
    { reflexivity },
  end

  definition psusp_functor_pid (A : Type*) : psusp_functor (pid A) ~* pid (psusp A) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square, apply elim_merid }},
    { reflexivity },
  end

  definition psusp_functor_pcompose {A B C : Type*} (g : B →* C) (f : A →* B) :
    psusp_functor (g ∘* f) ~* psusp_functor g ∘* psusp_functor f :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square, esimp,
        refine !elim_merid ⬝ _ ⬝ (ap_compose (psusp_functor g) _ _)⁻¹ᵖ,
        refine _ ⬝ ap02 _ !elim_merid⁻¹, exact !elim_merid⁻¹ }},
    { reflexivity },
  end

  definition psusp_elim_psusp_functor {A B C : Type*} (g : B →* Ω C) (f : A →* B) :
    psusp.elim g ∘* psusp_functor f ~* psusp.elim (g ∘* f) :=
  begin
    refine !passoc ⬝* _, exact pwhisker_left _ !psusp_functor_pcompose⁻¹*
  end

  definition psusp_elim_phomotopy {A B : Type*} {f g : A →* Ω B} (p : f ~* g) : psusp.elim f ~* psusp.elim g :=
  pwhisker_left _ (psusp_functor_phomotopy p)

  definition psusp_elim_natural {X Y Z : Type*} (g : Y →* Z) (f : X →* Ω Y)
    : g ∘* psusp.elim f ~* psusp.elim (Ω→ g ∘* f) :=
  begin
    refine _ ⬝* pwhisker_left _ !psusp_functor_pcompose⁻¹*,
    refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
    exact pwhisker_right _ !loop_psusp_counit_natural
  end

end susp

namespace category

  -- replace precategory_group with precategory_Group (the former has a universe error)
  definition precategory_Group.{u} [instance] [constructor] : precategory.{u+1 u} Group :=
  begin
    fapply precategory.mk,
    { exact λG H, G →g H },
    { exact _ },
    { exact λG H K ψ φ, ψ ∘g φ },
    { exact λG, gid G },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp }
  end


  definition precategory_AbGroup.{u} [instance] [constructor] : precategory.{u+1 u} AbGroup :=
  begin
    fapply precategory.mk,
    { exact λG H, G →g H },
    { exact _ },
    { exact λG H K ψ φ, ψ ∘g φ },
    { exact λG, gid G },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp }
  end
  open iso
  definition Group_is_iso_of_is_equiv {G H : Group} (φ : G →g H) (H : is_equiv (group_fun φ)) :
    is_iso φ :=
  begin
    fconstructor,
    { exact (isomorphism.mk φ H)⁻¹ᵍ },
    { apply homomorphism_eq, rexact left_inv φ },
    { apply homomorphism_eq, rexact right_inv φ }
  end

  definition Group_is_equiv_of_is_iso {G H : Group} (φ : G ⟶ H) (Hφ : is_iso φ) :
    is_equiv (group_fun φ) :=
  begin
    fapply adjointify,
    { exact group_fun φ⁻¹ʰ },
    { note p := right_inverse φ, exact ap010 group_fun p },
    { note p := left_inverse φ,  exact ap010 group_fun p }
  end

  definition Group_iso_equiv (G H : Group) : (G ≅ H) ≃ (G ≃g H) :=
  begin
    fapply equiv.MK,
    { intro φ, induction φ with φ φi, constructor, exact Group_is_equiv_of_is_iso φ _ },
    { intro v, induction v with φ φe, constructor, exact Group_is_iso_of_is_equiv φ _ },
    { intro v, induction v with φ φe, apply isomorphism_eq, reflexivity },
    { intro φ, induction φ with φ φi, apply iso_eq, reflexivity }
  end

  definition Group_props.{u} {A : Type.{u}} (v : (A → A → A) × (A → A) × A) : Prop.{u} :=
  begin
    induction v with m v, induction v with i o,
    fapply trunctype.mk,
    { exact is_set A × (Πa, m a o = a) × (Πa, m o a = a) × (Πa b c, m (m a b) c = m a (m b c)) ×
      (Πa, m (i a) a = o) },
    { apply is_trunc_of_imp_is_trunc, intro v, induction v with H v,
      have is_prop (Πa, m a o = a), from _,
      have is_prop (Πa, m o a = a), from _,
      have is_prop (Πa b c, m (m a b) c = m a (m b c)), from _,
      have is_prop (Πa, m (i a) a = o), from _,
      apply is_trunc_prod }
  end

  definition Group.sigma_char2.{u} : Group.{u} ≃
    Σ(A : Type.{u}) (v : (A → A → A) × (A → A) × A), Group_props v :=
  begin
    fapply equiv.MK,
    { intro G, refine ⟨G, _⟩, induction G with G g, induction g with m s ma o om mo i mi,
      repeat (fconstructor; do 2 try assumption), },
    { intro v, induction v with x v, induction v with y v, repeat induction y with x y,
      repeat induction v with x v, constructor, fconstructor, repeat assumption },
    { intro v, induction v with x v, induction v with y v, repeat induction y with x y,
      repeat induction v with x v, reflexivity },
    { intro v, repeat induction v with x v, reflexivity },
  end
  open is_trunc

  section
  local attribute group.to_has_mul group.to_has_inv [coercion]

  theorem inv_eq_of_mul_eq {A : Type} (G H : group A) (p : @mul A G ~2 @mul A H) :
    @inv A G ~ @inv A H :=
  begin
    have foo : Π(g : A), @inv A G g = (@inv A G g * g) * @inv A H g,
      from λg, !mul_inv_cancel_right⁻¹,
    cases G with Gm Gs Gh1 G1 Gh2 Gh3 Gi Gh4,
    cases H with Hm Hs Hh1 H1 Hh2 Hh3 Hi Hh4,
    change Gi ~ Hi, intro g, have p' : Gm ~2 Hm, from p,
    calc
      Gi g = Hm (Hm (Gi g) g) (Hi g) : foo
       ... = Hm (Gm (Gi g) g) (Hi g) : by rewrite p'
       ... = Hm G1 (Hi g) : by rewrite Gh4
       ... = Gm G1 (Hi g) : by rewrite p'
       ... = Hi g : Gh2
  end

  theorem one_eq_of_mul_eq {A : Type} (G H : group A)
    (p : @mul A (group.to_has_mul G) ~2 @mul A (group.to_has_mul H)) :
    @one A (group.to_has_one G) = @one A (group.to_has_one H) :=
  begin
    cases G with Gm Gs Gh1 G1 Gh2 Gh3 Gi Gh4,
    cases H with Hm Hs Hh1 H1 Hh2 Hh3 Hi Hh4,
    exact (Hh2 G1)⁻¹ ⬝ (p H1 G1)⁻¹ ⬝ Gh3 H1,
  end
  end

  open prod.ops
  definition group_of_Group_props.{u} {A : Type.{u}} {m : A → A → A} {i : A → A} {o : A}
    (H : Group_props (m, (i, o))) : group A :=
  ⦃group, mul := m, inv := i, one := o, is_set_carrier := H.1,
    mul_one := H.2.1, one_mul := H.2.2.1, mul_assoc := H.2.2.2.1, mul_left_inv := H.2.2.2.2⦄

  theorem Group_eq_equiv_lemma2 {A : Type} {m m' : A → A → A} {i i' : A → A} {o o' : A}
    (H : Group_props (m, (i, o))) (H' : Group_props (m', (i', o'))) :
    (m, (i, o)) = (m', (i', o')) ≃ (m ~2 m') :=
  begin
    have is_set A, from pr1 H,
    apply equiv_of_is_prop,
    { intro p, exact apd100 (eq_pr1 p)},
    { intro p, apply prod_eq (eq_of_homotopy2 p),
      apply prod_eq: esimp [Group_props] at *; esimp,
      { apply eq_of_homotopy,
        exact inv_eq_of_mul_eq (group_of_Group_props H) (group_of_Group_props H') p },
      { exact one_eq_of_mul_eq (group_of_Group_props H) (group_of_Group_props H') p }}
  end

  open sigma.ops

  theorem Group_eq_equiv_lemma {G H : Group}
    (p : (Group.sigma_char2 G).1 = (Group.sigma_char2 H).1) :
    ((Group.sigma_char2 G).2 =[p] (Group.sigma_char2 H).2) ≃
    (is_homomorphism (equiv_of_eq (proof p qed : Group.carrier G = Group.carrier H))) :=
  begin
    refine !sigma_pathover_equiv_of_is_prop ⬝e _,
    induction G with G g, induction H with H h,
    esimp [Group.sigma_char2] at p, induction p,
    refine !pathover_idp ⬝e _,
    induction g with m s ma o om mo i mi, induction h with μ σ μa ε εμ με ι μι,
    exact Group_eq_equiv_lemma2 (Group.sigma_char2 (Group.mk G (group.mk m s ma o om mo i mi))).2.2
                                (Group.sigma_char2 (Group.mk G (group.mk μ σ μa ε εμ με ι μι))).2.2
  end

  definition isomorphism.sigma_char (G H : Group) : (G ≃g H) ≃ Σ(e : G ≃ H), is_homomorphism e :=
  begin
    fapply equiv.MK,
    { intro φ, exact ⟨equiv_of_isomorphism φ, to_respect_mul φ⟩ },
    { intro v, induction v with e p, exact isomorphism_of_equiv e p },
    { intro v, induction v with e p, induction e, reflexivity },
    { intro φ, induction φ with φ H, induction φ, reflexivity },
  end

  definition Group_eq_equiv (G H : Group) : G = H ≃ (G ≃g H) :=
  begin
    refine (eq_equiv_fn_eq_of_equiv Group.sigma_char2 G H) ⬝e _,
    refine !sigma_eq_equiv ⬝e _,
    refine sigma_equiv_sigma_right Group_eq_equiv_lemma ⬝e _,
    transitivity (Σ(e : (Group.sigma_char2 G).1 ≃ (Group.sigma_char2 H).1),
      @is_homomorphism _ _ _ _ (to_fun e)), apply sigma_ua,
    exact !isomorphism.sigma_char⁻¹ᵉ
  end

  definition to_fun_Group_eq_equiv {G H : Group} (p : G = H)
    : Group_eq_equiv G H p ~ isomorphism_of_eq p :=
  begin
    induction p, reflexivity
  end

  definition Group_eq2 {G H : Group} {p q : G = H}
    (r : isomorphism_of_eq p ~ isomorphism_of_eq q) : p = q :=
  begin
    apply eq_of_fn_eq_fn (Group_eq_equiv G H),
    apply isomorphism_eq,
    intro g, refine to_fun_Group_eq_equiv p g ⬝ r g ⬝ (to_fun_Group_eq_equiv q g)⁻¹,
  end

  definition Group_eq_equiv_Group_iso (G₁ G₂ : Group) : G₁ = G₂ ≃ G₁ ≅ G₂ :=
  Group_eq_equiv G₁ G₂ ⬝e (Group_iso_equiv G₁ G₂)⁻¹ᵉ

  definition category_Group.{u} : category Group.{u} :=
  category.mk precategory_Group
  begin
    intro G H,
    apply is_equiv_of_equiv_of_homotopy (Group_eq_equiv_Group_iso G H),
    intro p, induction p, fapply iso_eq, apply homomorphism_eq, reflexivity
  end

  definition category_AbGroup : category AbGroup :=
  category.mk precategory_AbGroup sorry

  definition Grp.{u} [constructor] : Category := category.Mk Group.{u} category_Group
  definition AbGrp [constructor] : Category := category.Mk AbGroup category_AbGroup

end category

namespace sphere

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

definition image_pathover {A B : Type} (f : A → B) {x y : B} (p : x = y) (u : image f x) (v : image f y) : u =[p] v :=
  begin
    apply is_prop.elimo
  end

section injective_surjective
open trunc fiber image

variables {A B C : Type} [is_set A] [is_set B] [is_set C] (f : A → B) (g : B → C) (h : A → C) (H : g ∘ f ~ h)
include H

definition is_embedding_factor : is_embedding h → is_embedding f :=
  begin
    induction H using homotopy.rec_on_idp,
    intro E,
    fapply is_embedding_of_is_injective,
    intro x y p,
    fapply @is_injective_of_is_embedding _ _ _ E _ _ (ap g p)
  end

definition is_surjective_factor : is_surjective h → is_surjective g :=
  begin
    induction H using homotopy.rec_on_idp,
    intro S,
    intro c,
    note p := S c,
    induction p,
    apply tr,
    fapply fiber.mk,
    exact f a,
    exact p
  end

end injective_surjective
