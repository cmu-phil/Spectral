-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2 homotopy.cofiber homotopy.wedge hit.prop_trunc hit.set_quotient eq2 types.pointed2 algebra.graph algebra.category.functor.equivalence

open eq nat int susp pointed sigma is_equiv equiv fiber algebra trunc pi group
     is_trunc function unit prod bool

universe variable u

/-
eq_of_homotopy_eta     > eq_of_homotopy_apd10
pathover_of_tr_eq_idp  > pathover_idp_of_eq
pathover_of_tr_eq_idp' > pathover_of_tr_eq_idp
homotopy_group_isomorphism_of_ptrunc_pequiv > ghomotopy_group_isomorphism_of_ptrunc_pequiv
equiv_pathover <> equiv_pathover2
homotopy_group_functor_succ_phomotopy_in > homotopy_group_succ_in_natural
homotopy_group_succ_in_natural > homotopy_group_succ_in_natural_unpointed
le_step_left > le_of_succ_le
pmap.eta > pmap_eta
pType.sigma_char' > pType.sigma_char
cghomotopy_group to aghomotopy_group
is_trunc_loop_of_is_trunc > is_trunc_loopn_of_is_trunc


first two arguments reordered in is_trunc_loopn_nat
reorder pathover arguments of constructions with squareovers (mostly implicit)
-/

namespace eq

  definition transport_lemma {A : Type} {C : A → Type} {g₁ : A → A}
    {x y : A} (p : x = y) (f : Π⦃x⦄, C x → C (g₁ x)) (z : C x) :
    transport C (ap g₁ p)⁻¹ (f (transport C p z)) = f z :=
  by induction p; reflexivity

  definition transport_lemma2 {A : Type} {C : A → Type} {g₁ : A → A}
    {x y : A} (p : x = y) (f : Π⦃x⦄, C x → C (g₁ x)) (z : C x) :
    transport C (ap g₁ p) (f z) = f (transport C p z) :=
  by induction p; reflexivity

  variables {A A' B : Type} {a a₂ a₃ : A} {p p' : a = a₂} {p₂ : a₂ = a₃}
            {a' a₂' a₃' : A'} {b b₂ : B}

  definition apd_eq_ap (f : A → A') (p : a = a₂) : eq_of_pathover (apd f p) = ap f p :=
  begin induction p, reflexivity end

  definition eq_of_pathover_idp_constant (p : b =[idpath a] b₂) :
    eq_of_pathover_idp p = eq_of_pathover p :=
  begin induction p using idp_rec_on, reflexivity end

  definition eq_of_pathover_change_path (r : p = p') (q : a' =[p] a₂') :
    eq_of_pathover (change_path r q) = eq_of_pathover q :=
  begin induction r, reflexivity end

  definition eq_of_pathover_cono (q : a' =[p] a₂') (q₂ : a₂' =[p₂] a₃') :
    eq_of_pathover (q ⬝o q₂) = eq_of_pathover q ⬝ eq_of_pathover q₂ :=
  begin induction q₂, reflexivity end

  definition eq_of_pathover_invo (q : a' =[p] a₂') :
    eq_of_pathover q⁻¹ᵒ = (eq_of_pathover q)⁻¹ :=
  begin induction q, reflexivity end

  definition eq_of_pathover_concato_eq (q : a' =[p] a₂') (q₂ : a₂' = a₃') :
    eq_of_pathover (q ⬝op q₂) = eq_of_pathover q ⬝ q₂ :=
  begin induction q₂, reflexivity end

  definition eq_of_pathover_eq_concato (q : a' = a₂') (q₂ : a₂' =[p₂] a₃') :
    eq_of_pathover (q ⬝po q₂) = q ⬝ eq_of_pathover q₂ :=
  begin induction q, induction q₂, reflexivity end


end eq open eq

namespace nat

--   definition rec_down_le_beta_lt (P : ℕ → Type) (s : ℕ) (H0 : Πn, s ≤ n → P n)
--     (Hs : Πn, P (n+1) → P n) (n : ℕ) (Hn : n < s) :
--     rec_down_le P s H0 Hs n = Hs n (rec_down_le P s H0 Hs (n+1)) :=
--   begin
--     revert n Hn, induction s with s IH: intro n Hn,
--     { exfalso, exact not_succ_le_zero n Hn },
--     { have Hn' : n ≤ s, from le_of_succ_le_succ Hn,
--       --esimp [rec_down_le],
--       exact sorry
--       -- induction Hn' with s Hn IH,
--       -- { },
--       -- { }
-- }
--   end

end nat

  definition max0_monotone {n m : ℤ} (H : n ≤ m) : max0 n ≤ max0 m :=
  begin
    induction n with n n,
    { induction m with m m,
      { exact le_of_of_nat_le_of_nat H },
      { exfalso, exact not_neg_succ_le_of_nat H }},
    { apply zero_le }
  end


  -- definition ppi_eq_equiv_internal : (k = l) ≃ (k ~* l) :=
  --   calc (k = l) ≃ ppi.sigma_char P p₀ k = ppi.sigma_char P p₀ l
  --                  : eq_equiv_fn_eq (ppi.sigma_char P p₀) k l
  --           ...  ≃ Σ(p : k = l),
  --                    pathover (λh, h pt = p₀) (respect_pt k) p (respect_pt l)
  --                  : sigma_eq_equiv _ _
  --           ...  ≃ Σ(p : k = l),
  --                    respect_pt k = ap (λh, h pt) p ⬝ respect_pt l
  --                  : sigma_equiv_sigma_right
  --                      (λp, eq_pathover_equiv_Fl p (respect_pt k) (respect_pt l))
  --           ...  ≃ Σ(p : k = l),
  --                    respect_pt k = apd10 p pt ⬝ respect_pt l
  --                  : sigma_equiv_sigma_right
  --                      (λp, equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)))
  --           ...  ≃ Σ(p : k ~ l), respect_pt k = p pt ⬝ respect_pt l
  --                  : sigma_equiv_sigma_left' eq_equiv_homotopy
  --           ...  ≃ Σ(p : k ~ l), p pt ⬝ respect_pt l = respect_pt k
  --                  : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
  --           ...  ≃ (k ~* l) : phomotopy.sigma_char k l

namespace pointed

infixr ` →** `:29 := ppmap

end pointed open pointed

namespace trunc
  open trunc_index sigma.ops

  definition ptrunc_functor_pconst [constructor] (n : ℕ₋₂) (X Y : Type*) :
    ptrunc_functor n (pconst X Y) ~* pconst (ptrunc n X) (ptrunc n Y) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with x, reflexivity },
    { reflexivity }
  end

  -- TODO: redefine loopn_ptrunc_pequiv
  definition apn_ptrunc_functor (n : ℕ₋₂) (k : ℕ) {A B : Type*} (f : A →* B) :
    Ω→[k] (ptrunc_functor (n+k) f) ∘* (loopn_ptrunc_pequiv n k A)⁻¹ᵉ* ~*
    (loopn_ptrunc_pequiv n k B)⁻¹ᵉ* ∘* ptrunc_functor n (Ω→[k] f) :=
  begin
    revert n, induction k with k IH: intro n,
    { reflexivity },
    { exact sorry }
  end

end trunc open trunc


namespace sigma
  open sigma.ops
  -- open sigma.ops
  -- definition eq.rec_sigma {A : Type} {B : A → Type} {a₀ : A} {b₀ : B a₀}
  --   {P : Π(a : A) (b : B a), ⟨a₀, b₀⟩ = ⟨a, b⟩ → Type} (H : P a₀ b₀ idp) {a : A} {b : B a}
  --   (p : ⟨a₀, b₀⟩ = ⟨a, b⟩) : P a b p :=
  -- sorry

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

  definition sigma_functor2 [constructor] {A₁ A₂ A₃ : Type}
    {B₁ : A₁ → Type} {B₂ : A₂ → Type} {B₃ : A₃ → Type}
    (f : A₁ → A₂ → A₃) (g : Π⦃a₁ a₂⦄, B₁ a₁ → B₂ a₂ → B₃ (f a₁ a₂))
      (x₁ : Σa₁, B₁ a₁) (x₂ : Σa₂, B₂ a₂) : Σa₃, B₃ a₃ :=
  ⟨f x₁.1 x₂.1, g x₁.2 x₂.2⟩

  definition eq.rec_sigma {A : Type} {B : A → Type} {a : A} {b : B a}
    (P : Π⦃a'⦄ {b' : B a'}, ⟨a, b⟩ = ⟨a', b'⟩ → Type)
    (IH : P idp) ⦃a' : A⦄ {b' : B a'} (p : ⟨a, b⟩ = ⟨a', b'⟩) : P p :=
  begin
    apply transport (λp, P p) (to_left_inv !sigma_eq_equiv p),
    generalize !sigma_eq_equiv p, esimp, intro q,
    induction q with q₁ q₂, induction q₂, exact IH
  end

  definition ap_dpair_eq_dpair_pr {A A' : Type} {B : A → Type} {a a' : A} {b : B a} {b' : B a'} (f : Πa, B a → A') (p : a = a') (q : b =[p] b')
    : ap (λx, f x.1 x.2) (dpair_eq_dpair p q) = apd011 f p q :=
  by induction q; reflexivity

  definition sigma_eq_equiv_of_is_prop_right [constructor] {A : Type} {B : A → Type} (u v : Σa, B a)
    [H : Π a, is_prop (B a)] : u = v ≃ u.1 = v.1 :=
  !sigma_eq_equiv ⬝e !sigma_equiv_of_is_contr_right

  definition ap_sigma_pr1 {A B : Type} {C : B → Type} {a₁ a₂ : A} (f : A → B) (g : Πa, C (f a))
    (p : a₁ = a₂) : (ap (λa, ⟨f a, g a⟩) p)..1 = ap f p :=
  by induction p; reflexivity

  definition ap_sigma_pr2 {A B : Type} {C : B → Type} {a₁ a₂ : A} (f : A → B) (g : Πa, C (f a))
    (p : a₁ = a₂) : (ap (λa, ⟨f a, g a⟩) p)..2 =
    change_path (ap_sigma_pr1 f g p)⁻¹ (pathover_ap C f (apd g p)) :=
  by induction p; reflexivity

  definition ap_sigma_functor_sigma_eq {A A' : Type} {B : A → Type} {B' : A' → Type}
    {a a' : A} {b : B a} {b' : B a'} (f : A → A') (g : Πa, B a → B' (f a)) (p : a = a') (q : b =[p] b') :
    ap (sigma_functor f g) (sigma_eq p q) = sigma_eq (ap f p) (pathover_ap B' f (apo g q)) :=
  by induction q; reflexivity

  definition ap_sigma_functor_id_sigma_eq {A : Type} {B B' : A → Type}
    {a a' : A} {b : B a} {b' : B a'} (g : Πa, B a → B' a) (p : a = a') (q : b =[p] b') :
    ap (sigma_functor id g) (sigma_eq p q) = sigma_eq p (apo g q) :=
  by induction q; reflexivity

  definition sigma_eq_pr2_constant {A B : Type} {a a' : A} {b b' : B} (p : a = a')
    (q : b =[p] b') : ap pr2 (sigma_eq p q) = (eq_of_pathover q) :=
  by induction q; reflexivity

  definition sigma_eq_pr2_constant2 {A B : Type} {a a' : A} {b b' : B} (p : a = a')
    (q : b = b') : ap pr2 (sigma_eq p (pathover_of_eq p q)) = q :=
  by induction p; induction q; reflexivity

  definition sigma_eq_concato_eq {A : Type} {B : A → Type} {a a' : A} {b : B a} {b₁ b₂ : B a'}
    (p : a = a') (q : b =[p] b₁) (q' : b₁ = b₂) : sigma_eq p (q ⬝op q') = sigma_eq p q ⬝ ap (dpair a') q' :=
  by induction q'; reflexivity

  definition sigma_functor_compose {A A' A'' : Type} {B : A → Type} {B' : A' → Type}
    {B'' : A'' → Type} {f' : A' → A''} {f : A → A'} (g' : Πa, B' a → B'' (f' a))
    (g : Πa, B a → B' (f a)) (x : Σa, B a) :
    sigma_functor f' g' (sigma_functor f g x) = sigma_functor (f' ∘ f) (λa, g' (f a) ∘ g a) x :=
  begin
    reflexivity
  end

  definition sigma_functor_homotopy {A A' : Type} {B : A → Type} {B' : A' → Type}
    {f f' : A → A'} {g : Πa, B a → B' (f a)} {g' : Πa, B a → B' (f' a)} (h : f ~ f')
    (k : Πa b, g a b =[h a] g' a b) (x : Σa, B a) : sigma_functor f g x = sigma_functor f' g' x :=
  sigma_eq (h x.1) (k x.1 x.2)

  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type}
            {B₀₀ : A₀₀ → Type} {B₂₀ : A₂₀ → Type} {B₀₂ : A₀₂ → Type} {B₂₂ : A₂₂ → Type}
            {f₁₀ : A₀₀ → A₂₀} {f₁₂ : A₀₂ → A₂₂} {f₀₁ : A₀₀ → A₀₂} {f₂₁ : A₂₀ → A₂₂}
            {g₁₀ : Πa, B₀₀ a → B₂₀ (f₁₀ a)} {g₁₂ : Πa, B₀₂ a → B₂₂ (f₁₂ a)}
            {g₀₁ : Πa, B₀₀ a → B₀₂ (f₀₁ a)} {g₂₁ : Πa, B₂₀ a → B₂₂ (f₂₁ a)}

  definition sigma_functor_hsquare (h : hsquare f₁₀ f₁₂ f₀₁ f₂₁)
    (k : Πa (b : B₀₀ a), g₂₁ _ (g₁₀ _ b) =[h a] g₁₂ _ (g₀₁ _ b)) :
    hsquare (sigma_functor f₁₀ g₁₀) (sigma_functor f₁₂ g₁₂)
            (sigma_functor f₀₁ g₀₁) (sigma_functor f₂₁ g₂₁) :=
  λx, sigma_functor_compose g₂₁ g₁₀ x ⬝
      sigma_functor_homotopy h k x ⬝
      (sigma_functor_compose g₁₂ g₀₁ x)⁻¹

  definition sigma_equiv_of_is_embedding_left_fun [constructor] {X Y : Type} {P : Y → Type}
    {f : X → Y} (H : Πy, P y → fiber f y) (v : Σy, P y) : Σx, P (f x) :=
  ⟨fiber.point (H v.1 v.2), transport P (point_eq (H v.1 v.2))⁻¹ v.2⟩

  definition sigma_equiv_of_is_embedding_left_prop [constructor] {X Y : Type} {P : Y → Type}
    (f : X → Y) (Hf : is_embedding f) (HP : Πx, is_prop (P (f x))) (H : Πy, P y → fiber f y) :
    (Σy, P y) ≃ Σx, P (f x) :=
  begin
    apply equiv.MK (sigma_equiv_of_is_embedding_left_fun H) (sigma_functor f (λa, id)),
    { intro v, induction v with x p, esimp [sigma_equiv_of_is_embedding_left_fun],
      fapply sigma_eq, apply @is_injective_of_is_embedding _ _ f, exact point_eq (H (f x) p),
      apply is_prop.elimo },
    { intro v, induction v with y p, esimp, fapply sigma_eq, exact point_eq (H y p),
      apply tr_pathover }
  end

  definition sigma_equiv_of_is_embedding_left_contr [constructor] {X Y : Type} {P : Y → Type}
    (f : X → Y) (Hf : is_embedding f) (HP : Πx, is_contr (P (f x))) (H : Πy, P y → fiber f y) :
    (Σy, P y) ≃ X :=
  sigma_equiv_of_is_embedding_left_prop f Hf _ H ⬝e !sigma_equiv_of_is_contr_right

end sigma open sigma

namespace group

infixr ` →gg `:56 := aghomomorphism

definition pmap_of_homomorphism2 [constructor] {G H K : AbGroup} (φ : G →g H →gg K) :
  G →* H →** K :=
pmap.mk (λg, pmap_of_homomorphism (φ g))
  (eq_of_phomotopy (phomotopy_of_homotopy (ap010 group_fun (to_respect_one φ))))

definition homomorphism_apply [constructor] (G H : AbGroup) (g : G) :
  (G →gg H) →g H :=
begin
  fapply homomorphism.mk,
  { intro φ, exact φ g },
  { intros φ φ', reflexivity }
end

definition homomorphism_swap [constructor] {G H K : AbGroup} (φ : G →g H →gg K) :
  H →g G →gg K :=
begin
  fapply homomorphism.mk,
  { intro h, exact homomorphism_apply H K h ∘g φ },
  { intro h h', apply homomorphism_eq, intro g, exact to_respect_mul (φ g) h h' }
end

definition isomorphism.MK [constructor] {G H : Group} (φ : G →g H) (ψ : H →g G)
  (p : φ ∘g ψ ~ gid H) (q : ψ ∘g φ ~ gid G) : G ≃g H :=
isomorphism.mk φ (adjointify φ ψ p q)

protected definition homomorphism.sigma_char [constructor]
  (A B : Group) : (A →g B) ≃ Σ(f : A → B), is_mul_hom f :=
begin
  fapply equiv.MK,
    {intro F, exact ⟨F, _⟩ },
    {intro p, cases p with f H, exact (homomorphism.mk f H) },
    {intro p, cases p, reflexivity },
    {intro F, cases F, reflexivity },
end

definition homomorphism_pathover {A : Type} {a a' : A} (p : a = a')
  {B : A → Group} {C : A → Group} (f : B a →g C a) (g : B a' →g C a')
  (r : homomorphism.φ f =[p] homomorphism.φ g) : f =[p] g :=
begin
  fapply pathover_of_fn_pathover_fn,
  { intro a, apply homomorphism.sigma_char },
  { fapply sigma_pathover, exact r, apply is_prop.elimo }
end

protected definition isomorphism.sigma_char [constructor]
  (A B : Group) : (A ≃g B) ≃ Σ(f : A →g B), is_equiv f :=
begin
  fapply equiv.MK,
    {intro F, exact ⟨F, _⟩ },
    {intro p, cases p with f H, exact (isomorphism.mk f H) },
    {intro p, cases p, reflexivity },
    {intro F, cases F, reflexivity },
end

definition isomorphism_pathover {A : Type} {a a' : A} (p : a = a')
  {B : A → Group} {C : A → Group} (f : B a ≃g C a) (g : B a' ≃g C a')
  (r : pathover (λa, B a → C a) f p g) : f =[p] g :=
begin
  fapply pathover_of_fn_pathover_fn,
  { intro a, apply isomorphism.sigma_char },
  { fapply sigma_pathover, apply homomorphism_pathover, exact r, apply is_prop.elimo }
end

--  definition is_equiv_isomorphism


  -- some extra instances for type class inference
  -- definition is_mul_hom_comm_homomorphism [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_mul_hom G G' (@ab_group.to_group _ (AbGroup.struct G))
  --                           (@ab_group.to_group _ (AbGroup.struct G')) φ :=
  -- homomorphism.struct φ

  -- definition is_mul_hom_comm_homomorphism1 [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_mul_hom G G' _
  --                           (@ab_group.to_group _ (AbGroup.struct G')) φ :=
  -- homomorphism.struct φ

  -- definition is_mul_hom_comm_homomorphism2 [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_mul_hom G G' (@ab_group.to_group _ (AbGroup.struct G)) _ φ :=
  -- homomorphism.struct φ

  definition pgroup_of_Group (X : Group) : pgroup X :=
  pgroup_of_group _ idp

  definition isomorphism_ap {A : Type} (F : A → Group) {a b : A} (p : a = b) : F a ≃g F b :=
    isomorphism_of_eq (ap F p)

  definition interchange (G : AbGroup) (a b c d : G) : (a * b) * (c * d) = (a * c) * (b * d) :=
  calc (a * b) * (c * d) = a * (b * (c * d)) : by exact mul.assoc a b (c * d)
                     ... = a * ((b * c) * d) : by exact ap (λ bcd, a * bcd) (mul.assoc b c d)⁻¹
                     ... = a * ((c * b) * d) : by exact ap (λ bc, a * (bc * d)) (mul.comm b c)
                     ... = a * (c * (b * d)) : by exact ap (λ bcd, a * bcd) (mul.assoc c b d)
                     ... = (a * c) * (b * d) : by exact (mul.assoc a c (b * d))⁻¹

  definition homomorphism_comp_compute {G H K : Group} (g : H →g K) (f : G →g H) (x : G) : (g ∘g f) x = g (f x) :=
  begin
    reflexivity
  end

  open option
  definition add_point_AbGroup [unfold 3] {X : Type} (G : X → AbGroup) : X₊ → AbGroup
  | (some x) := G x
  | none     := trivial_ab_group_lift

  definition isomorphism_of_is_contr {G H : Group} (hG : is_contr G) (hH : is_contr H) : G ≃g H :=
  trivial_group_of_is_contr G ⬝g (trivial_group_of_is_contr H)⁻¹ᵍ

  definition trunc_isomorphism_of_equiv {A B : Type} [inf_group A] [inf_group B] (f : A ≃ B)
    (h : is_mul_hom f) : Group.mk (trunc 0 A) (trunc_group A) ≃g Group.mk (trunc 0 B) (trunc_group B) :=
  begin
    apply isomorphism_of_equiv (trunc_equiv_trunc 0 f), intros x x',
    induction x with a, induction x' with a', apply ap tr, exact h a a'
  end

  /----------------- The following are properties for ∞-groups ----------------/

  local attribute InfGroup_of_Group [coercion]

  /- left and right actions -/
  definition is_equiv_mul_right_inf [constructor] {A : InfGroup} (a : A) : is_equiv (λb, b * a) :=
  adjointify _ (λb : A, b * a⁻¹) (λb, !inv_mul_cancel_right) (λb, !mul_inv_cancel_right)

  definition right_action_inf [constructor] {A : InfGroup} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_mul_right_inf a)

  /- homomorphisms -/

  structure inf_homomorphism (G₁ G₂ : InfGroup) : Type :=
    (φ : G₁ → G₂)
    (p : is_mul_hom φ)

  infix ` →∞g `:55 := inf_homomorphism

  abbreviation inf_group_fun [unfold 3] [coercion] [reducible] := @inf_homomorphism.φ
  definition inf_homomorphism.struct [unfold 3] [instance] [priority 900] {G₁ G₂ : InfGroup}
    (φ : G₁ →∞g G₂) : is_mul_hom φ :=
  inf_homomorphism.p φ

  definition homomorphism_of_inf_homomorphism [constructor] {G H : Group} (φ : G →∞g H) : G →g H :=
  homomorphism.mk φ (inf_homomorphism.struct φ)

  definition inf_homomorphism_of_homomorphism [constructor] {G H : Group} (φ : G →g H) : G →∞g H :=
  inf_homomorphism.mk φ (homomorphism.struct φ)

  variables {G G₁ G₂ G₃ : InfGroup} {g h : G₁} {ψ : G₂ →∞g G₃} {φ₁ φ₂ : G₁ →∞g G₂} (φ : G₁ →∞g G₂)

  definition to_respect_mul_inf /- φ -/ (g h : G₁) : φ (g * h) = φ g * φ h :=
  respect_mul φ g h

  theorem to_respect_one_inf /- φ -/ : φ 1 = 1 :=
  have φ 1 * φ 1 = φ 1 * 1, by rewrite [-to_respect_mul_inf φ, +mul_one],
  eq_of_mul_eq_mul_left' this

  theorem to_respect_inv_inf /- φ -/ (g : G₁) : φ g⁻¹ = (φ g)⁻¹ :=
  have φ (g⁻¹) * φ g = 1, by rewrite [-to_respect_mul_inf φ, mul.left_inv, to_respect_one_inf φ],
  eq_inv_of_mul_eq_one this

  definition pmap_of_inf_homomorphism [constructor] /- φ -/ : G₁ →* G₂ :=
  pmap.mk φ begin esimp, exact to_respect_one_inf φ end

  definition inf_homomorphism_change_fun [constructor] {G₁ G₂ : InfGroup}
    (φ : G₁ →∞g G₂) (f : G₁ → G₂) (p : φ ~ f) : G₁ →∞g G₂ :=
  inf_homomorphism.mk f
    (λg h, (p (g * h))⁻¹ ⬝ to_respect_mul_inf φ g h ⬝ ap011 mul (p g) (p h))

  /- categorical structure of groups + homomorphisms -/

  definition inf_homomorphism_compose [constructor] [trans] [reducible]
    (ψ : G₂ →∞g G₃) (φ : G₁ →∞g G₂) : G₁ →∞g G₃ :=
  inf_homomorphism.mk (ψ ∘ φ) (is_mul_hom_compose _ _)

  variable (G)
  definition inf_homomorphism_id [constructor] [refl] : G →∞g G :=
  inf_homomorphism.mk (@id G) (is_mul_hom_id G)
  variable {G}

  abbreviation inf_gid [constructor] := @inf_homomorphism_id
  infixr ` ∘∞g `:75 := inf_homomorphism_compose

  structure inf_isomorphism (A B : InfGroup) :=
    (to_hom : A →∞g B)
    (is_equiv_to_hom : is_equiv to_hom)

  infix ` ≃∞g `:25 := inf_isomorphism
  attribute inf_isomorphism.to_hom [coercion]
  attribute inf_isomorphism.is_equiv_to_hom [instance]
  attribute inf_isomorphism._trans_of_to_hom [unfold 3]

  definition equiv_of_inf_isomorphism [constructor] (φ : G₁ ≃∞g G₂) : G₁ ≃ G₂ :=
  equiv.mk φ _

  definition pequiv_of_inf_isomorphism [constructor] (φ : G₁ ≃∞g G₂) :
    G₁ ≃* G₂ :=
  pequiv.mk φ begin esimp, exact _ end begin esimp, exact to_respect_one_inf φ end

  definition inf_isomorphism_of_equiv [constructor] (φ : G₁ ≃ G₂)
    (p : Πg₁ g₂, φ (g₁ * g₂) = φ g₁ * φ g₂) : G₁ ≃∞g G₂ :=
  inf_isomorphism.mk (inf_homomorphism.mk φ p) !to_is_equiv

  definition inf_isomorphism_of_eq [constructor] {G₁ G₂ : InfGroup} (φ : G₁ = G₂) : G₁ ≃∞g G₂ :=
  inf_isomorphism_of_equiv (equiv_of_eq (ap InfGroup.carrier φ))
    begin intros, induction φ, reflexivity end

  definition to_ginv_inf [constructor] (φ : G₁ ≃∞g G₂) : G₂ →∞g G₁ :=
  inf_homomorphism.mk φ⁻¹
    abstract begin
    intro g₁ g₂, apply inj' φ,
    rewrite [respect_mul φ, +right_inv φ]
    end end

  variable (G)
  definition inf_isomorphism.refl [refl] [constructor] : G ≃∞g G :=
  inf_isomorphism.mk !inf_gid !is_equiv_id
  variable {G}

  definition inf_isomorphism.symm [symm] [constructor] (φ : G₁ ≃∞g G₂) : G₂ ≃∞g G₁ :=
  inf_isomorphism.mk (to_ginv_inf φ) !is_equiv_inv

  definition inf_isomorphism.trans [trans] [constructor] (φ : G₁ ≃∞g G₂) (ψ : G₂ ≃∞g G₃) : G₁ ≃∞g G₃ :=
  inf_isomorphism.mk (ψ ∘∞g φ) !is_equiv_compose

  definition inf_isomorphism.eq_trans [trans] [constructor]
     {G₁ G₂ : InfGroup} {G₃ : InfGroup} (φ : G₁ = G₂) (ψ : G₂ ≃∞g G₃) : G₁ ≃∞g G₃ :=
  proof inf_isomorphism.trans (inf_isomorphism_of_eq φ) ψ qed

  definition inf_isomorphism.trans_eq [trans] [constructor]
    {G₁ : InfGroup} {G₂ G₃ : InfGroup} (φ : G₁ ≃∞g G₂) (ψ : G₂ = G₃) : G₁ ≃∞g G₃ :=
  inf_isomorphism.trans φ (inf_isomorphism_of_eq ψ)

  postfix `⁻¹ᵍ⁸`:(max + 1) := inf_isomorphism.symm
  infixl ` ⬝∞g `:75 := inf_isomorphism.trans
  infixl ` ⬝∞gp `:75 := inf_isomorphism.trans_eq
  infixl ` ⬝∞pg `:75 := inf_isomorphism.eq_trans

  definition pmap_of_inf_isomorphism [constructor] (φ : G₁ ≃∞g G₂) : G₁ →* G₂ :=
  pequiv_of_inf_isomorphism φ

  definition to_fun_inf_isomorphism_trans {G H K : InfGroup} (φ : G ≃∞g H) (ψ : H ≃∞g K) :
    φ ⬝∞g ψ ~ ψ ∘ φ :=
  by reflexivity

  definition inf_homomorphism_mul [constructor] {G H : AbInfGroup} (φ ψ : G →∞g H) : G →∞g H :=
  inf_homomorphism.mk (λg, φ g * ψ g)
    abstract begin
      intro g g', refine ap011 mul !to_respect_mul_inf !to_respect_mul_inf ⬝ _,
      refine !mul.assoc ⬝ ap (mul _) (!mul.assoc⁻¹ ⬝ ap (λx, x * _) !mul.comm ⬝ !mul.assoc) ⬝
             !mul.assoc⁻¹
    end end

  definition trivial_inf_homomorphism (A B : InfGroup) : A →∞g B :=
  inf_homomorphism.mk (λa, 1) (λa a', (mul_one 1)⁻¹)

  /- given an equivalence A ≃ B we can transport a group structure on A to a group structure on B -/

  section

    parameters {A B : Type} (f : A ≃ B) [inf_group A]

    definition inf_group_equiv_mul (b b' : B) : B := f (f⁻¹ᶠ b * f⁻¹ᶠ b')

    definition inf_group_equiv_one : B := f one

    definition inf_group_equiv_inv (b : B) : B := f (f⁻¹ᶠ b)⁻¹

    local infix * := inf_group_equiv_mul
    local postfix ^ := inf_group_equiv_inv
    local notation 1 := inf_group_equiv_one

    theorem inf_group_equiv_mul_assoc (b₁ b₂ b₃ : B) : (b₁ * b₂) * b₃ = b₁ * (b₂ * b₃) :=
    by rewrite [↑inf_group_equiv_mul, +left_inv f, mul.assoc]

    theorem inf_group_equiv_one_mul (b : B) : 1 * b = b :=
    by rewrite [↑inf_group_equiv_mul, ↑inf_group_equiv_one, left_inv f, one_mul, right_inv f]

    theorem inf_group_equiv_mul_one (b : B) : b * 1 = b :=
    by rewrite [↑inf_group_equiv_mul, ↑inf_group_equiv_one, left_inv f, mul_one, right_inv f]

    theorem inf_group_equiv_mul_left_inv (b : B) : b^ * b = 1 :=
    by rewrite [↑inf_group_equiv_mul, ↑inf_group_equiv_one, ↑inf_group_equiv_inv,
                +left_inv f, mul.left_inv]

    definition inf_group_equiv_closed : inf_group B :=
    ⦃inf_group,
      mul          := inf_group_equiv_mul,
      mul_assoc    := inf_group_equiv_mul_assoc,
      one          := inf_group_equiv_one,
      one_mul      := inf_group_equiv_one_mul,
      mul_one      := inf_group_equiv_mul_one,
      inv          := inf_group_equiv_inv,
      mul_left_inv := inf_group_equiv_mul_left_inv⦄

  end

  section
    variables {A B : Type} (f : A ≃ B) [ab_inf_group A]
    definition inf_group_equiv_mul_comm (b b' : B) : inf_group_equiv_mul f b b' = inf_group_equiv_mul f b' b :=
    by rewrite [↑inf_group_equiv_mul, mul.comm]

    definition ab_inf_group_equiv_closed : ab_inf_group B :=
    ⦃ab_inf_group, inf_group_equiv_closed f,
      mul_comm := inf_group_equiv_mul_comm f⦄
  end

  variable (G)

  /- the trivial ∞-group -/
  open unit
  definition inf_group_unit [constructor] : inf_group unit :=
  inf_group.mk (λx y, star) (λx y z, idp) star (unit.rec idp) (unit.rec idp) (λx, star) (λx, idp)

  definition ab_inf_group_unit [constructor] : ab_inf_group unit :=
  ⦃ab_inf_group, inf_group_unit, mul_comm := λx y, idp⦄

  definition trivial_inf_group [constructor] : InfGroup :=
  InfGroup.mk _ inf_group_unit

  definition AbInfGroup_of_InfGroup (G : InfGroup.{u}) (H : Π x y : G, x * y = y * x) :
    AbInfGroup.{u} :=
  begin
    induction G,
    fapply AbInfGroup.mk,
    assumption,
    exact ⦃ab_inf_group, struct', mul_comm := H⦄
  end

  definition trivial_ab_inf_group : AbInfGroup.{0} :=
  begin
    fapply AbInfGroup_of_InfGroup trivial_inf_group, intro x y, reflexivity
  end

  definition trivial_inf_group_of_is_contr [H : is_contr G] : G ≃∞g trivial_inf_group :=
  begin
    fapply inf_isomorphism_of_equiv,
    { apply equiv_unit_of_is_contr},
    { intros, reflexivity}
  end

  definition ab_inf_group_of_is_contr (A : Type) [is_contr A] : ab_inf_group A :=
  have ab_inf_group unit, from ab_inf_group_unit,
  ab_inf_group_equiv_closed (equiv_unit_of_is_contr A)⁻¹ᵉ

  definition inf_group_of_is_contr (A : Type) [is_contr A] : inf_group A :=
  have ab_inf_group A, from ab_inf_group_of_is_contr A, by apply _

  definition ab_inf_group_lift_unit : ab_inf_group (lift unit) :=
  ab_inf_group_of_is_contr (lift unit)

  definition trivial_ab_inf_group_lift : AbInfGroup :=
  AbInfGroup.mk _ ab_inf_group_lift_unit

  definition from_trivial_ab_inf_group (A : AbInfGroup) : trivial_ab_inf_group →∞g A :=
  trivial_inf_homomorphism trivial_ab_inf_group A

  definition to_trivial_ab_inf_group (A : AbInfGroup) : A →∞g trivial_ab_inf_group :=
  trivial_inf_homomorphism A trivial_ab_inf_group

end group open group

namespace fiber
  open pointed sigma sigma.ops

definition loopn_pfiber [constructor] {A B : Type*} (n : ℕ) (f : A →* B) :
  Ω[n] (pfiber f) ≃* pfiber (Ω→[n] f) :=
begin
  induction n with n IH, reflexivity, exact loop_pequiv_loop IH ⬝e* loop_pfiber (Ω→[n] f),
end

definition fiber_eq_pr2 {A B : Type} {f : A → B} {b : B} {x y : fiber f b}
  (p : x = y) : point_eq x = ap f (ap point p) ⬝ point_eq y :=
begin induction p, exact !idp_con⁻¹ end

definition fiber_eq_eta {A B : Type} {f : A → B} {b : B} {x y : fiber f b}
  (p : x = y) : p = fiber_eq (ap point p) (fiber_eq_pr2 p) :=
begin induction p, induction x with a q, induction q, reflexivity end

definition fiber_eq_con {A B : Type} {f : A → B} {b : B} {x y z : fiber f b}
  (p1 : point x = point y) (p2 : point y = point z)
  (q1 : point_eq x = ap f p1 ⬝ point_eq y) (q2 : point_eq y = ap f p2 ⬝ point_eq z) :
  fiber_eq p1 q1 ⬝ fiber_eq p2 q2 =
  fiber_eq (p1 ⬝ p2) (q1 ⬝ whisker_left (ap f p1) q2 ⬝ !con.assoc⁻¹ ⬝
                       whisker_right (point_eq z) (ap_con f p1 p2)⁻¹) :=
begin
  induction x with a₁ r₁, induction y with a₂ r₂, induction z with a₃ r₃, esimp at *,
  induction q2 using eq.rec_symm, induction q1 using eq.rec_symm,
  induction p2, induction p1, induction r₃, reflexivity
end

definition fiber_eq_equiv' [constructor] {A B : Type} {f : A → B} {b : B} (x y : fiber f b) :
  (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
@equiv_change_inv _ _ (fiber_eq_equiv x y) (λpq, fiber_eq pq.1 pq.2)
  begin intro pq, cases pq, reflexivity end

definition fiber_eq2_equiv {A B : Type} {f : A → B} {b : B} {x y : fiber f b}
  (p₁ p₂ : point x = point y) (q₁ : point_eq x = ap f p₁ ⬝ point_eq y)
  (q₂ : point_eq x = ap f p₂ ⬝ point_eq y) : (fiber_eq p₁ q₁ = fiber_eq p₂ q₂) ≃
  (Σ(r : p₁ = p₂), q₁ ⬝ whisker_right (point_eq y) (ap02 f r) = q₂) :=
begin
  refine (eq_equiv_fn_eq (fiber_eq_equiv' x y)⁻¹ᵉ _ _)⁻¹ᵉ ⬝e sigma_eq_equiv _ _ ⬝e _,
  apply sigma_equiv_sigma_right, esimp, intro r,
  refine !eq_pathover_equiv_square ⬝e _,
  refine eq_hconcat_equiv !ap_constant ⬝e hconcat_eq_equiv (ap_compose (λx, x ⬝ _) _ _) ⬝e _,
  refine !square_equiv_eq ⬝e _,
  exact eq_equiv_eq_closed idp (idp_con q₂)
end

definition fiber_eq2 {A B : Type} {f : A → B} {b : B} {x y : fiber f b}
  {p₁ p₂ : point x = point y} {q₁ : point_eq x = ap f p₁ ⬝ point_eq y}
  {q₂ : point_eq x = ap f p₂ ⬝ point_eq y} (r : p₁ = p₂)
  (s : q₁ ⬝ whisker_right (point_eq y) (ap02 f r) = q₂) : (fiber_eq p₁ q₁ = fiber_eq p₂ q₂) :=
(fiber_eq2_equiv p₁ p₂ q₁ q₂)⁻¹ᵉ ⟨r, s⟩

definition is_contr_pfiber_pid (A : Type*) : is_contr (pfiber (pid A)) :=
is_contr.mk pt begin intro x, induction x with a p, esimp at p, cases p, reflexivity end

definition fiber_functor [constructor] {A A' B B' : Type} {f : A → B} {f' : A' → B'} {b : B} {b' : B'}
  (g : A → A') (h : B → B') (H : hsquare g h f f') (p : h b = b') (x : fiber f b) : fiber f' b' :=
fiber.mk (g (point x)) (H (point x) ⬝ ap h (point_eq x) ⬝ p)

definition pfiber_functor [constructor] {A A' B B' : Type*} {f : A →* B} {f' : A' →* B'}
  (g : A →* A') (h : B →* B') (H : psquare g h f f') : pfiber f →* pfiber f' :=
pmap.mk (fiber_functor g h H (respect_pt h))
  begin
    fapply fiber_eq,
      exact respect_pt g,
      exact !con.assoc ⬝ to_homotopy_pt H
  end

definition ppoint_natural {A A' B B' : Type*} {f : A →* B} {f' : A' →* B'}
  (g : A →* A') (h : B →* B') (H : psquare g h f f') :
  psquare (ppoint f) (ppoint f') (pfiber_functor g h H) g :=
begin
  fapply phomotopy.mk,
  { intro x, reflexivity },
  { refine !idp_con ⬝ _ ⬝ !idp_con⁻¹, esimp, apply point_fiber_eq }
end

/- if we need this: do pfiber_functor_pcompose and so on first -/
-- definition psquare_pfiber_functor [constructor] {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
--   {f₁ : A₁ →* B₁} {f₂ : A₂ →* B₂} {f₃ : A₃ →* B₃} {f₄ : A₄ →* B₄}
--   {g₁₂ : A₁ →* A₂} {g₃₄ : A₃ →* A₄} {g₁₃ : A₁ →* A₃} {g₂₄ : A₂ →* A₄}
--   {h₁₂ : B₁ →* B₂} {h₃₄ : B₃ →* B₄} {h₁₃ : B₁ →* B₃} {h₂₄ : B₂ →* B₄}
--   (H₁₂ : psquare g₁₂ h₁₂ f₁ f₂) (H₃₄ : psquare g₃₄ h₃₄ f₃ f₄)
--   (H₁₃ : psquare g₁₃ h₁₃ f₁ f₃) (H₂₄ : psquare g₂₄ h₂₄ f₂ f₄)
--   (G : psquare g₁₂ g₃₄ g₁₃ g₂₄) (H : psquare h₁₂ h₃₄ h₁₃ h₂₄)
--   /- pcube H₁₂ H₃₄ H₁₃ H₂₄ G H -/ :
--   psquare (pfiber_functor g₁₂ h₁₂ H₁₂) (pfiber_functor g₃₄ h₃₄ H₃₄)
--           (pfiber_functor g₁₃ h₁₃ H₁₃) (pfiber_functor g₂₄ h₂₄ H₂₄) :=
-- begin
--   fapply phomotopy.mk,
--   { intro x, induction x with x p, induction B₁ with B₁ b₁₀, induction f₁ with f₁ f₁₀, esimp at *,
--     induction p, esimp [fiber_functor], },
--   { }
-- end

-- TODO: use this in pfiber_pequiv_of_phomotopy
definition fiber_equiv_of_homotopy {A B : Type} {f g : A → B} (h : f ~ g) (b : B)
  : fiber f b ≃ fiber g b :=
begin
  refine (fiber.sigma_char f b ⬝e _ ⬝e (fiber.sigma_char g b)⁻¹ᵉ),
  apply sigma_equiv_sigma_right, intros a,
  apply equiv_eq_closed_left, apply h
end

definition fiber_equiv_of_square {A B C D : Type} {b : B} {d : D} {f : A → B} {g : C → D} (h : A ≃ C)
  (k : B ≃ D) (s : k ∘ f ~ g ∘ h) (p : k b = d) : fiber f b ≃ fiber g d :=
  calc fiber f b ≃ fiber (k ∘ f) (k b) : fiber.equiv_postcompose
            ... ≃ fiber (k ∘ f) d : transport_fiber_equiv (k ∘ f) p
            ... ≃ fiber (g ∘ h) d : fiber_equiv_of_homotopy s d
            ... ≃ fiber g d : fiber.equiv_precompose

definition fiber_equiv_of_triangle {A B C : Type} {b : B} {f : A → B} {g : C → B} (h : A ≃ C)
  (s : f ~ g ∘ h) : fiber f b ≃ fiber g b :=
fiber_equiv_of_square h erfl s idp

definition is_trunc_fun_id (k : ℕ₋₂) (A : Type) : is_trunc_fun k (@id A) :=
λa, is_trunc_of_is_contr _ _

definition is_conn_fun_id (k : ℕ₋₂) (A : Type) : is_conn_fun k (@id A) :=
λa, _

open sigma.ops is_conn
definition fiber_compose {A B C : Type} (g : B → C) (f : A → B) (c : C) :
  fiber (g ∘ f) c ≃ Σ(x : fiber g c), fiber f (point x) :=
begin
  fapply equiv.MK,
  { intro x, exact ⟨fiber.mk (f (point x)) (point_eq x), fiber.mk (point x) idp⟩ },
  { intro x, exact fiber.mk (point x.2) (ap g (point_eq x.2) ⬝ point_eq x.1) },
  { intro x, induction x with x₁ x₂, induction x₁ with b p, induction x₂ with a q,
    induction p, esimp at q, induction q, reflexivity },
  { intro x, induction x with a p, induction p, reflexivity }
end

definition is_trunc_fun_compose (k : ℕ₋₂) {A B C : Type} {g : B → C} {f : A → B}
  (Hg : is_trunc_fun k g) (Hf : is_trunc_fun k f) : is_trunc_fun k (g ∘ f) :=
λc, is_trunc_equiv_closed_rev k (fiber_compose g f c) _

definition is_conn_fun_compose (k : ℕ₋₂) {A B C : Type} {g : B → C} {f : A → B}
  (Hg : is_conn_fun k g) (Hf : is_conn_fun k f) : is_conn_fun k (g ∘ f) :=
λc, is_conn_equiv_closed_rev k (fiber_compose g f c) _

end fiber open fiber

namespace fin

definition lift_succ2 [constructor] ⦃n : ℕ⦄ (x : fin n) : fin (nat.succ n) :=
fin.mk x (le.step (is_lt x))

end fin

namespace function
  variables {A B : Type} {f f' : A → B}
  open is_conn sigma.ops

  definition is_contr_of_is_surjective (f : A → B) (H : is_surjective f) (HA : is_contr A)
    (HB : is_set B) : is_contr B :=
  is_contr.mk (f !center) begin intro b, induction H b, exact ap f !is_prop.elim ⬝ p end

  definition is_surjective_of_is_contr [constructor] (f : A → B) (a : A) (H : is_contr B) :
    is_surjective f :=
  λb, image.mk a !eq_of_is_contr

  definition is_contr_of_is_embedding (f : A → B) (H : is_embedding f) (HB : is_prop B)
    (a₀ : A) : is_contr A :=
  is_contr.mk a₀ (λa, is_injective_of_is_embedding (is_prop.elim (f a₀) (f a)))

  definition merely_constant {A B : Type} (f : A → B) : Type :=
  Σb, Πa, merely (f a = b)

  definition merely_constant_pmap {A B : Type*} {f : A →* B} (H : merely_constant f) (a : A) :
    merely (f a = pt) :=
  tconcat (tconcat (H.2 a) (tinverse (H.2 pt))) (tr (respect_pt f))

  definition merely_constant_of_is_conn {A B : Type*} (f : A →* B) [is_conn 0 A] : merely_constant f :=
  ⟨pt, is_conn.elim -1 _ (tr (respect_pt f))⟩

  definition homotopy_group_isomorphism_of_is_embedding (n : ℕ) [H : is_succ n] {A B : Type*}
    (f : A →* B) [H2 : is_embedding f] : πg[n] A ≃g πg[n] B :=
  begin
    apply isomorphism.mk (homotopy_group_homomorphism n f),
    induction H with n,
    apply is_equiv_of_equiv_of_homotopy
      (ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn_of_is_embedding (n+1) f)),
    exact sorry
  end

  definition is_embedding_of_square {A B C D : Type} {f : A → B} {g : C → D} (h : A ≃ C)
    (k : B ≃ D) (s : k ∘ f ~ g ∘ h) (Hf : is_embedding f) : is_embedding g :=
  begin
    apply is_embedding_homotopy_closed, exact inv_homotopy_of_homotopy_pre _ _ _ s,
    apply is_embedding_compose, apply is_embedding_compose,
    apply is_embedding_of_is_equiv, exact Hf, apply is_embedding_of_is_equiv
  end

  definition is_embedding_of_square_rev {A B C D : Type} {f : A → B} {g : C → D} (h : A ≃ C)
    (k : B ≃ D) (s : k ∘ f ~ g ∘ h) (Hg : is_embedding g) : is_embedding f :=
  is_embedding_of_square h⁻¹ᵉ k⁻¹ᵉ s⁻¹ʰᵗʸᵛ Hg

end function open function

namespace is_conn

open unit trunc_index nat is_trunc pointed.ops sigma.ops prod.ops

definition is_conn_of_eq {n m : ℕ₋₂} (p : n = m) {A : Type} (H : is_conn n A) : is_conn m A :=
transport (λk, is_conn k A) p H

-- todo: make trunc_equiv_trunc_of_is_conn_fun a def.
definition ptrunc_pequiv_ptrunc_of_is_conn_fun {A B : Type*} (n : ℕ₋₂) (f : A →* B)
  [H : is_conn_fun n f] : ptrunc n A ≃* ptrunc n B :=
pequiv_of_pmap (ptrunc_functor n f) (is_equiv_trunc_functor_of_is_conn_fun n f)

definition is_conn_zero {A : Type} (a₀ : trunc 0 A) (p : Πa a' : A, ∥ a = a' ∥) : is_conn 0 A :=
is_conn_succ_intro a₀ (λa a', is_conn_minus_one _ (p a a'))

definition is_conn_zero_pointed {A : Type*} (p : Πa a' : A, ∥ a = a' ∥) : is_conn 0 A :=
is_conn_zero (tr pt) p

definition is_conn_zero_pointed' {A : Type*} (p : Πa : A, ∥ a = pt ∥) : is_conn 0 A :=
is_conn_zero_pointed (λa a', tconcat (p a) (tinverse (p a')))

definition is_conn_fiber (n : ℕ₋₂) {A B : Type} (f : A → B) (b : B) [is_conn n A]
  [is_conn (n.+1) B] : is_conn n (fiber f b) :=
is_conn_equiv_closed_rev _ !fiber.sigma_char _

definition is_conn_succ_of_is_conn_loop {n : ℕ₋₂} {A : Type*}
  (H : is_conn 0 A) (H2 : is_conn n (Ω A)) : is_conn (n.+1) A :=
begin
  apply is_conn_succ_intro, exact tr pt,
  intros a a',
  induction merely_of_minus_one_conn (is_conn_eq -1 a a') with p, induction p,
  induction merely_of_minus_one_conn (is_conn_eq -1 pt a) with p, induction p,
  exact H2
end

definition is_conn_fun_compose {n : ℕ₋₂} {A B C : Type} (g : B → C) (f : A → B)
  (H : is_conn_fun n g) (K : is_conn_fun n f) : is_conn_fun n (g ∘ f) :=
sorry

definition pconntype.sigma_char [constructor] (k : ℕ₋₂) :
  Type*[k] ≃ Σ(X : Type*), is_conn k X :=
equiv.MK (λX, ⟨pconntype.to_pType X, _⟩)
         (λX, pconntype.mk (carrier X.1) X.2 pt)
         begin intro X, induction X with X HX, induction X, reflexivity end
         begin intro X, induction X, reflexivity end

definition is_embedding_pconntype_to_pType (k : ℕ₋₂) : is_embedding (@pconntype.to_pType k) :=
begin
  intro X Y, fapply is_equiv_of_equiv_of_homotopy,
  { exact eq_equiv_fn_eq (pconntype.sigma_char k) _ _ ⬝e subtype_eq_equiv _ _ },
  intro p, induction p, reflexivity
end

definition pconntype_eq_equiv {k : ℕ₋₂} (X Y : Type*[k]) : (X = Y) ≃ (X ≃* Y) :=
equiv.mk _ (is_embedding_pconntype_to_pType k X Y) ⬝e pType_eq_equiv X Y

definition pconntype_eq {k : ℕ₋₂} {X Y : Type*[k]} (e : X ≃* Y) : X = Y :=
(pconntype_eq_equiv X Y)⁻¹ᵉ e

definition ptruncconntype.sigma_char [constructor] (n k : ℕ₋₂) :
  n-Type*[k] ≃ Σ(X : Type*), is_trunc n X × is_conn k X :=
equiv.MK (λX, ⟨ptruncconntype._trans_of_to_pconntype_1 X, (_, _)⟩)
         (λX, ptruncconntype.mk (carrier X.1) X.2.1 pt X.2.2)
         begin intro X, induction X with X HX, induction HX, induction X, reflexivity end
         begin intro X, induction X, reflexivity end

definition ptruncconntype.sigma_char_pconntype [constructor] (n k : ℕ₋₂) :
  n-Type*[k] ≃ Σ(X : Type*[k]), is_trunc n X :=
equiv.MK (λX, ⟨ptruncconntype.to_pconntype X, _⟩)
         (λX, ptruncconntype.mk (pconntype._trans_of_to_pType X.1) X.2 pt _)
         begin intro X, induction X with X HX, induction HX, induction X, reflexivity end
         begin intro X, induction X, reflexivity end

definition is_embedding_ptruncconntype_to_pconntype (n k : ℕ₋₂) :
  is_embedding (@ptruncconntype.to_pconntype n k) :=
begin
  intro X Y, fapply is_equiv_of_equiv_of_homotopy,
  { exact eq_equiv_fn_eq (ptruncconntype.sigma_char_pconntype n k) _ _ ⬝e subtype_eq_equiv _ _ },
  intro p, induction p, reflexivity
end

definition ptruncconntype_eq_equiv {n k : ℕ₋₂} (X Y : n-Type*[k]) : (X = Y) ≃ (X ≃* Y) :=
equiv.mk _ (is_embedding_ptruncconntype_to_pconntype n k X Y) ⬝e
pconntype_eq_equiv X Y

/- duplicate -/
definition ptruncconntype_eq {n k : ℕ₋₂} {X Y : n-Type*[k]} (e : X ≃* Y) : X = Y :=
(ptruncconntype_eq_equiv X Y)⁻¹ᵉ e

definition ptruncconntype_functor [constructor] {n n' k k' : ℕ₋₂} (p : n = n') (q : k = k')
  (X : n-Type*[k]) : n'-Type*[k'] :=
ptruncconntype.mk X (is_trunc_of_eq p _) pt (is_conn_of_eq q _)

definition ptruncconntype_equiv [constructor] {n n' k k' : ℕ₋₂} (p : n = n') (q : k = k') :
  n-Type*[k] ≃ n'-Type*[k'] :=
equiv.MK (ptruncconntype_functor p q) (ptruncconntype_functor p⁻¹ q⁻¹)
         (λX, ptruncconntype_eq pequiv.rfl) (λX, ptruncconntype_eq pequiv.rfl)

-- definition is_conn_pfiber_of_equiv_on_homotopy_groups (n : ℕ) {A B : pType.{u}} (f : A →* B)
--   [H : is_conn 0 A]
--   (H1 : Πk, k ≤ n → is_equiv (π→[k] f))
--   (H2 : is_surjective (π→[succ n] f)) :
--   is_conn n (pfiber f) :=
-- _

-- definition is_conn_pelim [constructor] {k : ℕ} {X : Type*} (Y : Type*) (H : is_conn k X) :
--   (X →* connect k Y) ≃ (X →* Y) :=

/- the k-connected cover of X, the fiber of the map X → ∥X∥ₖ. -/
definition connect (k : ℕ) (X : Type*) : Type* :=
pfiber (ptr k X)

definition is_conn_connect (k : ℕ) (X : Type*) : is_conn k (connect k X) :=
is_conn_fun_tr k X (tr pt)

definition connconnect [constructor] (k : ℕ) (X : Type*) : Type*[k]  :=
pconntype.mk (connect k X) (is_conn_connect k X) pt

definition connect_intro [constructor] {k : ℕ} {X : Type*} {Y : Type*} (H : is_conn k X)
  (f : X →* Y) : X →* connect k Y :=
pmap.mk (λx, fiber.mk (f x) (is_conn.elim (k.-1) _ (ap tr (respect_pt f)) x))
  begin
    fapply fiber_eq, exact respect_pt f, apply is_conn.elim_β
  end

definition ppoint_connect_intro [constructor] {k : ℕ} {X : Type*} {Y : Type*} (H : is_conn k X)
  (f : X →* Y) : ppoint (ptr k Y) ∘* connect_intro H f ~* f :=
begin
  induction f with f f₀, induction Y with Y y₀, esimp at (f,f₀), induction f₀,
  fapply phomotopy.mk,
  { intro x, reflexivity },
  { symmetry, esimp, apply point_fiber_eq }
end

definition connect_intro_ppoint [constructor] {k : ℕ} {X : Type*} {Y : Type*} (H : is_conn k X)
  (f : X →* connect k Y) : connect_intro H (ppoint (ptr k Y) ∘* f) ~* f :=
begin
  cases f with f f₀,
  fapply phomotopy.mk,
  { intro x, fapply fiber_eq, reflexivity,
    refine @is_conn.elim (k.-1) _ _ _ (λx', !is_trunc_eq) _ x,
    refine !is_conn.elim_β ⬝ _,
    refine _ ⬝ !idp_con⁻¹,
    symmetry, refine _ ⬝ !con_idp, exact fiber_eq_pr2 f₀ },
  { esimp, refine whisker_left _ !fiber_eq_eta ⬝ !fiber_eq_con ⬝ apd011 fiber_eq !idp_con _, esimp,
    apply eq_pathover_constant_left,
    refine whisker_right _ (whisker_right _ (whisker_right _ !is_conn.elim_β)) ⬝pv _,
    esimp [connect], refine _ ⬝vp !con_idp,
    apply move_bot_of_left, refine !idp_con ⬝ !con_idp⁻¹ ⬝ph _,
    refine !con.assoc ⬝ !con.assoc ⬝pv _, apply whisker_tl,
    note r := eq_bot_of_square (transpose (whisker_left_idp_square (fiber_eq_pr2 f₀))⁻¹ᵛ),
    refine !con.assoc⁻¹ ⬝ whisker_right _ r⁻¹ ⬝pv _, clear r,
    apply move_top_of_left,
    refine whisker_right_idp (ap_con tr idp (ap point f₀))⁻¹ᵖ ⬝pv _,
    exact (ap_con_idp_left tr (ap point f₀))⁻¹ʰ }
end

definition connect_intro_equiv [constructor] {k : ℕ} {X : Type*} (Y : Type*) (H : is_conn k X) :
  (X →* connect k Y) ≃ (X →* Y) :=
begin
  fapply equiv.MK,
  { intro f, exact ppoint (ptr k Y) ∘*  f },
  { intro g, exact connect_intro H g },
  { intro g, apply eq_of_phomotopy, exact ppoint_connect_intro H g },
  { intro f, apply eq_of_phomotopy, exact connect_intro_ppoint H f }
end

definition connect_intro_pequiv [constructor] {k : ℕ} {X : Type*} (Y : Type*) (H : is_conn k X) :
  ppmap X (connect k Y) ≃* ppmap X Y :=
pequiv_of_equiv (connect_intro_equiv Y H) (eq_of_phomotopy !pcompose_pconst)

definition connect_pequiv {k : ℕ} {X : Type*} (H : is_conn k X) : connect k X ≃* X :=
@pfiber_pequiv_of_is_contr _ _ (ptr k X) H

definition loop_connect (k : ℕ) (X : Type*) : Ω (connect (k+1) X) ≃* connect k (Ω X) :=
loop_pfiber (ptr (k+1) X) ⬝e*
pfiber_pequiv_of_square pequiv.rfl (loop_ptrunc_pequiv k X)
  (phomotopy_of_phomotopy_pinv_left (ap1_ptr k X))

definition loopn_connect (k : ℕ) (X : Type*) : Ω[k+1] (connect k X) ≃* Ω[k+1] X :=
loopn_pfiber (k+1) (ptr k X) ⬝e*
@pfiber_pequiv_of_is_contr _ _ _ (@is_contr_loop_of_is_trunc (k+1) _ !is_trunc_trunc)

definition is_conn_of_is_conn_succ_nat (n : ℕ) (A : Type) [is_conn (n+1) A] : is_conn n A :=
is_conn_of_is_conn_succ n A

definition connect_functor (k : ℕ) {X Y : Type*} (f : X →* Y) : connect k X →* connect k Y :=
pfiber_functor f (ptrunc_functor k f) (ptr_natural k f)⁻¹*

definition connect_intro_pequiv_natural {k : ℕ} {X X' : Type*} {Y Y' : Type*} (f : X' →* X)
  (g : Y →* Y') (H : is_conn k X) (H' : is_conn k X') :
  psquare (connect_intro_pequiv Y H) (connect_intro_pequiv Y' H')
          (ppcompose_left (connect_functor k g) ∘* ppcompose_right f)
          (ppcompose_left g ∘* ppcompose_right f) :=
begin
  refine _ ⬝v* _, exact connect_intro_pequiv Y H',
  { fapply phomotopy.mk,
    { intro h, apply eq_of_phomotopy, apply passoc },
    { xrewrite [▸*, pcompose_right_eq_of_phomotopy, pcompose_left_eq_of_phomotopy,
        -+eq_of_phomotopy_trans],
      apply ap eq_of_phomotopy, apply passoc_pconst_middle }},
  { fapply phomotopy.mk,
    { intro h, apply eq_of_phomotopy,
      refine !passoc⁻¹* ⬝* pwhisker_right h (ppoint_natural _ _ _) ⬝* !passoc },
    { xrewrite [▸*, +pcompose_left_eq_of_phomotopy, -+eq_of_phomotopy_trans],
      apply ap eq_of_phomotopy,
      refine !trans_assoc ⬝ idp ◾** !passoc_pconst_right ⬝ _,
      refine !trans_assoc ⬝ idp ◾** !pcompose_pconst_phomotopy ⬝ _,
      apply symm_trans_eq_of_eq_trans, symmetry, apply passoc_pconst_right }}
end

end is_conn

namespace misc
  open is_conn

  open sigma.ops pointed trunc_index

  /- this is equivalent to pfiber (A → ∥A∥₀) ≡ connect 0 A -/
  definition component [constructor] (A : Type*) : Type* :=
  pType.mk (Σ(a : A), merely (pt = a)) ⟨pt, tr idp⟩

  lemma is_conn_component [instance] (A : Type*) : is_conn 0 (component A) :=
  is_conn_zero_pointed'
    begin intro x, induction x with a p, induction p with p, induction p, exact tidp end

  definition component_incl [constructor] (A : Type*) : component A →* A :=
  pmap.mk pr1 idp

  definition is_embedding_component_incl [instance] (A : Type*) : is_embedding (component_incl A) :=
  is_embedding_pr1 _

  definition component_intro [constructor] {A B : Type*} (f : A →* B) (H : merely_constant f) :
    A →* component B :=
  begin
    fapply pmap.mk,
    { intro a, refine ⟨f a, _⟩, exact tinverse (merely_constant_pmap H a) },
    exact subtype_eq !respect_pt
  end

  definition component_functor [constructor] {A B : Type*} (f : A →* B) : component A →* component B :=
  component_intro (f ∘* component_incl A) !merely_constant_of_is_conn

  -- definition component_elim [constructor] {A B : Type*} (f : A →* B) (H : merely_constant f) :
  --   A →* component B :=
  -- begin
  --   fapply pmap.mk,
  --   { intro a, refine ⟨f a, _⟩, exact tinverse (merely_constant_pmap H a) },
  --   exact subtype_eq !respect_pt
  -- end

  definition loop_component (A : Type*) : Ω (component A) ≃* Ω A :=
  loop_pequiv_loop_of_is_embedding (component_incl A)

  lemma loopn_component (n : ℕ) (A : Type*) : Ω[n+1] (component A) ≃* Ω[n+1] A :=
  !loopn_succ_in ⬝e* loopn_pequiv_loopn n (loop_component A) ⬝e* !loopn_succ_in⁻¹ᵉ*

  -- lemma fundamental_group_component (A : Type*) : π₁ (component A) ≃g π₁ A :=
  -- isomorphism_of_equiv (trunc_equiv_trunc 0 (loop_component A)) _

  lemma homotopy_group_component (n : ℕ) (A : Type*) : πg[n+1] (component A) ≃g πg[n+1] A :=
  homotopy_group_isomorphism_of_is_embedding (n+1) (component_incl A)

  definition is_trunc_component [instance] (n : ℕ₋₂) (A : Type*) [is_trunc n A] :
    is_trunc n (component A) :=
  begin
    apply @is_trunc_sigma, intro a, cases n with n,
    { apply is_contr_of_inhabited_prop, exact tr !is_prop.elim },
    { apply is_trunc_succ_of_is_prop },
  end

  definition ptrunc_component' (n : ℕ₋₂) (A : Type*) :
    ptrunc (n.+2) (component A) ≃* component (ptrunc (n.+2) A) :=
  begin
    fapply pequiv.MK',
    { exact ptrunc.elim (n.+2) (component_functor !ptr) },
    { intro x, cases x with x p, induction x with a,
      refine tr ⟨a, _⟩,
      note q := trunc_functor -1 !tr_eq_tr_equiv p,
      exact trunc_trunc_equiv_left _ !minus_one_le_succ q },
    { exact sorry },
    { exact sorry }
  end

  definition ptrunc_component (n : ℕ₋₂) (A : Type*) :
    ptrunc n (component A) ≃* component (ptrunc n A) :=
  begin
    cases n with n, exact sorry,
    cases n with n, exact sorry,
    exact ptrunc_component' n A
  end

  definition break_into_components (A : Type) : A ≃ Σ(x : trunc 0 A), Σ(a : A), ∥ tr a = x ∥ :=
  calc
    A ≃ Σ(a : A) (x : trunc 0 A), tr a = x :
        by exact (@sigma_equiv_of_is_contr_right _ _ (λa, !is_contr_sigma_eq))⁻¹ᵉ
  ... ≃ Σ(x : trunc 0 A) (a : A), tr a = x :
        by apply sigma_comm_equiv
  ... ≃ Σ(x : trunc 0 A), Σ(a : A), ∥ tr a = x ∥ :
        by exact sigma_equiv_sigma_right (λx, sigma_equiv_sigma_right (λa, !trunc_equiv⁻¹ᵉ))

  definition pfiber_pequiv_component_of_is_contr [constructor] {A B : Type*} (f : A →* B) [is_contr B]
    /- extra condition, something like trunc_functor 0 f is an embedding -/ : pfiber f ≃* component A :=
  sorry

end misc

namespace sphere

  -- definition constant_sphere_map_sphere {n m : ℕ} (H : n < m) (f : S n →* S m) :
  --   f ~* pconst (S n) (S m) :=
  -- begin
  --   assert H : is_contr (Ω[n] (S m)),
  --   { apply homotopy_group_sphere_le, },
  --   apply phomotopy_of_eq,
  --   apply inj !sphere_pmap_pequiv,
  --   apply @is_prop.elim
  -- end

end sphere

section injective_surjective
open trunc fiber image

  /- do we want to prove this without funext before we move it? -/
  variables {A B C : Type} (f : A → B)
  definition is_embedding_factor [is_set A] [is_set B] (g : B → C) (h : A → C) (H : g ∘ f ~ h) :
    is_embedding h → is_embedding f :=
  begin
    induction H using homotopy.rec_on_idp,
    intro E,
    fapply is_embedding_of_is_injective,
    intro x y p,
    fapply @is_injective_of_is_embedding _ _ _ E _ _ (ap g p)
  end

  definition is_surjective_factor (g : B → C) (h : A → C) (H : g ∘ f ~ h) :
    is_surjective h → is_surjective g :=
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

-- Yuri Sulyma's code from HoTT MRC

definition ap1_phomotopy_symm {A B : Type*} {f g : A →* B} (p : f ~* g) : (Ω⇒ p)⁻¹* = Ω⇒ (p⁻¹*) :=
begin
  induction p using phomotopy_rec_idp,
  rewrite ap1_phomotopy_refl,
  xrewrite [+refl_symm],
  rewrite ap1_phomotopy_refl
end

definition ap1_phomotopy_trans {A B : Type*} {f g h : A →* B} (q : g ~* h) (p : f ~* g) : Ω⇒ (p ⬝* q) = Ω⇒ p ⬝* Ω⇒ q :=
begin
  induction p using phomotopy_rec_idp,
  induction q using phomotopy_rec_idp,
  rewrite trans_refl,
  rewrite [+ap1_phomotopy_refl],
  rewrite trans_refl
end

namespace pointed

  definition pbool_pequiv_add_point_unit [constructor] : pbool ≃* unit₊ :=
  pequiv_of_equiv (bool_equiv_option_unit) idp

  definition to_homotopy_pt_mk {A B : Type*} {f g : A →* B} (h : f ~ g)
    (p : h pt ⬝ respect_pt g = respect_pt f) : to_homotopy_pt (phomotopy.mk h p) = p :=
  to_right_inv !eq_con_inv_equiv_con_eq p


  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type*}
            {f₁₀ : A₀₀ →* A₂₀} {f₁₂ : A₀₂ →* A₂₂}
            {f₀₁ : A₀₀ →* A₀₂} {f₂₁ : A₂₀ →* A₂₂}
  definition psquare_transpose (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : psquare f₀₁ f₂₁ f₁₀ f₁₂ := p⁻¹*

end pointed

namespace pi
  definition pi_bool_left_nat {A B : bool → Type} (g : Πx, A x -> B x) :
             hsquare (pi_bool_left A) (pi_bool_left B) (pi_functor_right g) (prod_functor (g ff) (g tt)) :=
  begin intro h, esimp end

  definition pi_bool_left_inv_nat {A B : bool → Type} (g : Πx, A x -> B x) :
              hsquare (pi_bool_left A)⁻¹ᵉ (pi_bool_left B)⁻¹ᵉ (prod_functor (g ff) (g tt)) (pi_functor_right g) := hhinverse (pi_bool_left_nat g)

end pi

namespace sum

  infix ` +→ `:62 := sum_functor

  variables {A₀₀ A₂₀ A₀₂ A₂₂ B₀₀ B₂₀ B₀₂ B₂₂ A A' B B' C C' : Type}
    {f₁₀ : A₀₀ → A₂₀} {f₁₂ : A₀₂ → A₂₂} {f₀₁ : A₀₀ → A₀₂} {f₂₁ : A₂₀ → A₂₂}
    {g₁₀ : B₀₀ → B₂₀} {g₁₂ : B₀₂ → B₂₂} {g₀₁ : B₀₀ → B₀₂} {g₂₁ : B₂₀ → B₂₂}
    {h₀₁ : B₀₀ → A₀₂} {h₂₁ : B₂₀ → A₂₂}

  definition flip_flip (x : A ⊎ B) : flip (flip x) = x :=
  begin induction x: reflexivity end

  definition sum_rec_hsquare [unfold 16] (h : hsquare f₁₀ f₁₂ f₀₁ f₂₁)
    (k : hsquare g₁₀ f₁₂ h₀₁ h₂₁) : hsquare (f₁₀ +→ g₁₀) f₁₂ (sum.rec f₀₁ h₀₁) (sum.rec f₂₁ h₂₁) :=
  begin intro x, induction x with a b, exact h a, exact k b end

  definition sum_functor_hsquare [unfold 19] (h : hsquare f₁₀ f₁₂ f₀₁ f₂₁)
    (k : hsquare g₁₀ g₁₂ g₀₁ g₂₁) : hsquare (f₁₀ +→ g₁₀) (f₁₂ +→ g₁₂) (f₀₁ +→ g₀₁) (f₂₁ +→ g₂₁) :=
  sum_rec_hsquare (λa, ap inl (h a)) (λb, ap inr (k b))

  definition sum_functor_compose (g : B → C) (f : A → B) (g' : B' → C') (f' : A' → B') :
    (g ∘ f) +→ (g' ∘ f') ~ g +→ g' ∘ f +→ f' :=
  begin intro x, induction x with a a': reflexivity end

  definition sum_rec_sum_functor (g : B → C) (g' : B' → C) (f : A → B) (f' : A' → B') :
    sum.rec g g' ∘ sum_functor f f' ~ sum.rec (g ∘ f) (g' ∘ f') :=
  begin intro x, induction x with a a': reflexivity end

  definition sum_rec_same_compose (g : B → C) (f : A → B) :
    sum.rec (g ∘ f) (g ∘ f) ~ g ∘ sum.rec f f :=
  begin intro x, induction x with a a': reflexivity end

  definition sum_rec_same (f : A → B) :
    sum.rec f f ~ f ∘ sum.rec id id :=
  sum_rec_same_compose f id

end sum

namespace prod

  infix ` ×→ `:63 := prod_functor
  infix ` ×≃ `:63 := prod_equiv_prod

  definition pprod_incl1 [constructor] (X Y : Type*) : X →* X ×* Y := pmap.mk (λx, (x, pt)) idp
  definition pprod_incl2 [constructor] (X Y : Type*) : Y →* X ×* Y := pmap.mk (λy, (pt, y)) idp

end prod

namespace equiv

  definition rec_eq_of_equiv {A : Type} {P : A → A → Type} (e : Πa a', a = a' ≃ P a a')
    {a a' : A} (Q : P a a' → Type) (H : Π(q : a = a'), Q (e a a' q)) :
    Π(p : P a a'), Q p :=
  equiv_rect (e a a') Q H

  definition rec_idp_of_equiv {A : Type} {P : A → A → Type} (e : Πa a', a = a' ≃ P a a') {a : A}
    (r : P a a) (s : e a a idp = r) (Q : Πa', P a a' → Type) (H : Q a r) ⦃a' : A⦄ (p : P a a') :
    Q a' p :=
  rec_eq_of_equiv e _ begin intro q, induction q, induction s, exact H end p

  definition rec_idp_of_equiv_idp {A : Type} {P : A → A → Type} (e : Πa a', a = a' ≃ P a a') {a : A}
    (r : P a a) (s : e a a idp = r) (Q : Πa', P a a' → Type) (H : Q a r) :
    rec_idp_of_equiv e r s Q H r = H :=
  begin
    induction s, refine !is_equiv_rect_comp ⬝ _, reflexivity
  end

end equiv


namespace paths

variables {A : Type} {R : A → A → Type} {a₁ a₂ a₃ a₄ : A}
inductive all (T : Π⦃a₁ a₂ : A⦄, R a₁ a₂ → Type) : Π⦃a₁ a₂ : A⦄, paths R a₁ a₂ → Type :=
| nil {} : Π{a : A}, all T (@nil A R a)
| cons   : Π{a₁ a₂ a₃ : A} {r : R a₂ a₃} {p : paths R a₁ a₂}, T r → all T p → all T (cons r p)

inductive Exists (T : Π⦃a₁ a₂ : A⦄, R a₁ a₂ → Type) : Π⦃a₁ a₂ : A⦄, paths R a₁ a₂ → Type :=
| base : Π{a₁ a₂ a₃ : A} {r : R a₂ a₃} (p : paths R a₁ a₂), T r → Exists T (cons r p)
| cons : Π{a₁ a₂ a₃ : A} (r : R a₂ a₃) {p : paths R a₁ a₂}, Exists T p → Exists T (cons r p)

inductive mem (l : R a₃ a₄) : Π⦃a₁ a₂ : A⦄, paths R a₁ a₂ → Type :=
| base : Π{a₂ : A} (p : paths R a₂ a₃), mem l (cons l p)
| cons : Π{a₁ a₂ a₃ : A} (r : R a₂ a₃) {p : paths R a₁ a₂}, mem l p → mem l (cons r p)

definition len (p : paths R a₁ a₂) : ℕ :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { exact 0 },
  { exact nat.succ IH }
end

definition mem_equiv_Exists (l : R a₁ a₂) (p : paths R a₃ a₄) :
  mem l p ≃ Exists (λa a' r, ⟨a₁, a₂, l⟩ = ⟨a, a', r⟩) p :=
sorry

end paths

namespace list
open is_trunc trunc sigma.ops prod.ops lift
variables {A B X : Type}

definition foldl_homotopy {f g : A → B → A} (h : f ~2 g) (a : A) : foldl f a ~ foldl g a :=
begin
  intro bs, revert a, induction bs with b bs p: intro a, reflexivity, esimp [foldl],
  exact p (f a b) ⬝ ap010 (foldl g) (h a b) bs
end

definition cons_eq_cons {x x' : X} {l l' : list X} (p : x::l = x'::l') : x = x' × l = l' :=
begin
  refine lift.down (list.no_confusion p _), intro q r, split, exact q, exact r
end

definition concat_neq_nil (x : X) (l : list X) : concat x l ≠ nil :=
begin
  intro p, cases l: cases p,
end

definition concat_eq_singleton {x x' : X} {l : list X} (p : concat x l = [x']) :
  x = x' × l = [] :=
begin
  cases l with x₂ l,
  { cases cons_eq_cons p with q r, subst q, split: reflexivity },
  { exfalso, esimp [concat] at p, apply concat_neq_nil x l, revert p, generalize (concat x l),
    intro l' p, cases cons_eq_cons p with q r, exact r }
end

definition foldr_concat (f : A → B → B) (b : B) (a : A) (l : list A) :
  foldr f b (concat a l) = foldr f (f a b) l :=
begin
  induction l with a' l p, reflexivity, rewrite [concat_cons, foldr_cons, p]
end

definition iterated_prod (X : Type.{u}) (n : ℕ) : Type.{u} :=
iterate (prod X) n (lift unit)

definition is_trunc_iterated_prod {k : ℕ₋₂} {X : Type} {n : ℕ} (H : is_trunc k X) :
  is_trunc k (iterated_prod X n) :=
begin
  induction n with n IH,
  { apply is_trunc_of_is_contr, apply is_trunc_lift },
  { exact @is_trunc_prod _ _ _ H IH }
end

definition list_of_iterated_prod {n : ℕ} (x : iterated_prod X n) : list X :=
begin
  induction n with n IH,
  { exact [] },
  { exact x.1::IH x.2 }
end

definition list_of_iterated_prod_succ {n : ℕ} (x : X) (xs : iterated_prod X n) :
  @list_of_iterated_prod X (succ n) (x, xs) = x::list_of_iterated_prod xs :=
by reflexivity

definition iterated_prod_of_list (l : list X) : Σn, iterated_prod X n :=
begin
  induction l with x l IH,
  { exact ⟨0, up ⋆⟩ },
  { exact ⟨succ IH.1, (x, IH.2)⟩ }
end

definition iterated_prod_of_list_cons (x : X) (l : list X) :
  iterated_prod_of_list (x::l) =
  ⟨succ (iterated_prod_of_list l).1, (x, (iterated_prod_of_list l).2)⟩ :=
by reflexivity

protected definition sigma_char [constructor] (X : Type) : list X ≃ Σ(n : ℕ), iterated_prod X n :=
begin
  apply equiv.MK iterated_prod_of_list (λv, list_of_iterated_prod v.2),
  { intro x, induction x with n x, esimp, induction n with n IH,
    { induction x with x, induction x, reflexivity },
    { revert x, change Π(x : X × iterated_prod X n), _, intro xs, cases xs with x xs,
      rewrite [list_of_iterated_prod_succ, iterated_prod_of_list_cons],
      apply sigma_eq (ap succ (IH xs)..1),
      apply pathover_ap, refine prod_pathover _ _ _ _ (IH xs)..2,
      apply pathover_of_eq, reflexivity }},
  { intro l, induction l with x l IH,
    { reflexivity },
    { exact ap011 cons idp IH }}
end

local attribute [instance] is_trunc_iterated_prod
definition is_trunc_list [instance] {n : ℕ₋₂} {X : Type} (H : is_trunc (n.+2) X) :
  is_trunc (n.+2) (list X) :=
begin
  assert H : is_trunc (n.+2) (Σ(k : ℕ), iterated_prod X k),
  { apply is_trunc_sigma, apply is_trunc_succ_succ_of_is_set,
    intro, exact is_trunc_iterated_prod H },
  apply is_trunc_equiv_closed_rev _ (list.sigma_char X) _,
end

end list

namespace chain_complex

open fin
definition LES_is_contr_of_is_embedding_of_is_surjective (n : ℕ) {X Y : pType.{u}} (f : X →* Y)
  (H : is_embedding (π→[n] f)) (H2 : is_surjective (π→[n+1] f)) : is_contr (π[n] (pfiber f)) :=
begin
  rexact @is_contr_of_is_embedding_of_is_surjective +3ℕ (LES_of_homotopy_groups f) (n, 0)
    (is_exact_LES_of_homotopy_groups f _) proof H qed proof H2 qed
end

end chain_complex

namespace susp
open trunc_index
/- move to freudenthal -/
definition freudenthal_pequiv_trunc_index' (A : Type*) (n : ℕ) (k : ℕ₋₂) [HA : is_conn n A]
  (H : k ≤ of_nat (2 * n)) : ptrunc k A ≃* ptrunc k (Ω (susp A)) :=
begin
  assert lem : Π(l : ℕ₋₂), l ≤ 0 → ptrunc l A ≃* ptrunc l (Ω (susp A)),
  { intro l H', exact ptrunc_pequiv_ptrunc_of_le H' (freudenthal_pequiv (zero_le (2 * n)) A) },
  cases k with k, { exact lem -2 (minus_two_le 0) },
  cases k with k, { exact lem -1 (succ_le_succ (minus_two_le -1)) },
  rewrite [-of_nat_add_two at *, add_two_sub_two at HA],
  exact freudenthal_pequiv (le_of_of_nat_le_of_nat H) A
end

end susp

/- namespace logic? -/
namespace decidable
definition double_neg_elim {A : Type} (H : decidable A) (p : ¬ ¬ A) : A :=
begin induction H, assumption, contradiction end


definition dite_true {C : Type} [H : decidable C] {A : Type}
  {t : C → A} {e : ¬ C → A} (c : C) (H' : is_prop C) : dite C t e = t c :=
begin
  induction H with H H,
  exact ap t !is_prop.elim,
  contradiction
end

definition dite_false {C : Type} [H : decidable C] {A : Type}
  {t : C → A} {e : ¬ C → A} (c : ¬ C) : dite C t e = e c :=
begin
  induction H with H H,
  contradiction,
  exact ap e !is_prop.elim,
end

definition decidable_eq_of_is_prop (A : Type) [is_prop A] : decidable_eq A :=
λa a', decidable.inl !is_prop.elim

definition decidable_eq_sigma [instance] {A : Type} (B : A → Type) [HA : decidable_eq A]
  [HB : Πa, decidable_eq (B a)] : decidable_eq (Σa, B a) :=
begin
  intro v v', induction v with a b, induction v' with a' b',
  cases HA a a' with p np,
  { induction p, cases HB a b b' with q nq,
      induction q, exact decidable.inl idp,
      apply decidable.inr, intro p, apply nq, apply @eq_of_pathover_idp A B,
      exact change_path !is_prop.elim p..2 },
  { apply decidable.inr, intro p, apply np, exact p..1 }
end

open sum
definition decidable_eq_sum [instance] (A B : Type) [HA : decidable_eq A] [HB : decidable_eq B] :
  decidable_eq (A ⊎ B) :=
begin
  intro v v', induction v with a b: induction v' with a' b',
  { cases HA a a' with p np,
    { exact decidable.inl (ap sum.inl p) },
    { apply decidable.inr, intro p, cases p, apply np, reflexivity }},
  { apply decidable.inr, intro p, cases p },
  { apply decidable.inr, intro p, cases p },
  { cases HB b b' with p np,
    { exact decidable.inl (ap sum.inr p) },
    { apply decidable.inr, intro p, cases p, apply np, reflexivity }},
end
end decidable

namespace category
  open functor
  /- shortening pullback to pb to keep names relatively short -/
  definition pb_precategory [constructor] {A B : Type} (f : A → B) (C : precategory B) :
    precategory A :=
  precategory.mk (λa a', hom (f a) (f a')) (λa a' a'' h g, h ∘ g) (λa, ID (f a))
    (λa a' a'' a''' k h g, assoc k h g) (λa a' g, id_left g) (λa a' g, id_right g)

  definition pb_Precategory [constructor] {A : Type} (C : Precategory) (f : A → C) :
    Precategory :=
  Precategory.mk A (pb_precategory f C)

  definition pb_Precategory_functor [constructor] {A : Type} (C : Precategory) (f : A → C) :
    pb_Precategory C f ⇒ C :=
  functor.mk f (λa a' g, g) proof (λa, idp) qed proof (λa a' a'' h g, idp) qed

  definition fully_faithful_pb_Precategory_functor {A : Type} (C : Precategory)
    (f : A → C) : fully_faithful (pb_Precategory_functor C f) :=
  begin intro a a', apply is_equiv_id end

  definition split_essentially_surjective_pb_Precategory_functor {A : Type} (C : Precategory)
    (f : A → C) (H : is_split_surjective f) :
    split_essentially_surjective (pb_Precategory_functor C f) :=
  begin intro c, cases H c with a p, exact ⟨a, iso.iso_of_eq p⟩ end

  definition is_equivalence_pb_Precategory_functor {A : Type} (C : Precategory)
    (f : A → C) (H : is_split_surjective f) : is_equivalence (pb_Precategory_functor C f) :=
  @(is_equivalence_of_fully_faithful_of_split_essentially_surjective _)
    (fully_faithful_pb_Precategory_functor C f)
    (split_essentially_surjective_pb_Precategory_functor C f H)

  definition pb_Precategory_equivalence [constructor] {A : Type} (C : Precategory) (f : A → C)
    (H : is_split_surjective f) : pb_Precategory C f ≃c C :=
  equivalence.mk _ (is_equivalence_pb_Precategory_functor C f H)

  definition pb_Precategory_equivalence_of_equiv [constructor] {A : Type} (C : Precategory)
    (f : A ≃ C) : pb_Precategory C f ≃c C :=
  pb_Precategory_equivalence C f (is_split_surjective_of_is_retraction f)

  definition is_isomorphism_pb_Precategory_functor [constructor] {A : Type} (C : Precategory)
    (f : A ≃ C) : is_isomorphism (pb_Precategory_functor C f) :=
  (fully_faithful_pb_Precategory_functor C f, to_is_equiv f)

  definition pb_Precategory_isomorphism [constructor] {A : Type} (C : Precategory) (f : A ≃ C) :
    pb_Precategory C f ≅c C :=
  isomorphism.mk _ (is_isomorphism_pb_Precategory_functor C f)

end category

namespace chain_complex
  open fin
  definition is_contr_homotopy_group_fiber {A B : pType.{u}} {f : A →* B} {n : ℕ}
    (H1 : is_embedding (π→[n] f)) (H2 : is_surjective (π→g[n+1] f)) : is_contr (π[n] (pfiber f)) :=
  begin
    apply @is_contr_of_is_embedding_of_is_surjective +3ℕ (LES_of_homotopy_groups f) (n, 0),
    exact is_exact_LES_of_homotopy_groups f (n, 1), exact H1, exact H2
  end

  definition is_contr_homotopy_group_fiber_of_is_equiv {A B : pType.{u}} {f : A →* B} {n : ℕ}
    (H1 : is_equiv (π→[n] f)) (H2 : is_equiv (π→g[n+1] f)) : is_contr (π[n] (pfiber f)) :=
  is_contr_homotopy_group_fiber (is_embedding_of_is_equiv _) (is_surjective_of_is_equiv _)

end chain_complex
