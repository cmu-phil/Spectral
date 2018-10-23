-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2 homotopy.cofiber homotopy.wedge hit.prop_trunc hit.set_quotient eq2 types.pointed2 algebra.graph algebra.category.functor.equivalence

open eq nat int susp pointed sigma is_equiv equiv fiber algebra trunc pi group
     is_trunc function unit prod bool

universe variable u

  definition AddAbGroup.struct2 [instance] (G : AddAbGroup) :
    add_ab_group (algebra._trans_of_Group_of_AbGroup_2 G) :=
  AddAbGroup.struct G

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

  open option sum
  definition option_equiv_sum (A : Type) : option A ≃ A ⊎ unit :=
  begin
    fapply equiv.MK,
    { intro z, induction z with a,
      { exact inr star },
      { exact inl a } },
    { intro z, induction z with a b,
      { exact some a },
      { exact none } },
    { intro z, induction z with a b,
      { reflexivity },
      { induction b, reflexivity } },
    { intro z, induction z with a, all_goals reflexivity }
  end

  theorem is_trunc_add_point [instance] (n : ℕ₋₂) (A : Type) [HA : is_trunc (n.+2) A]
    : is_trunc (n.+2) A₊ :=
  begin
    apply is_trunc_equiv_closed_rev _ (option_equiv_sum A),
    apply is_trunc_sum
  end

end pointed open pointed

namespace trunc
  open trunc_index sigma.ops

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


  definition sigma_equiv_of_is_embedding_left_fun [constructor] {X Y : Type} {P : Y → Type}
    {f : X → Y} (H : Πy, P y → fiber f y) (v : Σy, P y) : Σx, P (f x) :=
  ⟨fiber.point (H v.1 v.2), transport P (point_eq (H v.1 v.2))⁻¹ v.2⟩

  definition sigma_equiv_of_is_embedding_left [constructor] {X Y : Type} {P : Y → Type}
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
  sigma_equiv_of_is_embedding_left f Hf _ H ⬝e sigma_equiv_of_is_contr_right _ _

end sigma open sigma

namespace group


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


  -- definition interchange (G : AbGroup) (a b c d : G) : (a * b) * (c * d) = (a * c) * (b * d) :=
  -- mul.comm4 a b c d

  open option
  definition add_point_AbGroup [unfold 3] {X : Type} (G : X → AbGroup) : X₊ → AbGroup
  | (some x) := G x
  | none     := trivial_ab_group_lift

  -- definition trunc_isomorphism_of_equiv {A B : Type} [inf_group A] [inf_group B] (f : A ≃ B)
  --   (h : is_mul_hom f) :
  --   Group.mk (trunc 0 A) (group_trunc A) ≃g Group.mk (trunc 0 B) (group_trunc B) :=
  -- begin
  --   apply isomorphism_of_equiv (trunc_equiv_trunc 0 f), intros x x',
  --   induction x with a, induction x' with a', apply ap tr, exact h a a'
  -- end


end group open group

namespace fiber

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


end fiber open fiber

namespace function
  variables {A B : Type} {f f' : A → B}
  open is_conn sigma.ops

  definition homotopy_group_isomorphism_of_is_embedding (n : ℕ) [H : is_succ n] {A B : Type*}
    (f : A →* B) [H2 : is_embedding f] : πg[n] A ≃g πg[n] B :=
  begin
    apply isomorphism.mk (homotopy_group_homomorphism n f),
    induction H with n,
    apply is_equiv_of_equiv_of_homotopy
      (ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn_of_is_embedding (n+1) f)),
    exact sorry
  end

  definition merely_constant_pmap {A B : Type*} {f : A →* B} (H : merely_constant f) (a : A) :
    merely (f a = pt) :=
  tconcat (tconcat (H.2 a) (tinverse (H.2 pt))) (tr (respect_pt f))

  definition merely_constant_of_is_conn {A B : Type*} (f : A →* B) [is_conn 0 A] :
    merely_constant f :=
  ⟨pt, is_conn.elim -1 _ (tr (respect_pt f))⟩

end function open function

namespace is_conn

open unit trunc_index nat is_trunc pointed.ops sigma.ops prod.ops

-- definition is_conn_pfiber_of_equiv_on_homotopy_groups (n : ℕ) {A B : pType.{u}} (f : A →* B)
--   [H : is_conn 0 A]
--   (H1 : Πk, k ≤ n → is_equiv (π→[k] f))
--   (H2 : is_surjective (π→[succ n] f)) :
--   is_conn n (pfiber f) :=
-- _

-- definition is_conn_pelim [constructor] {k : ℕ} {X : Type*} (Y : Type*) (H : is_conn k X) :
--   (X →* connect k Y) ≃ (X →* Y) :=

end is_conn


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


namespace paths

variables {A : Type} {R : A → A → Type} {a₁ a₂ a₃ a₄ : A}

definition mem_equiv_Exists (l : R a₁ a₂) (p : paths R a₃ a₄) :
  mem l p ≃ Exists (λa a' r, ⟨a₁, a₂, l⟩ = ⟨a, a', r⟩) p :=
sorry

end paths
