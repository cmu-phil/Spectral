-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2 homotopy.cofiber homotopy.wedge hit.prop_trunc hit.set_quotient eq2 types.pointed2

open eq nat int susp pointed sigma is_equiv equiv fiber algebra trunc pi group
     is_trunc function unit prod bool

attribute pType.sigma_char sigma_pi_equiv_pi_sigma sigma.coind_unc [constructor]
attribute ap1_gen [unfold 8 9 10]
attribute ap010 [unfold 7]
attribute tro_invo_tro [unfold 9] -- TODO: move
  -- TODO: homotopy_of_eq and apd10 should be the same
  -- TODO: there is also apd10_eq_of_homotopy in both pi and eq(?)



namespace algebra

variables {A : Type} [add_ab_inf_group A]
definition add_sub_cancel_middle (a b : A) : a + (b - a) = b :=
!add.comm ⬝ !sub_add_cancel

end algebra

namespace eq

definition homotopy.symm_symm {A : Type} {P : A → Type} {f g : Πx, P x} (H : f ~ g) :
  H⁻¹ʰᵗʸ⁻¹ʰᵗʸ = H :=
begin apply eq_of_homotopy, intro x, apply inv_inv end

  definition apd10_prepostcompose_nondep {A B C D : Type} (h : C → D) {g g' : B → C} (p : g = g')
    (f : A → B) (a : A) : apd10 (ap (λg a, h (g (f a))) p) a = ap h (apd10 p (f a)) :=
  begin induction p, reflexivity end

  definition apd10_prepostcompose {A B : Type} {C : B → Type} {D : A → Type}
    (f : A → B) (h : Πa, C (f a) → D a) {g g' : Πb, C b}
    (p : g = g') (a : A) :
    apd10 (ap (λg a, h a (g (f a))) p) a = ap (h a) (apd10 p (f a)) :=
  begin induction p, reflexivity end

  definition eq.rec_to {A : Type} {a₀ : A} {P : Π⦃a₁⦄, a₀ = a₁ → Type}
    {a₁ : A} (p₀ : a₀ = a₁) (H : P p₀) ⦃a₂ : A⦄ (p : a₀ = a₂) : P p :=
  begin
    induction p₀, induction p, exact H
  end

  definition eq.rec_to2 {A : Type} {P : Π⦃a₀ a₁⦄, a₀ = a₁ → Type}
    {a₀ a₀' a₁' : A} (p' : a₀' = a₁') (p₀ : a₀ = a₀') (H : P p') ⦃a₁ : A⦄ (p : a₀ = a₁) : P p :=
  begin
   induction p₀, induction p', induction p, exact H
  end

  definition eq.rec_right_inv {A : Type} (f : A ≃ A) {P : Π⦃a₀ a₁⦄, f a₀ = a₁ → Type}
    (H : Πa, P (right_inv f a)) ⦃a₀ a₁ : A⦄ (p : f a₀ = a₁) : P p :=
  begin
    revert a₀ p, refine equiv_rect f⁻¹ᵉ _ _,
    intro a₀ p, exact eq.rec_to (right_inv f a₀) (H a₀) p,
  end

  definition eq.rec_equiv {A B : Type} {a₀ : A} (f : A ≃ B) {P : Π{a₁}, f a₀ = f a₁ → Type}
    (H : P (idpath (f a₀))) ⦃a₁ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    assert qr : Σ(q : a₀ = a₁), ap f q = p,
    { exact ⟨eq_of_fn_eq_fn f p, ap_eq_of_fn_eq_fn' f p⟩ },
    cases qr with q r, apply transport P r, induction q, exact H
  end

  definition eq.rec_equiv_symm {A B : Type} {a₁ : A} (f : A ≃ B) {P : Π{a₀}, f a₀ = f a₁ → Type}
    (H : P (idpath (f a₁))) ⦃a₀ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    assert qr : Σ(q : a₀ = a₁), ap f q = p,
    { exact ⟨eq_of_fn_eq_fn f p, ap_eq_of_fn_eq_fn' f p⟩ },
    cases qr with q r, apply transport P r, induction q, exact H
  end

  definition eq.rec_equiv_to_same {A B : Type} {a₀ : A} (f : A ≃ B) {P : Π{a₁}, f a₀ = f a₁ → Type}
    ⦃a₁' : A⦄ (p' : f a₀ = f a₁') (H : P p') ⦃a₁ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    revert a₁' p' H a₁ p,
    refine eq.rec_equiv f _,
    exact eq.rec_equiv f
  end

  definition eq.rec_equiv_to {A A' B : Type} {a₀ : A} (f : A ≃ B) (g : A' ≃ B)
    {P : Π{a₁}, f a₀ = g a₁ → Type}
    ⦃a₁' : A'⦄ (p' : f a₀ = g a₁') (H : P p') ⦃a₁ : A'⦄ (p : f a₀ = g a₁) : P p :=
  begin
    assert qr : Σ(q : g⁻¹ (f a₀) = a₁), (right_inv g (f a₀))⁻¹ ⬝ ap g q = p,
    { exact ⟨eq_of_fn_eq_fn g (right_inv g (f a₀) ⬝ p),
             whisker_left _ (ap_eq_of_fn_eq_fn' g _) ⬝ !inv_con_cancel_left⟩ },
    assert q'r' : Σ(q' : g⁻¹ (f a₀) = a₁'), (right_inv g (f a₀))⁻¹ ⬝ ap g q' = p',
    { exact ⟨eq_of_fn_eq_fn g (right_inv g (f a₀) ⬝ p'),
             whisker_left _ (ap_eq_of_fn_eq_fn' g _) ⬝ !inv_con_cancel_left⟩ },
    induction qr with q r, induction q'r' with q' r',
    induction q, induction q',
    induction r, induction r',
    exact H
  end

  definition eq.rec_grading {A A' B : Type} {a : A} (f : A ≃ B) (g : A' ≃ B)
    {P : Π{b}, f a = b → Type}
    {a' : A'} (p' : f a = g a') (H : P p') ⦃b : B⦄ (p : f a = b) : P p :=
  begin
    revert b p, refine equiv_rect g _ _,
    exact eq.rec_equiv_to f g p' H
  end

  definition eq.rec_grading_unbased {A B B' C : Type} (f : A ≃ B) (g : B ≃ C) (h : B' ≃ C)
    {P : Π{b c}, g b = c → Type}
    {a' : A} {b' : B'} (p' : g (f a') = h b') (H : P p') ⦃b : B⦄ ⦃c : C⦄ (q : f a' = b)
    (p : g b = c) : P p :=
  begin
    induction q, exact eq.rec_grading (f ⬝e g) h p' H p
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

  lemma homotopy_group_isomorphism_of_ptrunc_pequiv {A B : Type*}
    (n k : ℕ) (H : n+1 ≤[ℕ] k) (f : ptrunc k A ≃* ptrunc k B) : πg[n+1] A ≃g πg[n+1] B :=
  (ghomotopy_group_ptrunc_of_le H A)⁻¹ᵍ ⬝g
  homotopy_group_isomorphism_of_pequiv n f ⬝g
  ghomotopy_group_ptrunc_of_le H B

definition equiv_pathover2 {A : Type} {a a' : A} (p : a = a')
  {B : A → Type} {C : A → Type} (f : B a ≃ C a) (g : B a' ≃ C a')
  (r : to_fun f =[p] to_fun g) : f =[p] g :=
begin
  fapply pathover_of_fn_pathover_fn,
  { intro a, apply equiv.sigma_char },
  { apply sigma_pathover _ _ _ r, apply is_prop.elimo }
end

definition equiv_pathover_inv {A : Type} {a a' : A} (p : a = a')
  {B : A → Type} {C : A → Type} (f : B a ≃ C a) (g : B a' ≃ C a')
  (r : to_inv f =[p] to_inv g) : f =[p] g :=
begin
  /- this proof is a bit weird, but it works -/
  apply equiv_pathover2,
  change f⁻¹ᶠ⁻¹ᶠ =[p] g⁻¹ᶠ⁻¹ᶠ,
  apply apo (λ(a: A) (h : C a ≃ B a), h⁻¹ᶠ),
  apply equiv_pathover2,
  exact r
end

definition transport_lemma {A : Type} {C : A → Type} {g₁ : A → A}
  {x y : A} (p : x = y) (f : Π⦃x⦄, C x → C (g₁ x)) (z : C x) :
  transport C (ap g₁ p)⁻¹ (f (transport C p z)) = f z :=
by induction p; reflexivity

definition transport_lemma2 {A : Type} {C : A → Type} {g₁ : A → A}
  {x y : A} (p : x = y) (f : Π⦃x⦄, C x → C (g₁ x)) (z : C x) :
  transport C (ap g₁ p) (f z) = f (transport C p z) :=
by induction p; reflexivity

definition eq_of_pathover_apo {A C : Type} {B : A → Type} {a a' : A} {b : B a} {b' : B a'}
  {p : a = a'} (g : Πa, B a → C) (q : b =[p] b') :
  eq_of_pathover (apo g q) = apd011 g p q :=
by induction q; reflexivity

  definition apd02 [unfold 8] {A : Type} {B : A → Type} (f : Πa, B a) {a a' : A} {p q : a = a'}
    (r : p = q) : change_path r (apd f p) = apd f q :=
  by induction r; reflexivity

  definition pathover_ap_cono {A A' : Type} {a₁ a₂ a₃ : A}
    {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} (B' : A' → Type) (f : A → A')
    {b₁ : B' (f a₁)} {b₂ : B' (f a₂)} {b₃ : B' (f a₃)}
    (q₁ : b₁ =[p₁] b₂) (q₂ : b₂ =[p₂] b₃) :
    pathover_ap B' f (q₁ ⬝o q₂) =
    change_path !ap_con⁻¹ (pathover_ap B' f q₁ ⬝o pathover_ap B' f q₂) :=
  by induction q₁; induction q₂; reflexivity

  definition concato_eq_eq {A : Type} {B : A → Type} {a₁ a₂ : A} {p₁ : a₁ = a₂}
    {b₁ : B a₁} {b₂ b₂' : B a₂} (r : b₁ =[p₁] b₂) (q : b₂ = b₂') :
    r ⬝op q = r ⬝o pathover_idp_of_eq q :=
  by induction q; reflexivity

definition ap_apd0111 {A₁ A₂ A₃ : Type} {B : A₁ → Type} {C : Π⦃a⦄, B a → Type} {a a₂ : A₁}
  {b : B a} {b₂ : B a₂} {c : C b} {c₂ : C b₂}
  (g : A₂ → A₃) (f : Πa b, C b → A₂) (Ha : a = a₂) (Hb : b =[Ha] b₂)
    (Hc : c =[apd011 C Ha Hb] c₂) :
  ap g (apd0111 f Ha Hb Hc) = apd0111 (λa b c, (g (f a b c))) Ha Hb Hc :=
by induction Hb; induction Hc using idp_rec_on; reflexivity

section squareover

  variables {A A' : Type} {B : A → Type}
            {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/
            {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁} {s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁}
            {s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃} {s₃₃ : square p₃₂ p₃₄ p₂₃ p₄₃}

            {b : B a}
            {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₄₀ : B a₄₀}
            {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₄₂ : B a₄₂}
            {b₀₄ : B a₀₄} {b₂₄ : B a₂₄} {b₄₄ : B a₄₄}
            /-b₀₀-/ {q₁₀ : b₀₀ =[p₁₀] b₂₀} /-b₂₀-/ {q₃₀ : b₂₀ =[p₃₀] b₄₀} /-b₄₀-/
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ {q₃₂ : b₂₂ =[p₃₂] b₄₂} /-b₄₂-/
            /-b₀₄-/ {q₁₄ : b₀₄ =[p₁₄] b₂₄} /-b₂₄-/ {q₃₄ : b₂₄ =[p₃₄] b₄₄} /-b₄₄-/
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} /-t₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂} /-t₃₁-/ {q₄₁ : b₄₀ =[p₄₁] b₄₂}
   {q₀₃ : b₀₂ =[p₀₃] b₀₄} /-t₁₃-/ {q₂₃ : b₂₂ =[p₂₃] b₂₄} /-t₃₃-/ {q₄₃ : b₄₂ =[p₄₃] b₄₄}

  definition move_right_of_top_over {p : a₀₀ = a} {p' : a = a₂₀}
    {s : square p p₁₂ p₀₁ (p' ⬝ p₂₁)} {q : b₀₀ =[p] b} {q' : b =[p'] b₂₀}
    (t : squareover B (move_top_of_right s) (q ⬝o q') q₁₂ q₀₁ q₂₁) :
    squareover B s q q₁₂ q₀₁ (q' ⬝o q₂₁) :=
  begin induction q', induction q, induction q₂₁, exact t end

  /- TODO: replace the version in the library by this -/
  definition hconcato_pathover' {p : a₂₀ = a₂₂} {sp : p = p₂₁} {s : square p₁₀ p₁₂ p₀₁ p}
    {q : b₂₀ =[p] b₂₂} (t₁₁ : squareover B (s ⬝hp sp) q₁₀ q₁₂ q₀₁ q₂₁)
    (r : change_path sp q = q₂₁) : squareover B s q₁₀ q₁₂ q₀₁ q :=
  by induction sp; induction r; exact t₁₁

  variables (s₁₁ q₀₁ q₁₀ q₂₁ q₁₂)
  definition squareover_fill_t : Σ (q : b₀₀ =[p₁₀] b₂₀), squareover B s₁₁ q q₁₂ q₀₁ q₂₁ :=
  begin
    induction s₁₁, induction q₀₁ using idp_rec_on, induction q₂₁ using idp_rec_on,
    induction q₁₂ using idp_rec_on, exact ⟨idpo, idso⟩
  end

  definition squareover_fill_b : Σ (q : b₀₂ =[p₁₂] b₂₂), squareover B s₁₁ q₁₀ q q₀₁ q₂₁ :=
  begin
    induction s₁₁, induction q₀₁ using idp_rec_on, induction q₂₁ using idp_rec_on,
    induction q₁₀ using idp_rec_on, exact ⟨idpo, idso⟩
  end

  definition squareover_fill_l : Σ (q : b₀₀ =[p₀₁] b₀₂), squareover B s₁₁ q₁₀ q₁₂ q q₂₁ :=
  begin
    induction s₁₁, induction q₁₀ using idp_rec_on, induction q₂₁ using idp_rec_on,
    induction q₁₂ using idp_rec_on, exact ⟨idpo, idso⟩
  end

  definition squareover_fill_r : Σ (q : b₂₀ =[p₂₁] b₂₂) , squareover B s₁₁ q₁₀ q₁₂ q₀₁ q :=
  begin
    induction s₁₁, induction q₀₁ using idp_rec_on, induction q₁₀ using idp_rec_on,
    induction q₁₂ using idp_rec_on, exact ⟨idpo, idso⟩
  end


end squareover

/- move this to types.eq, and replace the proof there -/
  section
    parameters {A : Type} (a₀ : A) (code : A → Type) (H : is_contr (Σa, code a))
      (c₀ : code a₀)
    include H c₀
    protected definition encode2 {a : A} (q : a₀ = a) : code a :=
    transport code q c₀

    protected definition decode2' {a : A} (c : code a) : a₀ = a :=
    have ⟨a₀, c₀⟩ = ⟨a, c⟩ :> Σa, code a, from !is_prop.elim,
    this..1

    protected definition decode2 {a : A} (c : code a) : a₀ = a :=
    (decode2' c₀)⁻¹ ⬝ decode2' c

    open sigma.ops
    definition total_space_method2 (a : A) : (a₀ = a) ≃ code a :=
    begin
      fapply equiv.MK,
      { exact encode2 },
      { exact decode2 },
      { intro c, unfold [encode2, decode2, decode2'],
        rewrite [is_prop_elim_self, ▸*, idp_con],
        apply tr_eq_of_pathover, apply eq_pr2 },
      { intro q, induction q, esimp, apply con.left_inv, },
    end
  end

definition total_space_method2_refl {A : Type} (a₀ : A) (code : A → Type) (H : is_contr (Σa, code a))
  (c₀ : code a₀) : total_space_method2 a₀ code H c₀ a₀ idp = c₀ :=
begin
  reflexivity
end

  section hsquare
  variables {A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type}
            {f₁₀ : A₀₀ → A₂₀} {f₃₀ : A₂₀ → A₄₀}
            {f₀₁ : A₀₀ → A₀₂} {f₂₁ : A₂₀ → A₂₂} {f₄₁ : A₄₀ → A₄₂}
            {f₁₂ : A₀₂ → A₂₂} {f₃₂ : A₂₂ → A₄₂}
            {f₀₃ : A₀₂ → A₀₄} {f₂₃ : A₂₂ → A₂₄} {f₄₃ : A₄₂ → A₄₄}
            {f₁₄ : A₀₄ → A₂₄} {f₃₄ : A₂₄ → A₄₄}

  definition trunc_functor_hsquare (n : ℕ₋₂) (h : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
    hsquare (trunc_functor n f₁₀) (trunc_functor n f₁₂)
            (trunc_functor n f₀₁) (trunc_functor n f₂₁) :=
  λa, !trunc_functor_compose⁻¹ ⬝ trunc_functor_homotopy n h a ⬝ !trunc_functor_compose

  attribute hhconcat hvconcat [unfold_full]

  definition rfl_hhconcat (q : hsquare f₃₀ f₃₂ f₂₁ f₄₁) : homotopy.rfl ⬝htyh q ~ q :=
  homotopy.rfl

  definition hhconcat_rfl (q : hsquare f₃₀ f₃₂ f₂₁ f₄₁) : q ⬝htyh homotopy.rfl ~ q :=
  λx, !idp_con ⬝ ap_id (q x)

  definition rfl_hvconcat (q : hsquare f₃₀ f₃₂ f₂₁ f₄₁) : homotopy.rfl ⬝htyv q ~ q :=
  λx, !idp_con

  definition hvconcat_rfl (q : hsquare f₃₀ f₃₂ f₂₁ f₄₁) : q ⬝htyv homotopy.rfl ~ q :=
  λx, !ap_id

  end hsquare
  definition homotopy_group_succ_in_natural (n : ℕ) {A B : Type*} (f : A →* B) :
    hsquare (homotopy_group_succ_in A n) (homotopy_group_succ_in B n) (π→[n+1] f) (π→[n] (Ω→ f)) :=
  trunc_functor_hsquare _ (loopn_succ_in_natural n f)⁻¹*

  definition homotopy2.refl {A} {B : A → Type} {C : Π⦃a⦄, B a → Type} (f : Πa (b : B a), C b) :
    f ~2 f :=
  λa b, idp

  definition homotopy2.rfl [refl] {A} {B : A → Type} {C : Π⦃a⦄, B a → Type}
    {f : Πa (b : B a), C b} : f ~2 f :=
  λa b, idp

  definition homotopy3.refl {A} {B : A → Type} {C : Πa, B a → Type}
    {D : Π⦃a⦄ ⦃b : B a⦄, C a b → Type} (f : Πa b (c : C a b), D c) : f ~3 f :=
  λa b c, idp

  definition homotopy3.rfl {A} {B : A → Type} {C : Πa, B a → Type}
    {D : Π⦃a⦄ ⦃b : B a⦄, C a b → Type} {f : Πa b (c : C a b), D c} : f ~3 f :=
  λa b c, idp

  definition eq_tr_of_pathover_con_tr_eq_of_pathover {A : Type} {B : A → Type}
    {a₁ a₂ : A} (p : a₁ = a₂) {b₁ : B a₁} {b₂ : B a₂} (q : b₁ =[p] b₂) :
    eq_tr_of_pathover q ⬝ tr_eq_of_pathover q⁻¹ᵒ = idp :=
  by induction q; reflexivity

end eq open eq

namespace nat

  protected definition rec_down (P : ℕ → Type) (s : ℕ) (H0 : P s) (Hs : Πn, P (n+1) → P n) : P 0 :=
  begin
    induction s with s IH,
    { exact H0 },
    { exact IH (Hs s H0) }
  end
/-  have Hp : Πn, P n → P (pred n),
  begin
    intro n p, cases n with n,
    { exact p },
    { exact Hs n p }
  end,
  have H : Πn, P (s - n),
  begin
    intro n, induction n with n p,
    { exact H0 },
    { exact Hp (s - n) p }
  end,
  transport P (nat.sub_self s) (H s)-/

  /- this generalizes iterate_commute -/
  definition iterate_hsquare {A B : Type} {f : A → A} {g : B → B}
    (h : A → B) (p : hsquare f g h h) (n : ℕ) : hsquare (f^[n]) (g^[n]) h h :=
  begin
    induction n with n q,
      exact homotopy.rfl,
      exact q ⬝htyh p
  end

definition iterate_equiv2 {A : Type} {C : A → Type} (f : A → A) (h : Πa, C a ≃ C (f a))
  (k : ℕ) (a : A) : C a ≃ C (f^[k] a) :=
begin induction k with k IH, reflexivity, exact IH ⬝e h (f^[k] a) end



  /- replace proof of le_of_succ_le by this -/
  definition le_step_left {n m : ℕ} (H : succ n ≤ m) : n ≤ m :=
  by induction H with H m H'; exact le_succ n; exact le.step H'

  /- TODO: make proof of le_succ_of_le simpler -/

  definition nat.add_le_add_left2 {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
  by induction H with m H H₂; reflexivity; exact le.step H₂

end nat


namespace trunc_index
  open is_conn nat trunc is_trunc
  lemma minus_two_add_plus_two (n : ℕ₋₂) : -2+2+n = n :=
  by induction n with n p; reflexivity; exact ap succ p

  protected definition of_nat_monotone {n k : ℕ} : n ≤ k → of_nat n ≤ of_nat k :=
  begin
    intro H, induction H with k H K,
    { apply le.tr_refl },
    { apply le.step K }
  end

  lemma add_plus_two_comm (n k : ℕ₋₂) : n +2+ k = k +2+ n :=
  begin
    induction n with n IH,
    { exact minus_two_add_plus_two k },
    { exact !succ_add_plus_two ⬝ ap succ IH}
  end

end trunc_index

namespace int

  private definition maxm2_le.lemma₁ {n k : ℕ} : n+(1:int) + -[1+ k] ≤ n :=
  le.intro (
    calc n + 1 + -[1+ k] + k
      = n + 1 + (-(k + 1)) + k : by reflexivity
  ... = n + 1 + (- 1 - k) + k    : by krewrite (neg_add_rev k 1)
  ... = n + 1 + (- 1 - k + k)    : add.assoc
  ... = n + 1 + (- 1 + -k + k)   : by reflexivity
  ... = n + 1 + (- 1 + (-k + k)) : add.assoc
  ... = n + 1 + (- 1 + 0)        : add.left_inv
  ... = n + (1 + (- 1 + 0))      : add.assoc
  ... = n                       : int.add_zero)

  private definition maxm2_le.lemma₂ {n : ℕ} {k : ℤ} : -[1+ n] + 1 + k ≤ k :=
  le.intro (
    calc -[1+ n] + 1 + k + n
      = - (n + 1) + 1 + k + n : by reflexivity
  ... = -n - 1 + 1 + k + n    : by rewrite (neg_add n 1)
  ... = -n + (- 1 + 1) + k + n : by krewrite (int.add_assoc (-n) (- 1) 1)
  ... = -n + 0 + k + n        : add.left_inv 1
  ... = -n + k + n            : int.add_zero
  ... = k + -n + n            : int.add_comm
  ... = k + (-n + n)          : int.add_assoc
  ... = k + 0                 : add.left_inv n
  ... = k                     : int.add_zero)

  open trunc_index
  /-
    The function from integers to truncation indices which sends
    positive numbers to themselves, and negative numbers to negative
    2. In particular -1 is sent to -2, but since we only work with
    pointed types, that doesn't matter for us -/
  definition maxm2 [unfold 1] : ℤ → ℕ₋₂ :=
  λ n, int.cases_on n trunc_index.of_nat (λk, -2)

  -- we also need the max -1 - function
  definition maxm1 [unfold 1] : ℤ → ℕ₋₂ :=
  λ n, int.cases_on n trunc_index.of_nat (λk, -1)

  definition maxm2_le_maxm1 (n : ℤ) : maxm2 n ≤ maxm1 n :=
  begin
    induction n with n n,
    { exact le.tr_refl n },
    { exact minus_two_le -1 }
  end

  -- the is maxm1 minus 1
  definition maxm1m1 [unfold 1] : ℤ → ℕ₋₂ :=
  λ n, int.cases_on n (λ k, k.-1) (λ k, -2)

  definition maxm1_eq_succ (n : ℤ) : maxm1 n = (maxm1m1 n).+1 :=
  begin
    induction n with n n,
    { reflexivity },
    { reflexivity }
  end

  definition maxm2_le_maxm0 (n : ℤ) : maxm2 n ≤ max0 n :=
  begin
    induction n with n n,
    { exact le.tr_refl n },
    { exact minus_two_le 0 }
  end

  definition max0_le_of_le {n : ℤ} {m : ℕ} (H : n ≤ of_nat m)
    : nat.le (max0 n) m :=
  begin
    induction n with n n,
    { exact le_of_of_nat_le_of_nat H },
    { exact nat.zero_le m }
  end

  definition not_neg_succ_le_of_nat {n m : ℕ} : ¬m ≤ -[1+n] :=
  by cases m: exact id

  definition maxm2_monotone {n m : ℤ} (H : n ≤ m) : maxm2 n ≤ maxm2 m :=
  begin
    induction n with n n,
    { induction m with m m,
      { apply of_nat_le_of_nat, exact le_of_of_nat_le_of_nat H },
      { exfalso, exact not_neg_succ_le_of_nat H }},
    { apply minus_two_le }
  end

  definition sub_nat_le (n : ℤ) (m : ℕ) : n - m ≤ n :=
  le.intro !sub_add_cancel

  definition sub_nat_lt (n : ℤ) (m : ℕ) : n - m < n + 1 :=
  add_le_add_right (sub_nat_le n m) 1

  definition sub_one_le (n : ℤ) : n - 1 ≤ n :=
  sub_nat_le n 1

  definition le_add_nat (n : ℤ) (m : ℕ) : n ≤ n + m :=
  le.intro rfl

  definition le_add_one (n : ℤ) : n ≤ n + 1:=
  le_add_nat n 1

  open trunc_index

  definition maxm2_le (n k : ℤ) : maxm2 (n+1+k) ≤ (maxm1m1 n).+1+2+(maxm1m1 k) :=
  begin
    rewrite [-(maxm1_eq_succ n)],
    induction n with n n,
    { induction k with k k,
      { induction k with k IH,
        { apply le.tr_refl },
        { exact succ_le_succ IH } },
      { exact trunc_index.le_trans (maxm2_monotone maxm2_le.lemma₁)
                                   (maxm2_le_maxm1 n) } },
    { krewrite (add_plus_two_comm -1 (maxm1m1 k)),
      rewrite [-(maxm1_eq_succ k)],
      exact trunc_index.le_trans (maxm2_monotone maxm2_le.lemma₂)
                                 (maxm2_le_maxm1 k) }
  end

end int open int

namespace pmap

  /- rename: pmap_eta in namespace pointed -/
  definition eta {A B : Type*} (f : A →* B) : pmap.mk f (respect_pt f) = f :=
  begin induction f, reflexivity end

end pmap

namespace lift

  definition is_trunc_plift [instance] [priority 1450] (A : Type*) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc n (plift A) :=
  is_trunc_lift A n

end lift

namespace trunc
  open trunc_index
  definition trunc_index_equiv_nat [constructor] : ℕ₋₂ ≃ ℕ :=
  equiv.MK add_two sub_two add_two_sub_two sub_two_add_two

  definition is_set_trunc_index [instance] : is_set ℕ₋₂ :=
  is_trunc_equiv_closed_rev 0 trunc_index_equiv_nat

  definition is_contr_ptrunc_minus_one (A : Type*) : is_contr (ptrunc -1 A) :=
  is_contr_of_inhabited_prop pt

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

  definition ptrunc_elim_ptr_phomotopy_pid (n : ℕ₋₂) (A : Type*):
    ptrunc.elim n (ptr n A) ~* pid (ptrunc n A) :=
  begin
    fapply phomotopy.mk,
    { intro a, induction a with a, reflexivity },
    { apply idp_con }
  end

  definition is_trunc_ptrunc_of_is_trunc [instance] [priority 500] (A : Type*)
    (n m : ℕ₋₂) [H : is_trunc n A] : is_trunc n (ptrunc m A) :=
  is_trunc_trunc_of_is_trunc A n m

  definition ptrunc_pequiv_ptrunc_of_is_trunc {n m k : ℕ₋₂} {A : Type*}
    (H1 : n ≤ m) (H2 : n ≤ k) (H : is_trunc n A) : ptrunc m A ≃* ptrunc k A :=
  have is_trunc m A, from is_trunc_of_le A H1,
  have is_trunc k A, from is_trunc_of_le A H2,
  pequiv.MK (ptrunc.elim _ (ptr k A)) (ptrunc.elim _ (ptr m A))
    abstract begin
      refine !ptrunc_elim_pcompose⁻¹* ⬝* _,
      exact ptrunc_elim_phomotopy _ !ptrunc_elim_ptr ⬝* !ptrunc_elim_ptr_phomotopy_pid,
    end end
    abstract begin
      refine !ptrunc_elim_pcompose⁻¹* ⬝* _,
      exact ptrunc_elim_phomotopy _ !ptrunc_elim_ptr ⬝* !ptrunc_elim_ptr_phomotopy_pid,
    end end

  definition ptrunc_change_index {k l : ℕ₋₂} (p : k = l) (X : Type*)
    : ptrunc k X ≃* ptrunc l X :=
  pequiv_ap (λ n, ptrunc n X) p

  definition ptrunc_functor_le {k l : ℕ₋₂} (p : l ≤ k) (X : Type*)
    : ptrunc k X →* ptrunc l X :=
  have is_trunc k (ptrunc l X), from is_trunc_of_le _ p,
  ptrunc.elim _ (ptr l X)

  definition trunc_index.pred [unfold 1] (n : ℕ₋₂) : ℕ₋₂ :=
  begin cases n with n, exact -2, exact n end

  /- A more general version of ptrunc_elim_phomotopy, where the proofs of truncatedness might be different -/
  definition ptrunc_elim_phomotopy2 [constructor] (k : ℕ₋₂) {A B : Type*} {f g : A →* B} (H₁ : is_trunc k B)
    (H₂ : is_trunc k B) (p : f ~* g) : @ptrunc.elim k A B H₁ f ~* @ptrunc.elim k A B H₂ g :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with a, exact p a },
    { exact to_homotopy_pt p }
  end

end trunc

namespace is_trunc

  open trunc_index is_conn

  definition is_trunc_of_eq {n m : ℕ₋₂} (p : n = m) {A : Type} (H : is_trunc n A) : is_trunc m A :=
  transport (λk, is_trunc k A) p H

  definition is_trunc_succ_succ_of_is_trunc_loop (n : ℕ₋₂) (A : Type*) (H : is_trunc (n.+1) (Ω A))
    (H2 : is_conn 0 A) : is_trunc (n.+2) A :=
  begin
    apply is_trunc_succ_of_is_trunc_loop, apply minus_one_le_succ,
    refine is_conn.elim -1 _ _, exact H
  end

  lemma is_trunc_of_is_trunc_loopn (m n : ℕ) (A : Type*) (H : is_trunc n (Ω[m] A))
    (H2 : is_conn m A) : is_trunc (m + n) A :=
  begin
    revert A H H2; induction m with m IH: intro A H H2,
    { rewrite [nat.zero_add], exact H },
    rewrite [succ_add],
    apply is_trunc_succ_succ_of_is_trunc_loop,
    { apply IH,
      { apply is_trunc_equiv_closed _ !loopn_succ_in },
      apply is_conn_loop },
    exact is_conn_of_le _ (zero_le_of_nat (succ m))
  end

  lemma is_trunc_of_is_set_loopn (m : ℕ) (A : Type*) (H : is_set (Ω[m] A))
    (H2 : is_conn m A) : is_trunc m A :=
  is_trunc_of_is_trunc_loopn m 0 A H H2

end is_trunc
namespace sigma
  open sigma.ops

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
    apply isomorphism_of_equiv (equiv.mk (trunc_functor 0 f) (is_equiv_trunc_functor 0 f)), intros x x',
    induction x with a, induction x' with a', apply ap tr, exact h a a'
  end

end group open group

namespace fiber

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

end fiber

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

end function open function

namespace is_conn

  open unit trunc_index nat is_trunc pointed.ops

  definition is_conn_zero {A : Type} (a₀ : trunc 0 A) (p : Πa a' : A, ∥ a = a' ∥) : is_conn 0 A :=
  is_conn_succ_intro a₀ (λa a', is_conn_minus_one _ (p a a'))

  definition is_conn_zero_pointed {A : Type*} (p : Πa a' : A, ∥ a = a' ∥) : is_conn 0 A :=
  is_conn_zero (tr pt) p

  definition is_conn_fiber (n : ℕ₋₂) {A B : Type} (f : A → B) (b : B) [is_conn n A] [is_conn (n.+1) B] :
    is_conn n (fiber f b) :=
  is_conn_equiv_closed_rev _ !fiber.sigma_char _

  definition is_conn_fun_compose {n : ℕ₋₂} {A B C : Type} (g : B → C) (f : A → B)
    (H : is_conn_fun n g) (K : is_conn_fun n f) : is_conn_fun n (g ∘ f) :=
  sorry

end is_conn

namespace misc
  open is_conn

  open sigma.ops pointed trunc_index

  definition component [constructor] (A : Type*) : Type* :=
  pType.mk (Σ(a : A), merely (pt = a)) ⟨pt, tr idp⟩

  lemma is_conn_component [instance] (A : Type*) : is_conn 0 (component A) :=
  is_contr.mk (tr pt)
    begin
      intro x, induction x with x, induction x with a p, induction p with p, induction p, reflexivity
    end

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
  --   apply eq_of_fn_eq_fn !sphere_pmap_pequiv,
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

notation `⅀→`:(max+5) := susp_functor
notation `⅀⇒`:(max+5) := susp_functor_phomotopy
notation `Ω⇒`:(max+5) := ap1_phomotopy

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
