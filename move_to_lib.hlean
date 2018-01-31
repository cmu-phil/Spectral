-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2 homotopy.cofiber homotopy.wedge hit.prop_trunc hit.set_quotient eq2 types.pointed2 algebra.graph

open eq nat int susp pointed sigma is_equiv equiv fiber algebra trunc pi group
     is_trunc function unit prod bool

attribute pType.sigma_char sigma_pi_equiv_pi_sigma sigma.coind_unc [constructor]
attribute ap1_gen [unfold 8 9 10]
attribute ap010 [unfold 7]
attribute tro_invo_tro [unfold 9] -- TODO: move
  -- TODO: homotopy_of_eq and apd10 should be the same
  -- TODO: there is also apd10_eq_of_homotopy in both pi and eq(?)
universe variable u


namespace algebra

variables {A : Type} [add_ab_inf_group A]
definition add_sub_cancel_middle (a b : A) : a + (b - a) = b :=
!add.comm ⬝ !sub_add_cancel

end algebra

namespace eq

  -- this should maybe replace whisker_left_idp and whisker_left_idp_con
  definition whisker_left_idp_square {A : Type} {a a' : A} {p q : a = a'} (r : p = q) :
    square (whisker_left idp r) r (idp_con p) (idp_con q) :=
  begin induction r, exact hrfl end

  definition ap_con_idp_left {A B : Type} (f : A → B) {a a' : A} (p : a = a') :
    square (ap_con f idp p) idp (ap02 f (idp_con p)) (idp_con (ap f p)) :=
  begin induction p, exact ids end

  definition pathover_tr_pathover_idp_of_eq {A : Type} {B : A → Type} {a a' : A} {b : B a} {b' : B a'} {p : a = a'}
    (q : b =[p] b') :
    pathover_tr p b ⬝o pathover_idp_of_eq (tr_eq_of_pathover q) = q :=
  begin induction q; reflexivity end

  -- rename pathover_of_tr_eq_idp
  definition pathover_of_tr_eq_idp' {A : Type} {B : A → Type} {a a₂ : A} (p : a = a₂) (b : B a) :
    pathover_of_tr_eq idp = pathover_tr p b :=
  by induction p; constructor

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

definition fundamental_group_isomorphism {X : Type*} {G : Group}
  (e : Ω X ≃ G) (hom_e : Πp q, e (p ⬝ q) = e p * e q) : π₁ X ≃g G :=
isomorphism_of_equiv (trunc_equiv_trunc 0 e ⬝e (trunc_equiv 0 G))
  begin intro p q, induction p with p, induction q with q, exact hom_e p q end

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

  definition rec_down_le (P : ℕ → Type) (s : ℕ) (H0 : Πn, s ≤ n → P n) (Hs : Πn, P (n+1) → P n)
    : Πn, P n :=
  begin
    induction s with s IH: intro n,
    { exact H0 n (zero_le n) },
    { apply IH, intro n' H, induction H with n' H IH2, apply Hs, exact H0 _ !le.refl,
      exact H0 _ (succ_le_succ H) }
  end

  definition rec_down_le_univ {P : ℕ → Type} {s : ℕ} {H0 : Π⦃n⦄, s ≤ n → P n}
    {Hs : Π⦃n⦄, P (n+1) → P n} (Q : Π⦃n⦄, P n → P (n + 1) → Type)
    (HQ0 : Πn (H : s ≤ n), Q (H0 H) (H0 (le.step H))) (HQs : Πn (p : P (n+1)), Q (Hs p) p) :
    Πn, Q (rec_down_le P s H0 Hs n) (rec_down_le P s H0 Hs (n + 1)) :=
  begin
    induction s with s IH: intro n,
    { apply HQ0 },
    { apply IH, intro n' H, induction H with n' H IH2,
      { apply HQs },
      { apply HQ0 }}
  end

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

  lemma sub_one_add_plus_two_sub_one (n m : ℕ) : n.-1 +2+ m.-1 = of_nat (n + m) :=
  begin
    induction m with m IH,
    { reflexivity },
    { exact ap succ IH }
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

  definition lift_functor2 {A B C : Type} (f : A → B → C) (x : lift A) (y : lift B) : lift C :=
  up (f (down x) (down y))

end lift

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
/- move to pointed -/
open sigma.ops
definition pType.sigma_char' [constructor] : pType.{u} ≃ Σ(X : Type.{u}), X :=
begin
  fapply equiv.MK,
  { intro X, exact ⟨X, pt⟩ },
  { intro X, exact pointed.MK X.1 X.2 },
  { intro x, induction x with X x, reflexivity },
  { intro x, induction x with X x, reflexivity },
end

definition ap_equiv_eq {X Y : Type} {e e' : X ≃ Y} (p : e ~ e') (x : X) :
  ap (λ(e : X ≃ Y), e x) (equiv_eq p) = p x :=
begin
  cases e with e He, cases e' with e' He', esimp at *, esimp [equiv_eq],
  refine homotopy.rec_on' p _, intro q, induction q, esimp [equiv_eq', equiv_mk_eq],
  assert H : He = He', apply is_prop.elim, induction H, rewrite [is_prop_elimo_self]
end

definition pequiv.sigma_char_equiv [constructor] (X Y : Type*) :
  (X ≃* Y) ≃ Σ(e : X ≃ Y), e pt = pt :=
begin
  fapply equiv.MK,
  { intro e, exact ⟨equiv_of_pequiv e, respect_pt e⟩ },
  { intro e, exact pequiv_of_equiv e.1 e.2 },
  { intro e, induction e with e p, fapply sigma_eq,
    apply equiv_eq, reflexivity, esimp,
    apply eq_pathover_constant_right, esimp,
    refine _ ⬝ph vrfl,
    apply ap_equiv_eq },
  { intro e, apply pequiv_eq, fapply phomotopy.mk, intro x, reflexivity,
    refine !idp_con ⬝ _, reflexivity },
end

definition pequiv.sigma_char_pmap [constructor] (X Y : Type*) :
  (X ≃* Y) ≃ Σ(f : X →* Y), is_equiv f :=
begin
  fapply equiv.MK,
  { intro e, exact ⟨ pequiv.to_pmap e , pequiv.to_is_equiv e ⟩ },
  { intro w, exact pequiv_of_pmap w.1 w.2 },
  { intro w, induction w with f p, fapply sigma_eq,
    { reflexivity }, { apply is_prop.elimo } },
  { intro e, apply pequiv_eq, fapply phomotopy.mk,
    { intro x, reflexivity },
    { refine !idp_con ⬝ _, reflexivity } }
end

definition pType_eq_equiv (X Y : Type*) : (X = Y) ≃ (X ≃* Y) :=
begin
  refine eq_equiv_fn_eq pType.sigma_char' X Y ⬝e !sigma_eq_equiv ⬝e _, esimp,
  transitivity Σ(p : X = Y), cast p pt = pt,
  apply sigma_equiv_sigma_right, intro p, apply pathover_equiv_tr_eq,
  transitivity Σ(e : X ≃ Y), e pt = pt,
  refine sigma_equiv_sigma (eq_equiv_equiv X Y) (λp, equiv.rfl),
  exact (pequiv.sigma_char_equiv X Y)⁻¹ᵉ
end

end pointed open pointed

namespace trunc
  open trunc_index sigma.ops

definition ptrunctype.sigma_char [constructor] (n : ℕ₋₂) :
  n-Type* ≃ Σ(X : Type*), is_trunc n X :=
equiv.MK (λX, ⟨ptrunctype.to_pType X, _⟩)
         (λX, ptrunctype.mk (carrier X.1) X.2 pt)
         begin intro X, induction X with X HX, induction X, reflexivity end
         begin intro X, induction X, reflexivity end

definition is_embedding_ptrunctype_to_pType (n : ℕ₋₂) : is_embedding (@ptrunctype.to_pType n) :=
begin
  intro X Y, fapply is_equiv_of_equiv_of_homotopy,
  { exact eq_equiv_fn_eq (ptrunctype.sigma_char n) _ _ ⬝e subtype_eq_equiv _ _ },
  intro p, induction p, reflexivity
end

definition ptrunctype_eq_equiv {n : ℕ₋₂} (X Y : n-Type*) : (X = Y) ≃ (X ≃* Y) :=
equiv.mk _ (is_embedding_ptrunctype_to_pType n X Y) ⬝e pType_eq_equiv X Y

/- replace trunc_trunc_equiv_left by this -/
definition trunc_trunc_equiv_left' [constructor] (A : Type) {n m : ℕ₋₂} (H : n ≤ m)
  : trunc n (trunc m A) ≃ trunc n A :=
begin
  note H2 := is_trunc_of_le (trunc n A) H,
  fapply equiv.MK,
  { intro x, induction x with x, induction x with x, exact tr x },
  { exact trunc_functor n tr },
  { intro x, induction x with x, reflexivity},
  { intro x, induction x with x, induction x with x, reflexivity}
end

definition is_equiv_ptrunc_functor_ptr [constructor] (A : Type*) {n m : ℕ₋₂} (H : n ≤ m)
  : is_equiv (ptrunc_functor n (ptr m A)) :=
to_is_equiv (trunc_trunc_equiv_left' A H)⁻¹ᵉ

definition Prop_eq {P Q : Prop} (H : P ↔ Q) : P = Q :=
tua (equiv_of_is_prop (iff.mp H) (iff.mpr H))

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

definition pmap_ptrunc_equiv [constructor] (n : ℕ₋₂) (A B : Type*) [H : is_trunc n B] :
  (ptrunc n A →* B) ≃ (A →* B) :=
begin
  fapply equiv.MK,
  { intro g, exact g ∘* ptr n A },
  { exact ptrunc.elim n },
  { intro f, apply eq_of_phomotopy, apply ptrunc_elim_ptr },
  { intro g, apply eq_of_phomotopy,
    exact ptrunc_elim_pcompose n g (ptr n A) ⬝* pwhisker_left g (ptrunc_elim_ptr_phomotopy_pid n A) ⬝*
      pcompose_pid g }
end

definition pmap_ptrunc_pequiv [constructor] (n : ℕ₋₂) (A B : Type*) [H : is_trunc n B] :
  ppmap (ptrunc n A) B ≃* ppmap A B :=
pequiv_of_equiv (pmap_ptrunc_equiv n A B) (eq_of_phomotopy (pconst_pcompose (ptr n A)))

definition loopn_ptrunc_pequiv_nat (n : ℕ) (k : ℕ) (A : Type*) :
  Ω[k] (ptrunc (n+k) A) ≃* ptrunc n (Ω[k] A) :=
loopn_pequiv_loopn k (ptrunc_change_index (of_nat_add_of_nat n k)⁻¹ A) ⬝e* loopn_ptrunc_pequiv n k A

end trunc open trunc

namespace is_trunc

  open trunc_index is_conn

  lemma is_trunc_loopn_nat (m n : ℕ) (A : Type*) [H : is_trunc (n + m) A] :
    is_trunc n (Ω[m] A) :=
  @is_trunc_loopn n m A (transport (λk, is_trunc k _) (of_nat_add_of_nat n m)⁻¹ H)

  lemma is_trunc_loop_nat (n : ℕ) (A : Type*) [H : is_trunc (n + 1) A] :
    is_trunc n (Ω A) :=
  is_trunc_loop A n

  definition is_trunc_of_eq {n m : ℕ₋₂} (p : n = m) {A : Type} (H : is_trunc n A) : is_trunc m A :=
  transport (λk, is_trunc k A) p H

  definition is_trunc_succ_succ_of_is_trunc_loop (n : ℕ₋₂) (A : Type*) (H : is_trunc (n.+1) (Ω A))
    (H2 : is_conn 0 A) : is_trunc (n.+2) A :=
  begin
    apply is_trunc_succ_of_is_trunc_loop, apply minus_one_le_succ,
    refine is_conn.elim -1 _ _, exact H
  end

  lemma is_trunc_of_is_trunc_loopn (m n : ℕ) (A : Type*) (H : is_trunc n (Ω[m] A))
    (H2 : is_conn (m.-1) A) : is_trunc (m + n) A :=
  begin
    revert A H H2; induction m with m IH: intro A H H2,
    { rewrite [nat.zero_add], exact H },
    rewrite [succ_add],
    apply is_trunc_succ_succ_of_is_trunc_loop,
    { apply IH,
      { apply is_trunc_equiv_closed _ !loopn_succ_in },
      apply is_conn_loop },
    exact is_conn_of_le _ (zero_le_of_nat m)
  end

  lemma is_trunc_of_is_set_loopn (m : ℕ) (A : Type*) (H : is_set (Ω[m] A))
    (H2 : is_conn (m.-1) A) : is_trunc m A :=
  is_trunc_of_is_trunc_loopn m 0 A H H2

end is_trunc
namespace sigma
  open sigma.ops

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
    apply isomorphism_of_equiv (equiv.mk (trunc_functor 0 f) (is_equiv_trunc_functor 0 f)), intros x x',
    induction x with a, induction x' with a', apply ap tr, exact h a a'
  end

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

definition fiber_eq_equiv' [constructor] {A B : Type} {f : A → B} {b : B} (x y : fiber f b)
  : (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
@equiv_change_inv _ _ (fiber_eq_equiv x y) (λpq, fiber_eq pq.1 pq.2)
  begin intro pq, cases pq, reflexivity end

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
λc, is_trunc_equiv_closed_rev k (fiber_compose g f c)

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

end function open function

namespace is_conn

open unit trunc_index nat is_trunc pointed.ops sigma.ops prod.ops

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
  apply is_trunc_equiv_closed_rev _ (list.sigma_char X),
end

end list


namespace susp
open trunc_index
/- move to freudenthal -/
definition freudenthal_pequiv_trunc_index' (A : Type*) (n : ℕ) (k : ℕ₋₂) [HA : is_conn n A]
  (H : k ≤ of_nat (2 * n)) : ptrunc k A ≃* ptrunc k (Ω (susp A)) :=
begin
  assert lem : Π(l : ℕ₋₂), l ≤ 0 → ptrunc l A ≃* ptrunc l (Ω (susp A)),
  { intro l H', exact ptrunc_pequiv_ptrunc_of_le H' (freudenthal_pequiv A (zero_le (2 * n))) },
  cases k with k, { exact lem -2 (minus_two_le 0) },
  cases k with k, { exact lem -1 (succ_le_succ (minus_two_le -1)) },
  rewrite [-of_nat_add_two at *, add_two_sub_two at HA],
  exact freudenthal_pequiv A (le_of_of_nat_le_of_nat H)
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
