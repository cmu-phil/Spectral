/-
Copyright (c) 2016 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Floris van Doorn
-/

import homotopy.connectedness types.pointed2 .move_to_lib .pointed

open eq pointed equiv sigma is_equiv trunc option pi function fiber

/-
  In this file we define dependent pointed maps and properties of them.

  Using this, we give the truncation level
  of the type of pointed maps, giving the connectivity of
  the domain and the truncation level of the codomain.
  This is is_trunc_pmap_of_is_conn at the end.

  We also prove other properties about pointed (dependent maps), like the fact that
  (Π*a, F a) → (Π*a, X a) → (Π*a, B a)
  is a fibration sequence if (F a) → (X a) → B a) is.
-/

namespace pointed

  /- the pointed type of unpointed (nondependent) maps -/
  definition pumap [constructor] (A : Type) (B : Type*) : Type* :=
  pointed.MK (A → B) (const A pt)

  /- the pointed type of unpointed dependent maps -/
  definition pupi [constructor] {A : Type} (B : A → Type*) : Type* :=
  pointed.MK (Πa, B a) (λa, pt)

  notation `Πᵘ*` binders `, ` r:(scoped P, pupi P) := r
  infix ` →ᵘ* `:30 := pumap

  /- stuff about the pointed type of unpointed maps (dependent and non-dependent) -/
  definition sigma_pumap {A : Type} (B : A → Type) (C : Type*) :
    ((Σa, B a) →ᵘ* C) ≃* Πᵘ*a, B a →ᵘ* C :=
  pequiv_of_equiv (equiv_sigma_rec _)⁻¹ᵉ idp

  definition loop_pupi [constructor] {A : Type} (B : A → Type*) : Ω (Πᵘ*a, B a) ≃* Πᵘ*a, Ω (B a) :=
  pequiv_of_equiv eq_equiv_homotopy idp

  definition phomotopy_mk_pupi [constructor] {A : Type*} {B : Type} {C : B → Type*}
    {f g : A →* (Πᵘ*b, C b)} (p : f ~2 g)
    (q : p pt ⬝hty apd10 (respect_pt g) ~ apd10 (respect_pt f)) : f ~* g :=
  begin
    apply phomotopy.mk (λa, eq_of_homotopy (p a)),
    apply eq_of_fn_eq_fn eq_equiv_homotopy,
    apply eq_of_homotopy, intro b,
    refine !apd10_con ⬝ _,
    refine whisker_right _ !pi.apd10_eq_of_homotopy ⬝ q b
  end

  definition pupi_functor [constructor] {A A' : Type} {B : A → Type*} {B' : A' → Type*}
    (f : A' → A) (g : Πa, B (f a) →* B' a) : (Πᵘ*a, B a) →* (Πᵘ*a', B' a') :=
  pmap.mk (pi_functor f g) (eq_of_homotopy (λa, respect_pt (g a)))

  definition pupi_functor_right [constructor] {A : Type} {B B' : A → Type*}
    (g : Πa, B a →* B' a) : (Πᵘ*a, B a) →* (Πᵘ*a, B' a) :=
  pupi_functor id g

  definition pupi_functor_compose {A A' A'' : Type}
    {B : A → Type*} {B' : A' → Type*} {B'' : A'' → Type*} (f : A'' → A') (f' : A' → A)
    (g' : Πa, B' (f a) →* B'' a) (g : Πa, B (f' a) →* B' a) :
    pupi_functor (f' ∘ f) (λa, g' a ∘* g (f a)) ~* pupi_functor f g' ∘* pupi_functor f' g :=
  begin
    fapply phomotopy_mk_pupi,
    { intro h a, reflexivity },
    { intro a, refine !idp_con ⬝ _, refine !apd10_con ⬝ _ ⬝ !pi.apd10_eq_of_homotopy⁻¹, esimp,
      refine (!apd10_prepostcompose ⬝ ap02 (g' a) !pi.apd10_eq_of_homotopy) ◾
             !pi.apd10_eq_of_homotopy }
  end

  definition pupi_functor_pid (A : Type) (B : A → Type*) :
    pupi_functor id (λa, pid (B a)) ~* pid (Πᵘ*a, B a) :=
  begin
    fapply phomotopy_mk_pupi,
    { intro h a, reflexivity },
    { intro a, refine !idp_con ⬝ !pi.apd10_eq_of_homotopy⁻¹ }
  end

  definition pupi_functor_phomotopy {A A' : Type} {B : A → Type*} {B' : A' → Type*}
    {f f' : A' → A} {g : Πa, B (f a) →* B' a} {g' : Πa, B (f' a) →* B' a}
    (p : f ~ f') (q : Πa, g a ~* g' a ∘* ptransport B (p a)) :
    pupi_functor f g ~* pupi_functor f' g' :=
  begin
    fapply phomotopy_mk_pupi,
    { intro h a, exact q a (h (f a)) ⬝ ap (g' a) (apdt h (p a)) },
    { intro a, esimp,
     exact whisker_left _ !pi.apd10_eq_of_homotopy ⬝ !con.assoc ⬝
           to_homotopy_pt (q a) ⬝ !pi.apd10_eq_of_homotopy⁻¹ }
  end

  definition pupi_pequiv [constructor] {A A' : Type} {B : A → Type*} {B' : A' → Type*}
    (e : A' ≃ A) (f : Πa, B (e a) ≃* B' a) :
    (Πᵘ*a, B a) ≃* (Πᵘ*a', B' a') :=
  pequiv.MK (pupi_functor e f)
            (pupi_functor e⁻¹ᵉ (λa, ptransport B (right_inv e a) ∘* (f (e⁻¹ᵉ a))⁻¹ᵉ*))
    abstract begin
      refine !pupi_functor_compose⁻¹* ⬝* pupi_functor_phomotopy (to_right_inv e) _ ⬝*
             !pupi_functor_pid,
      intro a, exact !pinv_pcompose_cancel_right ⬝* !pid_pcompose⁻¹*
    end end
    abstract begin
      refine !pupi_functor_compose⁻¹* ⬝* pupi_functor_phomotopy (to_left_inv e) _ ⬝*
             !pupi_functor_pid,
      intro a, refine !passoc⁻¹* ⬝* pinv_right_phomotopy_of_phomotopy _ ⬝* !pid_pcompose⁻¹*,
      refine pwhisker_left _ _ ⬝* !ptransport_natural,
      exact ptransport_change_eq _ (adj e a) ⬝* ptransport_ap B e (to_left_inv e a)
    end end

  definition pupi_pequiv_right [constructor] {A : Type} {B B' : A → Type*} (f : Πa, B a ≃* B' a) :
    (Πᵘ*a, B a) ≃* (Πᵘ*a, B' a) :=
  pupi_pequiv erfl f

  definition loop_pumap [constructor] (A : Type) (B : Type*) : Ω (A →ᵘ* B) ≃* A →ᵘ* Ω B :=
  loop_pupi (λa, B)

  definition phomotopy_mk_pumap [constructor] {A C : Type*} {B : Type} {f g : A →* (B →ᵘ* C)}
    (p : f ~2 g) (q : p pt ⬝hty apd10 (respect_pt g) ~ apd10 (respect_pt f))
    : f ~* g :=
  phomotopy_mk_pupi p q

  definition pumap_functor [constructor] {A A' : Type} {B B' : Type*} (f : A' → A) (g : B →* B') :
    (A →ᵘ* B) →* (A' →ᵘ* B') :=
  pupi_functor f (λa, g)

  definition pumap_functor_compose {A A' A'' : Type} {B B' B'' : Type*}
    (f : A'' → A') (f' : A' → A) (g' : B' →* B'') (g : B →* B') :
    pumap_functor (f' ∘ f) (g' ∘* g) ~* pumap_functor f g' ∘* pumap_functor f' g :=
  pupi_functor_compose f f' (λa, g') (λa, g)

  definition pumap_functor_pid (A : Type) (B : Type*) :
    pumap_functor id (pid B) ~* pid (A →ᵘ* B) :=
  pupi_functor_pid A (λa, B)

  definition pumap_functor_phomotopy {A A' : Type} {B B' : Type*} {f f' : A' → A} {g g' : B →* B'}
    (p : f ~ f') (q : g ~* g') : pumap_functor f g ~* pumap_functor f' g' :=
  pupi_functor_phomotopy p (λa, q ⬝* !pcompose_pid⁻¹* ⬝* pwhisker_left _ !ptransport_constant⁻¹*)

  definition pumap_pequiv [constructor] {A A' : Type} {B B' : Type*} (e : A ≃ A') (f : B ≃* B') :
    (A →ᵘ* B) ≃* (A' →ᵘ* B') :=
  pupi_pequiv e⁻¹ᵉ (λa, f)

  definition pumap_pequiv_right [constructor] (A : Type) {B B' : Type*} (f : B ≃* B') :
    (A →ᵘ* B) ≃* (A →ᵘ* B') :=
  pumap_pequiv erfl f

  definition pumap_pequiv_left [constructor] {A A' : Type} (B : Type*) (f : A ≃ A') :
    (A →ᵘ* B) ≃* (A' →ᵘ* B) :=
  pumap_pequiv f pequiv.rfl

  /- the pointed sigma type -/
  definition psigma_gen [constructor] {A : Type*} (P : A → Type) (x : P pt) : Type* :=
  pointed.MK (Σa, P a) ⟨pt, x⟩

  definition psigma_gen_functor [constructor] {A A' : Type*} {B : A → Type}
    {B' : A' → Type} {b : B pt} {b' : B' pt} (f : A →* A')
    (g : Πa, B a → B' (f a)) (p : g pt b =[respect_pt f] b') : psigma_gen B b →* psigma_gen B' b' :=
  pmap.mk (sigma_functor f g) (sigma_eq (respect_pt f) p)

  definition psigma_gen_functor_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a → B' a) (p : f pt b = b') :
    psigma_gen B b →* psigma_gen B' b' :=
  proof pmap.mk (sigma_functor id f) (sigma_eq_right p) qed

  definition psigma_gen_pequiv_psigma_gen [constructor] {A A' : Type*} {B : A → Type}
    {B' : A' → Type} {b : B pt} {b' : B' pt} (f : A ≃* A')
    (g : Πa, B a ≃ B' (f a)) (p : g pt b =[respect_pt f] b') : psigma_gen B b ≃* psigma_gen B' b' :=
  pequiv_of_equiv (sigma_equiv_sigma f g) (sigma_eq (respect_pt f) p)

  definition psigma_gen_pequiv_psigma_gen_left [constructor] {A A' : Type*} {B : A' → Type}
    {b : B pt} (f : A ≃* A') {b' : B (f pt)} (q : b' =[respect_pt f] b) :
    psigma_gen (B ∘ f) b' ≃* psigma_gen B b :=
  psigma_gen_pequiv_psigma_gen f (λa, erfl) q

  definition psigma_gen_pequiv_psigma_gen_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a ≃ B' a) (p : f pt b = b') :
    psigma_gen B b ≃* psigma_gen B' b' :=
  psigma_gen_pequiv_psigma_gen pequiv.rfl f (pathover_idp_of_eq p)

  definition psigma_gen_pequiv_psigma_gen_basepoint [constructor] {A : Type*} {B : A → Type}
    {b b' : B pt} (p : b = b') : psigma_gen B b ≃* psigma_gen B b' :=
  psigma_gen_pequiv_psigma_gen_right (λa, erfl) p

  definition loop_psigma_gen {A : Type*} (B : A → Type) (b₀ : B pt) :
    Ω (psigma_gen B b₀) ≃* @psigma_gen (Ω A) (λp, pathover B b₀ p b₀) idpo :=
  pequiv_of_equiv (sigma_eq_equiv pt pt) idp

  /- maybe this needs to be generalized to ap1_gen -/
  definition loop_psigma_gen_natural {A A' : Type*} {B : A → Type}
    {B' : A' → Type} {b : B pt} {b' : B' pt} (f : A →* A')
    (g : Πa, B a → B' (f a)) (p : g pt b =[respect_pt f] b') :
    psquare (Ω→ (psigma_gen_functor f g p))
            (psigma_gen_functor (Ω→ f) (λq r, p⁻¹ᵒ ⬝o pathover_ap _ _ (apo g r) ⬝o p)
            !cono.left_inv)
            (loop_psigma_gen B b) (loop_psigma_gen B' b') :=
  sorry /- TODO FOR SSS -/

  definition psigma_gen_functor_psquare [constructor] {A₀₀ A₀₂ A₂₀ A₂₂ : Type*}
    {B₀₀ : A₀₀ → Type} {B₀₂ : A₀₂ → Type} {B₂₀ : A₂₀ → Type} {B₂₂ : A₂₂ → Type}
    {b₀₀ : B₀₀ pt} {b₀₂ : B₀₂ pt} {b₂₀ : B₂₀ pt} {b₂₂ : B₂₂ pt}
    {f₀₁ : A₀₀ →* A₀₂} {f₁₀ : A₀₀ →* A₂₀} {f₂₁ : A₂₀ →* A₂₂} {f₁₂ : A₀₂ →* A₂₂}
    {g₀₁ : Π⦃a⦄, B₀₀ a → B₀₂ (f₀₁ a)} {g₁₀ : Π⦃a⦄, B₀₀ a → B₂₀ (f₁₀ a)}
    {g₂₁ : Π⦃a⦄, B₂₀ a → B₂₂ (f₂₁ a)} {g₁₂ : Π⦃a⦄, B₀₂ a → B₂₂ (f₁₂ a)}
    {p₀₁ : g₀₁ b₀₀ =[respect_pt f₀₁] b₀₂} {p₁₀ : g₁₀ b₀₀ =[respect_pt f₁₀] b₂₀}
    {p₂₁ : g₂₁ b₂₀ =[respect_pt f₂₁] b₂₂} {p₁₂ : g₁₂ b₀₂ =[respect_pt f₁₂] b₂₂}
    (h₁ : psquare f₁₀ f₁₂ f₀₁ f₂₁)
    (h₂ : Π⦃a⦄ (b : B₀₀ a), pathover B₂₂ (g₂₁ (g₁₀ b)) (h₁ a) (g₁₂ (g₀₁ b)))
    (h₃ : squareover B₂₂ (square_of_eq (!con_idp ⬝ (to_homotopy_pt h₁)⁻¹))
                         (pathover_ap B₂₂ f₂₁ (apo g₂₁ p₁₀) ⬝o p₂₁)
                         (pathover_ap B₂₂ f₁₂ (apo g₁₂ p₀₁) ⬝o p₁₂)
                         (h₂ b₀₀) idpo) :
    psquare (psigma_gen_functor f₁₀ g₁₀ p₁₀) (psigma_gen_functor f₁₂ g₁₂ p₁₂)
            (psigma_gen_functor f₀₁ g₀₁ p₀₁) (psigma_gen_functor f₂₁ g₂₁ p₂₁) :=
  sorry /- TODO FOR SSS -/

end pointed open pointed

namespace pointed

  definition pointed_respect_pt [instance] [constructor] {A B : Type*} (f : A →* B) :
    pointed (f pt = pt) :=
  pointed.mk (respect_pt f)

  definition ppi_gen_of_phomotopy [constructor] {A B : Type*} {f g : A →* B} (h : f ~* g) :
    ppi_gen (λx, f x = g x) (respect_pt f ⬝ (respect_pt g)⁻¹) :=
  h

  abbreviation ppi_resp_pt [unfold 3] := @ppi.resp_pt

  definition ppi_const [constructor] {A : Type*} (P : A → Type*) : ppi P :=
  ppi.mk (λa, pt) idp

  definition pointed_ppi [instance] [constructor] {A : Type*}
    (P : A → Type*) : pointed (ppi P) :=
  pointed.mk (ppi_const P)

  definition pppi [constructor] {A : Type*} (P : A → Type*) : Type* :=
  pointed.mk' (ppi P)

  notation `Π*` binders `, ` r:(scoped P, pppi P) := r

  definition ppi_homotopy {A : Type*} {P : A → Type} {x : P pt} (f g : ppi_gen P x) : Type :=
  ppi_gen (λa, f a = g a) (ppi_gen.resp_pt f ⬝ (ppi_gen.resp_pt g)⁻¹)

  variables {A : Type*} {P Q R : A → Type*} {f g h : Π*a, P a}
                        {B : A → Type} {x₀ : B pt} {k l m : ppi_gen B x₀}

  infix ` ~~* `:50 := ppi_homotopy

  definition ppi_homotopy.mk [constructor] [reducible] (h : k ~ l)
    (p : h pt ⬝ ppi_gen.resp_pt l = ppi_gen.resp_pt k) : k ~~* l :=
  ppi_gen.mk h (eq_con_inv_of_con_eq p)
  definition ppi_to_homotopy [coercion] [unfold 6] [reducible] (p : k ~~* l) : Πa, k a = l a := p
  definition ppi_to_homotopy_pt [unfold 6] [reducible] (p : k ~~* l) :
    p pt ⬝ ppi_gen.resp_pt l = ppi_gen.resp_pt k :=
  con_eq_of_eq_con_inv (ppi_gen.resp_pt p)

  variable (k)
  protected definition ppi_homotopy.refl : k ~~* k :=
  ppi_homotopy.mk homotopy.rfl !idp_con
  variable {k}
  protected definition ppi_homotopy.rfl [refl] : k ~~* k :=
  ppi_homotopy.refl k

  protected definition ppi_homotopy.symm [symm] (p : k ~~* l) : l ~~* k :=
  ppi_homotopy.mk p⁻¹ʰᵗʸ (inv_con_eq_of_eq_con (ppi_to_homotopy_pt p)⁻¹)

  protected definition ppi_homotopy.trans [trans] (p : k ~~* l) (q : l ~~* m) : k ~~* m :=
  ppi_homotopy.mk (λa, p a ⬝ q a) (!con.assoc ⬝ whisker_left (p pt) (ppi_to_homotopy_pt q) ⬝ ppi_to_homotopy_pt p)

  infix ` ⬝*' `:75 := ppi_homotopy.trans
  postfix `⁻¹*'`:(max+1) := ppi_homotopy.symm

  definition ppi_trans_refl (p : k ~~* l) : p ⬝*' ppi_homotopy.refl l = p :=
  begin
    unfold ppi_homotopy.trans,
    induction A with A a₀,
    induction k with k k₀, induction l with l l₀, induction p with p p₀, esimp at p, induction l₀, esimp at p₀, induction p₀, reflexivity, 
  end

  definition ppi_equiv_pmap [constructor] (A B : Type*) : (Π*(a : A), B) ≃ (A →* B) :=
  begin
    fapply equiv.MK,
    { intro k, induction k with k p, exact pmap.mk k p },
    { intro k, induction k with k p, exact ppi.mk k p },
    { intro k, induction k with k p, reflexivity },
    { intro k, induction k with k p, reflexivity }
  end

  definition pppi_pequiv_ppmap [constructor] (A B : Type*) : (Π*(a : A), B) ≃* ppmap A B :=
  pequiv_of_equiv (ppi_equiv_pmap A B) idp

  protected definition ppi_gen.sigma_char [constructor] {A : Type*} (B : A → Type) (b₀ : B pt) :
    ppi_gen B b₀ ≃ Σ(k : Πa, B a), k pt = b₀ :=
  begin
    fapply equiv.MK: intro x,
    { constructor, exact ppi_gen.resp_pt x },
    { induction x, constructor, assumption },
    { induction x, reflexivity },
    { induction x, reflexivity }
  end

  definition ppi.sigma_char [constructor] {A : Type*} (B : A → Type*)
    : (Π*(a : A), B a) ≃ Σ(k : (Π (a : A), B a)), k pt = pt :=
  begin
    fapply equiv.MK : intros k,
    { exact ⟨ k , ppi_resp_pt k ⟩ },
    all_goals cases k with k p,
    { exact ppi.mk k p },
    all_goals reflexivity
  end


  variables (k l)

  definition ppi_homotopy.rec' [recursor] (B : k ~~* l → Type)
    (H : Π(h : k ~ l) (p : h pt ⬝ ppi_gen.resp_pt l = ppi_gen.resp_pt k), B (ppi_homotopy.mk h p))
    (h : k ~~* l) : B h :=
  begin
    induction h with h p,
    refine transport (λp, B (ppi_gen.mk h p)) _ (H h (con_eq_of_eq_con_inv p)),
    apply to_left_inv !eq_con_inv_equiv_con_eq p
  end

  definition ppi_homotopy.sigma_char [constructor]
    : (k ~~* l) ≃ Σ(p : k ~ l), p pt ⬝ ppi_gen.resp_pt l = ppi_gen.resp_pt k :=
  begin
    fapply equiv.MK : intros h,
    { exact ⟨h , ppi_to_homotopy_pt h⟩ },
    { cases h with h p, exact ppi_homotopy.mk h p },
    { cases h with h p, exact ap (dpair h) (to_right_inv !eq_con_inv_equiv_con_eq p) },
    { induction h using ppi_homotopy.rec' with h p,
      exact ap (ppi_homotopy.mk h) (to_right_inv !eq_con_inv_equiv_con_eq p) }
  end

  -- the same as pmap_eq_equiv
  definition ppi_eq_equiv : (k = l) ≃ (k ~~* l) :=
    calc (k = l) ≃ ppi_gen.sigma_char B x₀ k = ppi_gen.sigma_char B x₀ l
                   : eq_equiv_fn_eq (ppi_gen.sigma_char B x₀) k l
            ...  ≃ Σ(p : k = l),
                     pathover (λh, h pt = x₀) (ppi_gen.resp_pt k) p (ppi_gen.resp_pt l)
                   : sigma_eq_equiv _ _
            ...  ≃ Σ(p : k = l),
                     ppi_gen.resp_pt k = ap (λh, h pt) p ⬝ ppi_gen.resp_pt l
                   : sigma_equiv_sigma_right
                       (λp, eq_pathover_equiv_Fl p (ppi_gen.resp_pt k) (ppi_gen.resp_pt l))
            ...  ≃ Σ(p : k = l),
                     ppi_gen.resp_pt k = apd10 p pt ⬝ ppi_gen.resp_pt l
                   : sigma_equiv_sigma_right
                       (λp, equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)))
            ...  ≃ Σ(p : k ~ l), ppi_gen.resp_pt k = p pt ⬝ ppi_gen.resp_pt l
                   : sigma_equiv_sigma_left' eq_equiv_homotopy
            ...  ≃ Σ(p : k ~ l), p pt ⬝ ppi_gen.resp_pt l = ppi_gen.resp_pt k
                   : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
            ...  ≃ (k ~~* l) : ppi_homotopy.sigma_char k l

  -- the same as pmap_eq
  variables {k l}
  definition ppi_eq (h : k ~~* l) : k = l :=
  (ppi_eq_equiv k l)⁻¹ᵉ h

  definition eq_of_ppi_homotopy (h : k ~~* l) : k = l := ppi_eq h

  definition ppi_homotopy_of_eq (p : k = l) : k ~~* l := ppi_eq_equiv k l p

  definition ppi_homotopy_of_eq_of_ppi_homotopy (h : k ~~* l) :
    ppi_homotopy_of_eq (eq_of_ppi_homotopy h) = h :=
  to_right_inv (ppi_eq_equiv k l) h

  variable (k)

  definition eq_ppi_homotopy_refl_ppi_homotopy_of_eq_refl : ppi_homotopy.refl k = ppi_homotopy_of_eq (refl k) :=
  begin
    induction k with k p,
    induction p, reflexivity
  end

  definition ppi_homotopy_of_eq_refl 
    : ppi_homotopy.refl k = ppi_homotopy_of_eq (refl k)
    :=
  begin
    induction k with k k₀, induction k₀, reflexivity,
  end

  definition ppi_homotopy_of_eq_con {A : Type*} {B : A → Type*} {f g h : Π* (a : A), B a} (p : f = g) (q : g = h) :
    ppi_homotopy_of_eq (p ⬝ q) = ppi_homotopy_of_eq p ⬝*' ppi_homotopy_of_eq q :=
  begin induction q, induction p, 
    fapply eq_of_ppi_homotopy,
    rewrite [!idp_con],
    refine transport (λ x, x ~~* x ⬝*' x) !ppi_homotopy_of_eq_refl _,
    fapply ppi_homotopy_of_eq,
    refine (ppi_trans_refl (ppi_homotopy.refl f))⁻¹  
  end

--  definition ppi_homotopy_of_eq_of_ppi_homotopy 

  definition ppi_homotopy_mk_ppmap [constructor] 
    {A : Type*} {X : A → Type*} {Y : Π (a : A), X a → Type*} 
    {f g : Π* (a : A), Π*(x : (X a)), (Y a x)} 
    (p : Πa, f a ~~* g a)
    (q : p pt ⬝*' ppi_homotopy_of_eq (ppi_resp_pt g) = ppi_homotopy_of_eq (ppi_resp_pt f))
    : f ~~* g :=
  begin
    apply ppi_homotopy.mk (λa, eq_of_ppi_homotopy (p a)),
    apply eq_of_fn_eq_fn (ppi_eq_equiv _ _),
    refine !ppi_homotopy_of_eq_con ⬝ _,
    repeat exact sorry
--    refine !ppi_homotopy_of_eq_of_ppi_homotopy ◾** idp ⬝ q,
  end

  variable {k}

  definition ppi_homotopy_rec_on_eq [recursor] {k' : ppi_gen B x₀}
    {Q : (k ~~* k') → Type} (p : k ~~* k') (H : Π(q : k = k'), Q (ppi_homotopy_of_eq q)) : Q p :=
  ppi_homotopy_of_eq_of_ppi_homotopy p ▸ H (eq_of_ppi_homotopy p)

  definition ppi_homotopy_rec_on_idp [recursor]
    {Q : Π {k' : ppi_gen B x₀},  (k ~~* k') → Type}
    (q : Q (ppi_homotopy.refl k)) {k' : ppi_gen B x₀} (H : k ~~* k') : Q H :=
  begin
    induction H using ppi_homotopy_rec_on_eq with t,
    induction t, exact eq_ppi_homotopy_refl_ppi_homotopy_of_eq_refl k ▸ q,
  end

  variables (k l)

  definition ppi_loop_equiv : (k = k) ≃ Π*(a : A), Ω (pType.mk (B a) (k a)) :=
  begin
    induction k with k p, induction p,
    exact ppi_eq_equiv (ppi_gen.mk k idp) (ppi_gen.mk k idp)
  end

  variables {k l}
  -- definition eq_of_ppi_homotopy (h : k ~~* l) : k = l :=
  -- (ppi_eq_equiv k l)⁻¹ᵉ h

  definition pmap_compose_ppi [constructor] (g : Π(a : A), ppmap (P a) (Q a))
    (f : Π*(a : A), P a) : Π*(a : A), Q a :=
  proof ppi.mk (λa, g a (f a)) (ap (g pt) (ppi.resp_pt f) ⬝ respect_pt (g pt)) qed

  definition pmap_compose_ppi_const_right (g : Π(a : A), ppmap (P a) (Q a)) :
    pmap_compose_ppi g (ppi_const P) ~~* ppi_const Q :=
  proof ppi_homotopy.mk (λa, respect_pt (g a)) !idp_con⁻¹ qed

  definition pmap_compose_ppi_const_left (f : Π*(a : A), P a) :
    pmap_compose_ppi (λa, pconst (P a) (Q a)) f ~~* ppi_const Q :=
  ppi_homotopy.mk homotopy.rfl !ap_constant⁻¹

  definition ppi_compose_left [constructor] (g : Π(a : A), ppmap (P a) (Q a)) :
    (Π*(a : A), P a) →* Π*(a : A), Q a :=
  pmap.mk (pmap_compose_ppi g) (ppi_eq (pmap_compose_ppi_const_right g))

  -- ppi_compose_left is associative in the following sense.
  definition ppi_assoc_compose_left {A : Type*} {B C D : A → Type*}
    (f : Π (a : A), B a →* C a) (g : Π (a : A), C a →* D a)
    : (ppi_compose_left g ∘* ppi_compose_left f) ~* ppi_compose_left (λ a, g a ∘* f a) :=
  begin
    fapply phomotopy.mk,
    intro h, fapply eq_of_ppi_homotopy,
    fapply ppi_homotopy.mk,
    intro a, reflexivity,
    refine !idp_con ⬝ _,
--    esimp,
    repeat exact sorry,
  end /- TODO FOR SSS -/

  definition psquare_of_ppi_compose_left {A : Type*} {B C D E : A → Type*}
    {ftop : Π (a : A), B a →* C a} {fbot : Π (a : A), D a →* E a}
    {fleft : Π (a : A), B a →* D a} {fright : Π (a : A), C a →* E a}
    (psq : Π (a :A), psquare (ftop a) (fbot a) (fleft a) (fright a))
    : psquare
        (ppi_compose_left ftop)
        (ppi_compose_left fbot)
        (ppi_compose_left fleft)
        (ppi_compose_left fright)
    :=
  begin
    refine (ppi_assoc_compose_left ftop fright) ⬝* _ ⬝* (ppi_assoc_compose_left fleft fbot)⁻¹*,
    refine eq_of_homotopy (λ a, eq_of_phomotopy (psq a)) ▸ phomotopy.rfl,
    -- the last step is probably an unnecessary application of function extensionality.
  end

  definition pmap_compose_ppi_phomotopy_left [constructor] {g g' : Π(a : A), ppmap (P a) (Q a)}
    (f : Π*(a : A), P a) (p : Πa, g a ~* g' a) : pmap_compose_ppi g f ~~* pmap_compose_ppi g' f :=
  ppi_homotopy.mk (λa, p a (f a))
    abstract !con.assoc⁻¹ ⬝ whisker_right _ !ap_con_eq_con_ap⁻¹ ⬝ !con.assoc ⬝
             whisker_left _ (to_homotopy_pt (p pt)) end

  definition pmap_compose_ppi_pid_left [constructor]
    (f : Π*(a : A), P a) : pmap_compose_ppi (λa, pid (P a)) f ~~* f :=
  ppi_homotopy.mk homotopy.rfl idp

  definition pmap_compose_ppi_pcompose [constructor] (h : Π(a : A), ppmap (Q a) (R a))
    (g : Π(a : A), ppmap (P a) (Q a)) :
    pmap_compose_ppi (λa, h a ∘* g a) f ~~* pmap_compose_ppi h (pmap_compose_ppi g f)  :=
  ppi_homotopy.mk homotopy.rfl
    abstract !idp_con ⬝ whisker_right _ (!ap_con ⬝ whisker_right _ !ap_compose'⁻¹) ⬝ !con.assoc end

  definition ppi_pequiv_right [constructor] (g : Π(a : A), P a ≃* Q a) :
    (Π*(a : A), P a) ≃* Π*(a : A), Q a :=
  begin
    apply pequiv_of_pmap (ppi_compose_left g),
    apply adjointify _ (ppi_compose_left (λa, (g a)⁻¹ᵉ*)),
    { intro f, apply ppi_eq,
      refine !pmap_compose_ppi_pcompose⁻¹*' ⬝*' _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pright_inv) ⬝*' _,
      apply pmap_compose_ppi_pid_left },
    { intro f, apply ppi_eq,
      refine !pmap_compose_ppi_pcompose⁻¹*' ⬝*' _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pleft_inv) ⬝*' _,
      apply pmap_compose_ppi_pid_left }
  end

end pointed


namespace pointed

  variables {A B C : Type*}

  -- TODO: replace in types.fiber
  definition pfiber.sigma_char' (f : A →* B) :
    pfiber f ≃* psigma_gen (λa, f a = pt) (respect_pt f) :=
  pequiv_of_equiv (fiber.sigma_char f pt) idp

  definition ppmap.sigma_char [constructor] (A B : Type*) :
    ppmap A B ≃* @psigma_gen (A →ᵘ* B) (λf, f pt = pt) idp :=
  pequiv_of_equiv pmap.sigma_char idp

  definition pppi.sigma_char [constructor] (B : A → Type*) :
    (Π*(a : A), B a) ≃* @psigma_gen (Πᵘ*a, B a) (λf, f pt = pt) idp :=
  proof pequiv_of_equiv !ppi.sigma_char idp qed

  definition pppi_sigma_char_natural_bottom {B B' : A → Type*} (f : Πa, B a →* B' a) :
    @psigma_gen (Πᵘ*a, B a) (λg, g pt = pt) idp →* @psigma_gen (Πᵘ*a, B' a) (λg, g pt = pt) idp :=
  psigma_gen_functor
    (pupi_functor_right f)
    (λg p, ap (f pt) p ⬝ respect_pt (f pt))
    begin
      apply eq_pathover_constant_right, apply square_of_eq,
      esimp, exact !idp_con ⬝ !apd10_eq_of_homotopy⁻¹ ⬝ !ap_eq_apd10⁻¹,
    end

  definition pppi_sigma_char_natural {B B' : A → Type*} (f : Πa, B a →* B' a) :
    psquare (ppi_compose_left f) (pppi_sigma_char_natural_bottom f)
            (pppi.sigma_char B) (pppi.sigma_char B') :=
  sorry /- TODO FOR SSS -/

  definition ppi_gen_functor_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a → B' a) (p : f pt b = b') (g : ppi_gen B b)
    : ppi_gen B' b' :=
  ppi_gen.mk (λa, f a (g a)) (ap (f pt) (ppi_gen.resp_pt g) ⬝ p)

  definition ppi_gen_functor_right_compose [constructor] {A : Type*} {B₁ B₂ B₃ : A → Type}
    {b₁ : B₁ pt} {b₂ : B₂ pt} {b₃ : B₃ pt} (f₂ : Πa, B₂ a → B₃ a) (p₂ : f₂ pt b₂ = b₃)
    (f₁ : Πa, B₁ a → B₂ a) (p₁ : f₁ pt b₁ = b₂)
    (g : ppi_gen B₁ b₁) : ppi_gen_functor_right (λa, f₂ a ∘ f₁ a) (ap (f₂ pt) p₁ ⬝ p₂) g ~~*
    ppi_gen_functor_right f₂ p₂ (ppi_gen_functor_right f₁ p₁ g) :=
  begin
    fapply ppi_homotopy.mk,
    { reflexivity },
    { induction p₁, induction p₂, exact !idp_con ⬝ !ap_compose⁻¹ }
  end

  definition ppi_gen_functor_right_id [constructor] {A : Type*} {B : A → Type}
    {b : B pt} (g : ppi_gen B b) : ppi_gen_functor_right (λa, id) idp g ~~* g :=
  begin
    fapply ppi_homotopy.mk,
    { reflexivity },
    { reflexivity }
  end

  definition ppi_gen_functor_right_homotopy [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} {f f' : Πa, B a → B' a} {p : f pt b = b'} {p' : f' pt b = b'}
    (h : f ~2 f') (q : h pt b ⬝ p' = p) (g : ppi_gen B b) :
    ppi_gen_functor_right f p g ~~* ppi_gen_functor_right f' p' g :=
  begin
    fapply ppi_homotopy.mk,
    { exact λa, h a (g a) },
    { induction g with g r, induction r, induction q,
      exact whisker_left _ !idp_con ⬝ !idp_con⁻¹ }
  end

  definition ppi_gen_equiv_ppi_gen_right [constructor] {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a ≃ B' a) (p : f pt b = b') :
    ppi_gen B b ≃ ppi_gen B' b' :=
  equiv.MK (ppi_gen_functor_right f p) (ppi_gen_functor_right (λa, (f a)⁻¹ᵉ) (inv_eq_of_eq p⁻¹))
    abstract begin
      intro g, apply ppi_eq,
      refine !ppi_gen_functor_right_compose⁻¹*' ⬝*' _,
      refine ppi_gen_functor_right_homotopy (λa, to_right_inv (f a)) _ g ⬝*'
            !ppi_gen_functor_right_id, induction p, exact adj (f pt) b ⬝ ap02 (f pt) !idp_con⁻¹

    end end
    abstract begin
      intro g, apply ppi_eq,
      refine !ppi_gen_functor_right_compose⁻¹*' ⬝*' _,
      refine ppi_gen_functor_right_homotopy (λa, to_left_inv (f a)) _ g ⬝*'
            !ppi_gen_functor_right_id, induction p, exact (!idp_con ⬝ !idp_con)⁻¹,
    end end

  definition ppi_gen_equiv_ppi_gen_basepoint [constructor] {A : Type*} {B : A → Type} {b b' : B pt}
    (p : b = b') : ppi_gen B b ≃ ppi_gen B b' :=
  ppi_gen_equiv_ppi_gen_right (λa, erfl) p

  open sigma.ops

  definition psigma_gen_pi_pequiv_pupi_psigma_gen [constructor] {A : Type*} {B : A → Type*}
    (C : Πa, B a → Type) (c : Πa, C a pt) :
    @psigma_gen (Πᵘ*a, B a) (λf, Πa, C a (f a)) c ≃* Πᵘ*a, psigma_gen (C a) (c a) :=
  pequiv_of_equiv sigma_pi_equiv_pi_sigma idp

  definition pupi_psigma_gen_pequiv_psigma_gen_pi [constructor] {A : Type*} {B : A → Type*}
    (C : Πa, B a → Type) (c : Πa, C a pt) :
    (Πᵘ*a, psigma_gen (C a) (c a)) ≃* @psigma_gen (Πᵘ*a, B a) (λf, Πa, C a (f a)) c :=
  pequiv_of_equiv sigma_pi_equiv_pi_sigma⁻¹ᵉ idp

  definition psigma_gen_assoc [constructor] {A : Type*} {B : A → Type} (C : Πa, B a → Type)
    (b₀ : B pt) (c₀ : C pt b₀) :
    psigma_gen (λa, Σb, C a b) ⟨b₀, c₀⟩ ≃* @psigma_gen (psigma_gen B b₀) (λv, C v.1 v.2) c₀ :=
  pequiv_of_equiv !sigma_assoc_equiv idp

  definition psigma_gen_swap [constructor] {A : Type*} {B B' : A → Type}
    (C : Π⦃a⦄, B a → B' a → Type) (b₀ : B pt) (b₀' : B' pt) (c₀ : C b₀ b₀') :
    @psigma_gen (psigma_gen B  b₀ ) (λv, Σb', C v.2 b') ⟨b₀', c₀⟩ ≃*
    @psigma_gen (psigma_gen B' b₀') (λv, Σb , C b  v.2) ⟨b₀ , c₀⟩ :=
  !psigma_gen_assoc⁻¹ᵉ* ⬝e* psigma_gen_pequiv_psigma_gen_right (λa, !sigma_comm_equiv) idp ⬝e*
  !psigma_gen_assoc

  definition ppi_psigma.{u v w} {A : pType.{u}} {B : A → pType.{v}} (C : Πa, B a → Type.{w})
    (c : Πa, C a pt) : (Π*(a : A), (psigma_gen (C a) (c a))) ≃*
    psigma_gen (λ(f : Π*(a : A), B a), ppi_gen (λa, C a (f a))
                 (transport (C pt) (ppi.resp_pt f)⁻¹ (c pt))) (ppi_const _) :=
  proof
  calc (Π*(a : A), psigma_gen (C a) (c a))
          ≃* @psigma_gen (Πᵘ*a, psigma_gen (C a) (c a)) (λf, f pt = pt) idp : pppi.sigma_char
      ... ≃* @psigma_gen (@psigma_gen (Πᵘ*a, B a) (λf, Πa, C a (f a)) c)
                         (λv, Σ(p : v.1 pt = pt), v.2 pt =[p] c pt) ⟨idp, idpo⟩ :
             by exact psigma_gen_pequiv_psigma_gen (pupi_psigma_gen_pequiv_psigma_gen_pi C c)
                        (λf, sigma_eq_equiv _ _) idpo
      ... ≃* @psigma_gen (@psigma_gen (Πᵘ*a, B a) (λf, f pt = pt) idp)
                         (λv, Σ(g : Πa, C a (v.1 a)), g pt =[v.2] c pt) ⟨c, idpo⟩ :
             by apply psigma_gen_swap
      ... ≃* psigma_gen (λ(f : Π*(a : A), B a), ppi_gen (λa, C a (f a))
                                                        (transport (C pt) (ppi.resp_pt f)⁻¹ (c pt)))
                        (ppi_const _) :
             by exact (psigma_gen_pequiv_psigma_gen (pppi.sigma_char B)
                (λf, !ppi_gen.sigma_char ⬝e sigma_equiv_sigma_right (λg, !pathover_equiv_eq_tr⁻¹ᵉ))
                idpo)⁻¹ᵉ*
  qed

  definition ppmap_psigma {A B : Type*} (C : B → Type) (c : C pt) :
    ppmap A (psigma_gen C c) ≃*
    psigma_gen (λ(f : ppmap A B), ppi_gen (C ∘ f) (transport C (respect_pt f)⁻¹ c))
                (ppi_const _) :=
  !pppi_pequiv_ppmap⁻¹ᵉ* ⬝e* !ppi_psigma ⬝e*
  sorry
--  psigma_gen_pequiv_psigma_gen (pppi_pequiv_ppmap A B) (λf, begin esimp, exact ppi_gen_equiv_ppi_gen_right (λa, _) _ end) _

  definition pfiber_ppcompose_left (f : B →* C) :
    pfiber (@ppcompose_left A B C f) ≃* ppmap A (pfiber f) :=
  calc
    pfiber (@ppcompose_left A B C f) ≃*
             psigma_gen (λ(g : ppmap A B), f ∘* g = pconst A C)
             proof (eq_of_phomotopy (pcompose_pconst f)) qed :
             by exact !pfiber.sigma_char'
      ... ≃* psigma_gen (λ(g : ppmap A B), f ∘* g ~* pconst A C) proof (pcompose_pconst f) qed :
             by exact psigma_gen_pequiv_psigma_gen_right (λa, !pmap_eq_equiv)
                        !phomotopy_of_eq_of_phomotopy
      ... ≃* psigma_gen (λ(g : ppmap A B), ppi_gen (λa, f (g a) = pt)
               (transport (λb, f b = pt) (respect_pt g)⁻¹ (respect_pt f)))
               (ppi_const _) :
             begin
               refine psigma_gen_pequiv_psigma_gen_right
                        (λg, ppi_gen_equiv_ppi_gen_basepoint (_ ⬝ !eq_transport_Fl⁻¹)) _,
               intro g, refine !con_idp ⬝ _, apply whisker_right,
               exact ap02 f !inv_inv⁻¹ ⬝ !ap_inv,
               apply ppi_eq, fapply ppi_homotopy.mk,
                 intro x, reflexivity,
                 refine !idp_con ⬝ _, symmetry, refine !ap_id ◾ !idp_con ⬝ _, apply con.right_inv
             end
      ... ≃* ppmap A (psigma_gen (λb, f b = pt) (respect_pt f)) :
             by exact (ppmap_psigma _ _)⁻¹ᵉ*
      ... ≃* ppmap A (pfiber f) : by exact pequiv_ppcompose_left !pfiber.sigma_char'⁻¹ᵉ*


  definition pfiber_ppi_compose_left {B C : A → Type*} (f : Πa, B a →* C a) :
    pfiber (ppi_compose_left f) ≃* Π*(a : A), pfiber (f a) :=
  calc
    pfiber (ppi_compose_left f) ≃*
             psigma_gen (λ(g : Π*(a : A), B a), pmap_compose_ppi f g = ppi_const C)
               proof (ppi_eq (pmap_compose_ppi_const_right f)) qed : by exact !pfiber.sigma_char'
      ... ≃* psigma_gen (λ(g : Π*(a : A), B a), pmap_compose_ppi f g ~~* ppi_const C)
               proof (pmap_compose_ppi_const_right f) qed :
             by exact psigma_gen_pequiv_psigma_gen_right (λa, !ppi_eq_equiv)
                        !ppi_homotopy_of_eq_of_ppi_homotopy
      ... ≃* psigma_gen (λ(g : Π*(a : A), B a), ppi_gen (λa, f a (g a) = pt)
               (transport (λb, f pt b = pt) (ppi.resp_pt g)⁻¹ (respect_pt (f pt))))
               (ppi_const _) :
             begin
               refine psigma_gen_pequiv_psigma_gen_right
                        (λg, ppi_gen_equiv_ppi_gen_basepoint (_ ⬝ !eq_transport_Fl⁻¹)) _,
               intro g, refine !con_idp ⬝ _, apply whisker_right,
               exact ap02 (f pt) !inv_inv⁻¹ ⬝ !ap_inv,
               apply ppi_eq, fapply ppi_homotopy.mk,
                 intro x, reflexivity,
                 refine !idp_con ⬝ _, symmetry, refine !ap_id ◾ !idp_con ⬝ _, apply con.right_inv
             end
      ... ≃* Π*(a : A), (psigma_gen (λb, f a b = pt) (respect_pt (f a))) :
             by exact (ppi_psigma _ _)⁻¹ᵉ*
      ... ≃* Π*(a : A), pfiber (f a) : by exact ppi_pequiv_right (λa, !pfiber.sigma_char'⁻¹ᵉ*)

  -- definition pppi_ppmap {A C : Type*} {B : A → Type*} :
  --   ppmap (/- dependent smash of B -/) C ≃* Π*(a : A), ppmap (B a) C :=

  definition ppi_add_point_over {A : Type} (B : A → Type*) :
    (Π*a, add_point_over B a) ≃ Πa, B a :=
  begin
    fapply equiv.MK,
    { intro f a, exact f (some a) },
    { intro f, fconstructor,
        intro a, cases a, exact pt, exact f a,
        reflexivity },
    { intro f, reflexivity },
    { intro f, cases f with f p, apply ppi_eq, fapply ppi_homotopy.mk,
      { intro a, cases a, exact p⁻¹, reflexivity },
      { exact con.left_inv p }},
  end

  definition pppi_add_point_over {A : Type} (B : A → Type*) :
    (Π*a, add_point_over B a) ≃* Πᵘ*a, B a :=
  pequiv_of_equiv (ppi_add_point_over B) idp

  definition ppmap_add_point {A : Type} (B : Type*) :
    ppmap A₊ B ≃* A →ᵘ* B :=
  pequiv_of_equiv (pmap_equiv_left A B) idp

  -- TODO: homotopy_of_eq and apd10 should be the same
  -- TODO: there is also apd10_eq_of_homotopy in both pi and eq(?)

  definition loop_pppi_pequiv {A : Type*} (B : A → Type*) : Ω (Π*a, B a) ≃* Π*(a : A), Ω (B a) :=
  begin
    refine loop_pequiv_loop (pppi.sigma_char B) ⬝e* _,
    refine !loop_psigma_gen ⬝e* _,
    transitivity @psigma_gen (Πᵘ*a, Ω (B a)) (λf, f pt = idp) idp,
      exact psigma_gen_pequiv_psigma_gen
      (loop_pupi B) (λp, eq_pathover_equiv_Fl p idp idp ⬝e
                  equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)) ⬝e !eq_equiv_eq_symm) idpo,
    exact (pppi.sigma_char (Ω ∘ B))⁻¹ᵉ*
  end

  definition psquare_loop_ppi_compose_left {A : Type*} {X Y : A → Type*} (f :  Π (a : A), X a →* Y a) :
    psquare
      (Ω→ (ppi_compose_left f))
      (ppi_compose_left (λ a, Ω→ (f a)))
      (loop_pppi_pequiv X)
      (loop_pppi_pequiv Y)
    :=
  begin
    refine ap1_psquare (pppi_sigma_char_natural f) ⬝v* _,
    refine !loop_psigma_gen_natural ⬝v* _,
    refine _ ⬝v* (pppi_sigma_char_natural (λ a, Ω→ (f a)))⁻¹ᵛ*,
    fapply psigma_gen_functor_psquare,

    repeat exact sorry
  end /- TODO FOR SSS -/

end pointed open pointed

open is_trunc is_conn
namespace is_conn
  section

  variables (A : Type*) (n : ℕ₋₂) [H : is_conn (n.+1) A]
  include H

  definition is_contr_ppi_match (P : A → Type*) (H : Πa, is_trunc (n.+1) (P a))
    : is_contr (Π*(a : A), P a) :=
  begin
    apply is_contr.mk pt,
    intro f, induction f with f p,
    apply ppi_eq, fapply ppi_homotopy.mk,
    { apply is_conn.elim n, exact p⁻¹ },
    { krewrite (is_conn.elim_β n), apply con.left_inv }
  end

  -- definition is_trunc_ppi_of_is_conn (k : ℕ₋₂) (P : A → Type*)
  --   : is_trunc k.+1 (Π*(a : A), P a) :=

  definition is_trunc_ppi_of_is_conn (k l : ℕ₋₂) (H2 : l ≤ n.+1+2+k)
    (P : A → Type*) (H3 : Πa, is_trunc l (P a)) :
    is_trunc k.+1 (Π*(a : A), P a) :=
  begin
    have H4 : Πa, is_trunc (n.+1+2+k) (P a), from λa, is_trunc_of_le (P a) H2,
    clear H2 H3, revert P H4,
    induction k with k IH: intro P H4,
    { apply is_prop_of_imp_is_contr, intro f,
      apply is_contr_ppi_match A n P H4 },
    { apply is_trunc_succ_of_is_trunc_loop
        (trunc_index.succ_le_succ (trunc_index.minus_two_le k)),
      intro f,
      apply @is_trunc_equiv_closed_rev _ _ k.+1 (ppi_loop_equiv f),
      apply IH, intro a,
      apply is_trunc_loop, apply H4 }
  end


  definition is_trunc_pmap_of_is_conn (k l : ℕ₋₂) (B : Type*) (H2 : l ≤ n.+1+2+k)
    (H3 : is_trunc l B) : is_trunc k.+1 (A →* B) :=
  @is_trunc_equiv_closed _ _ k.+1 (ppi_equiv_pmap A B)
    (is_trunc_ppi_of_is_conn A n k l H2 (λ a, B) _)

  end

  -- this is probably much easier to prove directly
  definition is_trunc_ppi (A : Type*) (n k : ℕ₋₂) (H : n ≤ k) (P : A → Type*)
    (H2 : Πa, is_trunc n (P a)) : is_trunc k (Π*(a : A), P a) :=
  begin
    cases k with k,
    { apply is_contr_of_merely_prop,
      { exact @is_trunc_ppi_of_is_conn A -2 (is_conn_minus_one A (tr pt)) -2 _
                (trunc_index.le.step H) P H2 },
      { exact tr pt } },
    { assert K : n ≤ -1 +2+ k,
      { rewrite (trunc_index.add_plus_two_comm -1 k), exact H },
      { exact @is_trunc_ppi_of_is_conn A -2 (is_conn_minus_one A (tr pt)) k _ K P H2 } }
  end

end is_conn
