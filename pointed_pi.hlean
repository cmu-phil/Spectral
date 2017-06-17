/-
Copyright (c) 2016 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Floris van Doorn
-/

import homotopy.connectedness types.pointed2

open eq pointed equiv sigma is_equiv

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
  sorry
  variable {k}
  protected definition ppi_homotopy.rfl [refl] : k ~~* k :=
  ppi_homotopy.refl k

  protected definition ppi_homotopy.symm [symm] (p : k ~~* l) : l ~~* k :=
  sorry

  protected definition ppi_homotopy.trans [trans] (p : k ~~* l) (q : l ~~* m) : k ~~* m :=
  sorry

  infix ` ⬝*' `:75 := ppi_homotopy.trans
  postfix `⁻¹*'`:(max+1) := ppi_homotopy.symm

  definition ppi_equiv_pmap (A B : Type*) : (Π*(a : A), B) ≃ (A →* B) :=
  begin
    fapply equiv.MK,
    { intro k, induction k with k p, exact pmap.mk k p },
    { intro k, induction k with k p, exact ppi.mk k p },
    { intro k, induction k with k p, reflexivity },
    { intro k, induction k with k p, reflexivity }
  end

  definition pppi_pequiv_ppmap (A B : Type*) : (Π*(a : A), B) ≃* ppmap A B :=
  pequiv_of_equiv (ppi_equiv_pmap A B) idp

  definition ppi.sigma_char [constructor] {A : Type*} (B : A → Type*)
    : (Π*(a : A), B a) ≃ Σ(k : (Π (a : A), B a)), k pt = pt :=
  begin
    fapply equiv.MK : intros k,
    { exact ⟨ k , ppi_resp_pt k ⟩ },
    all_goals cases k with k p,
    { exact ppi.mk k p },
    all_goals reflexivity
  end

  protected definition ppi_gen.sigma_char [constructor] {A : Type*} (B : A → Type) (b₀ : B pt) :
    ppi_gen B b₀ ≃ Σ(k : Πa, B a), k pt = b₀ :=
  begin
    fapply equiv.MK: intro x,
    { constructor, exact ppi_gen.resp_pt x },
    { induction x, constructor, assumption },
    { induction x, reflexivity },
    { induction x, reflexivity }
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


  variables
  -- the same as pmap_eq
  variables {k l}
  definition ppi_eq (h : k ~~* l) : k = l :=
  (ppi_eq_equiv k l)⁻¹ᵉ h

  definition eq_of_ppi_homotopy (h : k ~~* l) : k = l := ppi_eq h

  definition ppi_homotopy_of_eq (p : k = l) : k ~~* l := ppi_eq_equiv k l p

  definition ppi_homotopy_of_eq_of_ppi_homotopy (h : k ~~* l) :
    ppi_homotopy_of_eq (eq_of_ppi_homotopy h) = h :=
  to_right_inv (ppi_eq_equiv k l) h

  definition ppi_loop_equiv_lemma (p : k ~ k)
    : (p pt ⬝ ppi_gen.resp_pt k = ppi_gen.resp_pt k) ≃ (p pt = idp) :=
    calc (p pt ⬝ ppi_gen.resp_pt k = ppi_gen.resp_pt k)
      ≃ (p pt ⬝ ppi_gen.resp_pt k = idp ⬝ ppi_gen.resp_pt k)
        : equiv_eq_closed_right (p pt ⬝ ppi_gen.resp_pt k) (inverse (idp_con (ppi_gen.resp_pt k)))
  ... ≃ (p pt = idp)
        : eq_equiv_con_eq_con_right

  variables (k l)
  definition ppi_loop_equiv : (k = k) ≃ Π*(a : A), Ω (pType.mk (B a) (k a)) :=
    calc (k = k) ≃ (k ~~* k)
                   : ppi_eq_equiv
             ... ≃ Σ(p : k ~ k), p pt ⬝ ppi_gen.resp_pt k = ppi_gen.resp_pt k
                   : ppi_homotopy.sigma_char k k
             ... ≃ Σ(p : k ~ k), p pt = idp
                   : sigma_equiv_sigma_right
                       (λ p, ppi_loop_equiv_lemma p)
             ... ≃ Π*(a : A), pType.mk (k a = k a) idp
                   : ppi.sigma_char
             ... ≃ Π*(a : A), Ω (pType.mk (B a) (k a))
                   : erfl

  variables {k l}
  -- definition eq_of_ppi_homotopy (h : k ~~* l) : k = l :=
  -- (ppi_eq_equiv k l)⁻¹ᵉ h

  definition ppi_loop_pequiv : Ω (Π*(a : A), P a) ≃* Π*(a : A), Ω (P a) :=
  pequiv_of_equiv (ppi_loop_equiv pt) idp

  definition pmap_compose_ppi [constructor] (g : Π(a : A), ppmap (P a) (Q a))
    (f : Π*(a : A), P a) : Π*(a : A), Q a :=
  proof ppi.mk (λa, g a (f a)) (ap (g pt) (ppi.resp_pt f) ⬝ respect_pt (g pt)) qed

  definition pmap_compose_ppi_const_right (g : Π(a : A), ppmap (P a) (Q a)) :
    pmap_compose_ppi g (ppi_const P) ~~* ppi_const Q :=
  proof ppi_homotopy.mk (λa, respect_pt (g a)) !idp_con⁻¹ qed

  definition pmap_compose_ppi_const_left (f : Π*(a : A), P a) :
    pmap_compose_ppi (λa, pconst (P a) (Q a)) f ~~* ppi_const Q :=
  sorry

  definition ppi_compose_left [constructor] (g : Π(a : A), ppmap (P a) (Q a)) :
    (Π*(a : A), P a) →* Π*(a : A), Q a :=
  pmap.mk (pmap_compose_ppi g) (ppi_eq (pmap_compose_ppi_const_right g))

  definition pmap_compose_ppi_phomotopy_left [constructor] {g g' : Π(a : A), ppmap (P a) (Q a)}
    (f : Π*(a : A), P a) (p : Πa, g a ~* g' a) : pmap_compose_ppi g f ~~* pmap_compose_ppi g' f :=
  sorry

  definition pmap_compose_ppi_pid_left [constructor]
    (f : Π*(a : A), P a) : pmap_compose_ppi (λa, pid (P a)) f ~~* f :=
  sorry

  definition pmap_compose_pmap_compose_ppi [constructor] (h : Π(a : A), ppmap (Q a) (R a))
    (g : Π(a : A), ppmap (P a) (Q a)) :
    pmap_compose_ppi h (pmap_compose_ppi g f) ~~* pmap_compose_ppi (λa, h a ∘* g a) f :=
  sorry

  definition ppi_pequiv_right [constructor] (g : Π(a : A), P a ≃* Q a) :
    (Π*(a : A), P a) ≃* Π*(a : A), Q a :=
  begin
    apply pequiv_of_pmap (ppi_compose_left g),
    apply adjointify _ (ppi_compose_left (λa, (g a)⁻¹ᵉ*)),
    { intro f, apply ppi_eq,
      refine !pmap_compose_pmap_compose_ppi ⬝*' _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pright_inv) ⬝*' _,
      apply pmap_compose_ppi_pid_left },
    { intro f, apply ppi_eq,
      refine !pmap_compose_pmap_compose_ppi ⬝*' _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pleft_inv) ⬝*' _,
      apply pmap_compose_ppi_pid_left }
  end

  definition psigma_gen [constructor] {A : Type*} (P : A → Type) (x : P pt) : Type* :=
  pointed.MK (Σa, P a) ⟨pt, x⟩

end pointed
open fiber function
namespace pointed

  variables {A B C : Type*}

  -- TODO: replace in types.fiber
  definition pfiber.sigma_char' (f : A →* B) :
    pfiber f ≃* psigma_gen (λa, f a = pt) (respect_pt f) :=
  pequiv_of_equiv (fiber.sigma_char f pt) idp

  /- the pointed type of unpointed (nondependent) maps -/
  definition parrow [constructor] (A : Type) (B : Type*) : Type* :=
  pointed.MK (A → B) (const A pt)

  /- the pointed type of unpointed dependent maps -/
  definition p_pi [constructor] {A : Type} (B : A → Type*) : Type* :=
  pointed.MK (Πa, B a) (λa, pt)

  definition ppmap.sigma_char (A B : Type*) :
    ppmap A B ≃* @psigma_gen (parrow A B) (λf, f pt = pt) idp :=
  pequiv_of_equiv pmap.sigma_char idp

  definition pppi.sigma_char {A : Type*} {B : A → Type*} :
    (Π*(a : A), B a) ≃* @psigma_gen (p_pi B) (λf, f pt = pt) idp :=
  proof pequiv_of_equiv !ppi.sigma_char idp qed

  definition psigma_gen_pequiv_psigma_gen_right {A : Type*} {B B' : A → Type}
    {b : B pt} {b' : B' pt} (f : Πa, B a ≃ B' a) (p : f pt b = b') :
    psigma_gen B b ≃* psigma_gen B' b' :=
  pequiv_of_equiv (sigma_equiv_sigma_right f) (ap (dpair pt) p)

  definition psigma_gen_pequiv_psigma_gen_basepoint {A : Type*} {B : A → Type} {b b' : B pt}
    (p : b = b') : psigma_gen B b ≃* psigma_gen B b' :=
  psigma_gen_pequiv_psigma_gen_right (λa, erfl) p

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

  definition ppi_psigma {A : Type*} {B : A → Type*} (C : Πa, B a → Type) (c : Πa, C a pt) :
    (Π*(a : A), (psigma_gen (C a) (c a))) ≃*
    psigma_gen (λ(f : Π*(a : A), B a), ppi_gen (λa, C a (f a))
                                               (transport (C pt) (ppi.resp_pt f)⁻¹ (c pt)))
               (ppi_const _) :=
  calc (Π*(a : A), psigma_gen (C a) (c a))
          ≃* @psigma_gen (p_pi (λa, psigma_gen (C a) (c a))) (λf, f pt = pt) idp : pppi.sigma_char
      ... ≃* psigma_gen (λ(f : Π*(a : A), B a), ppi_gen (λa, C a (f a))
                                                        (transport (C pt) (ppi.resp_pt f)⁻¹ (c pt)))
                        (ppi_const _) : sorry

  definition pmap_psigma {A B : Type*} (C : B → Type) (c : C pt) :
    ppmap A (psigma_gen C c) ≃*
    psigma_gen (λ(f : ppmap A B), ppi_gen (C ∘ f) (transport C (respect_pt f)⁻¹ c))
                (ppi_const _) :=
  !pppi_pequiv_ppmap⁻¹ᵉ* ⬝e* !ppi_psigma ⬝e* sorry


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
             by exact (pmap_psigma _ _)⁻¹ᵉ*
      ... ≃* ppmap A (pfiber f) : by exact pequiv_ppcompose_left !pfiber.sigma_char'⁻¹ᵉ*


  definition pfiber_ppcompose_left_dep {B C : A → Type*} (f : Πa, B a →* C a) :
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

end pointed open pointed

open is_trunc is_conn
namespace is_conn
  variables (A : Type*) (n : ℕ₋₂) [H : is_conn (n.+1) A]
  include H

  definition is_contr_ppi_match (P : A → (n.+1)-Type*)
    : is_contr (Π*(a : A), P a) :=
  begin
    apply is_contr.mk pt,
    intro f, induction f with f p,
    apply ppi_eq, fapply ppi_homotopy.mk,
    { apply is_conn.elim n, exact p⁻¹ },
    { krewrite (is_conn.elim_β n), apply con.left_inv }
  end

  definition is_trunc_ppi (k : ℕ₋₂) (P : A → (n.+1+2+k)-Type*)
    : is_trunc k.+1 (Π*(a : A), P a) :=
  begin
    induction k with k IH,
    { apply is_prop_of_imp_is_contr, intro f,
      apply is_contr_ppi_match },
    { apply is_trunc_succ_of_is_trunc_loop
        (trunc_index.succ_le_succ (trunc_index.minus_two_le k)),
      intro f,
      apply @is_trunc_equiv_closed_rev _ _ k.+1
        (ppi_loop_equiv f),
      apply IH, intro a,
      apply ptrunctype.mk (Ω (pType.mk (P a) (f a))),
      { apply is_trunc_loop, exact is_trunc_ptrunctype (P a) },
      { exact pt } }
  end

  definition is_trunc_pmap_of_is_conn (k : ℕ₋₂) (B : (n.+1+2+k)-Type*)
    : is_trunc k.+1 (A →* B) :=
  @is_trunc_equiv_closed _ _ k.+1 (ppi_equiv_pmap A B)
    (is_trunc_ppi A n k (λ a, B))

end is_conn
