/-
Copyright (c) 2016 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/

import .move_to_lib

open eq pointed equiv sigma is_equiv

/-
  The goal of this file is to give the truncation level
  of the type of pointed maps, giving the connectivity of
  the domain and the truncation level of the codomain.
  This is is_trunc_pmap_of_is_conn at the end.

  First we define the type of dependent pointed maps
  as a tool, because these appear in the more general
  statement is_trunc_ppi (the generality needed for induction).

-/

namespace pointed

  abbreviation ppi_resp_pt [unfold 3] := @ppi.resp_pt

  definition ppi_const [constructor] {A : Type*} (P : A → Type*) : Π*(a : A), P a :=
  ppi.mk (λa, pt) idp

  definition pointed_ppi [instance] [constructor] {A : Type*}
    (P : A → Type*) : pointed (ppi A P) :=
  pointed.mk (ppi_const P)

  definition pppi [constructor] {A : Type*} (P : A → Type*) : Type* :=
  pointed.mk' (ppi A P)

  notation `Π*` binders `, ` r:(scoped P, pppi P) := r

  structure ppi_homotopy {A : Type*} {P : A → Type*} (f g : Π*(a : A), P a) :=
    (homotopy : f ~ g)
    (homotopy_pt : homotopy pt ⬝ ppi_resp_pt g = ppi_resp_pt f)

  variables {A : Type*} {P Q R : A → Type*} {f g h : Π*(a : A), P a}

  infix ` ~~* `:50 := ppi_homotopy
  abbreviation ppi_to_homotopy_pt [unfold 5] := @ppi_homotopy.homotopy_pt
  abbreviation ppi_to_homotopy [coercion] [unfold 5] (p : f ~~* g) : Πa, f a = g a :=
  ppi_homotopy.homotopy p

  variable (f)
  protected definition ppi_homotopy.refl : f ~~* f :=
  sorry
  variable {f}
  protected definition ppi_homotopy.rfl [refl] : f ~~* f :=
  ppi_homotopy.refl f

  protected definition ppi_homotopy.symm [symm] (p : f ~~* g) : g ~~* f :=
  sorry

  protected definition ppi_homotopy.trans [trans] (p : f ~~* g) (q : g ~~* h) : f ~~* h :=
  sorry

  infix ` ⬝*' `:75 := ppi_homotopy.trans
  postfix `⁻¹*'`:(max+1) := ppi_homotopy.symm

  definition ppi_equiv_pmap (A B : Type*) : (Π*(a : A), B) ≃ (A →* B) :=
  begin
    fapply equiv.MK,
    { intro f, induction f with f p, exact pmap.mk f p },
    { intro f, induction f with f p, exact ppi.mk f p },
    { intro f, induction f with f p, reflexivity },
    { intro f, induction f with f p, reflexivity }
  end

  definition ppi.sigma_char [constructor] {A : Type*} (P : A → Type*)
    : (Π*(a : A), P a) ≃ Σ(f : (Π (a : A), P a)), f pt = pt :=
  begin
    fapply equiv.MK : intros f,
    { exact ⟨ f , ppi_resp_pt f ⟩ },
    all_goals cases f with f p,
    { exact ppi.mk f p },
    all_goals reflexivity
  end

  -- the same as pmap_eq
  definition ppi_eq (h : f ~ g) : ppi_resp_pt f = h pt ⬝ ppi_resp_pt g → f = g :=
  begin
    cases f with f p, cases g with g q, intro r,
    esimp at *,
    fapply apd011 ppi.mk,
    { apply eq_of_homotopy h },
    { esimp, apply concato_eq, apply eq_pathover_Fl, apply inv_con_eq_of_eq_con,
      rewrite [ap_eq_apd10, apd10_eq_of_homotopy], exact r }
  end

  variables (f g)

  definition ppi_homotopy.sigma_char [constructor]
    : (f ~~* g) ≃ Σ(p : f ~ g), p pt ⬝ ppi_resp_pt g = ppi_resp_pt f :=
  begin
    fapply equiv.MK : intros h,
    { exact ⟨h , ppi_to_homotopy_pt h⟩ },
    all_goals cases h with h p,
    { exact ppi_homotopy.mk h p },
    all_goals reflexivity
  end

  -- the same as pmap_eq_equiv
  definition ppi_eq_equiv : (f = g) ≃ (f ~~* g) :=
    calc (f = g) ≃ ppi.sigma_char P f = ppi.sigma_char P g
                   : eq_equiv_fn_eq (ppi.sigma_char P) f g
            ...  ≃ Σ(p : f = g),
                     pathover (λh, h pt = pt) (ppi_resp_pt f) p (ppi_resp_pt g)
                   : sigma_eq_equiv _ _
            ...  ≃ Σ(p : f = g),
                     ppi_resp_pt f = ap (λh, h pt) p ⬝ ppi_resp_pt g
                   : sigma_equiv_sigma_right
                       (λp, eq_pathover_equiv_Fl p (ppi_resp_pt f) (ppi_resp_pt g))
            ...  ≃ Σ(p : f = g),
                     ppi_resp_pt f = apd10 p pt ⬝ ppi_resp_pt g
                   : sigma_equiv_sigma_right
                       (λp, equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)))
            ...  ≃ Σ(p : f ~ g), ppi_resp_pt f = p pt ⬝ ppi_resp_pt g
                   : sigma_equiv_sigma_left' eq_equiv_homotopy
            ...  ≃ Σ(p : f ~ g), p pt ⬝ ppi_resp_pt g = ppi_resp_pt f
                   : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
            ...  ≃ (f ~~* g) : ppi_homotopy.sigma_char f g

  definition ppi_loop_equiv_lemma (p : f ~ f)
    : (p pt ⬝ ppi_resp_pt f = ppi_resp_pt f) ≃ (p pt = idp) :=
    calc (p pt ⬝ ppi_resp_pt f = ppi_resp_pt f)
      ≃ (p pt ⬝ ppi_resp_pt f = idp ⬝ ppi_resp_pt f)
        : equiv_eq_closed_right (p pt ⬝ ppi_resp_pt f) (inverse (idp_con (ppi_resp_pt f)))
  ... ≃ (p pt = idp)
        : eq_equiv_con_eq_con_right

  definition ppi_loop_equiv : (f = f) ≃ Π*(a : A), Ω (pType.mk (P a) (f a)) :=
    calc (f = f) ≃ (f ~~* f)
                   : ppi_eq_equiv
             ... ≃ Σ(p : f ~ f), p pt ⬝ ppi_resp_pt f = ppi_resp_pt f
                   : ppi_homotopy.sigma_char f f
             ... ≃ Σ(p : f ~ f), p pt = idp
                   : sigma_equiv_sigma_right
                       (λ p, ppi_loop_equiv_lemma f p)
             ... ≃ Π*(a : A), pType.mk (f a = f a) idp
                   : ppi.sigma_char
             ... ≃ Π*(a : A), Ω (pType.mk (P a) (f a))
                   : erfl

  variables {f g}
  definition eq_of_ppi_homotopy (h : f ~~* g) : f = g :=
  (ppi_eq_equiv f g)⁻¹ᵉ h

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
  pmap.mk (pmap_compose_ppi g) (eq_of_ppi_homotopy (pmap_compose_ppi_const_right g))

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
    { intro f, apply eq_of_ppi_homotopy,
      refine !pmap_compose_pmap_compose_ppi ⬝*' _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pright_inv) ⬝*' _,
      apply pmap_compose_ppi_pid_left },
    { intro f, apply eq_of_ppi_homotopy,
      refine !pmap_compose_pmap_compose_ppi ⬝*' _,
      refine pmap_compose_ppi_phomotopy_left _ (λa, !pleft_inv) ⬝*' _,
      apply pmap_compose_ppi_pid_left }
  end

end pointed open pointed

open is_trunc is_conn
section
  variables (A : Type*) (n : ℕ₋₂) [H : is_conn (n.+1) A]
  include H

  definition is_contr_ppi_match (P : A → (n.+1)-Type*)
    : is_contr (Π*(a : A), P a) :=
  begin
    apply is_contr.mk pt,
    intro f, induction f with f p,
    fapply ppi_eq,
    { apply is_conn.elim n, esimp, exact p⁻¹ },
    { krewrite (is_conn.elim_β n), apply inverse, apply con.left_inv }
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

end
