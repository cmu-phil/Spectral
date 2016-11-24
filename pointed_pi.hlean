/-
Copyright (c) 2016 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/

import move_to_lib

open eq pointed equiv sigma

/-
  The goal of this file is to give the truncation level
  of the type of pointed maps, giving the connectivity of
  the domain and the truncation level of the codomain.
  This is is_trunc_pmap at the end.

  First we define the type of dependent pointed maps
  as a tool, because these appear in the more general
  statement is_trunc_ppi (the generality needed for induction).

  Unfortunately, some of these names (ppi) and notations (Π*)
  clash with those in types.pi in the pi namespace.
-/

namespace pointed

  abbreviation ppi_resp_pt [unfold 3] := @ppi.resp_pt

  definition pointed_ppi [instance] [constructor] {A : Type*}
    (P : A → Type*) : pointed (ppi A P) :=
  pointed.mk (ppi.mk (λ a, pt) idp)

  definition pppi [constructor] {A : Type*} (P : A → Type*) : Type* :=
  pointed.mk' (ppi A P)

  notation `Π*` binders `, ` r:(scoped P, pppi P) := r

  structure ppi_homotopy {A : Type*} {P : A → Type*} (f g : Π*(a : A), P a) :=
    (homotopy : f ~ g)
    (homotopy_pt : homotopy pt ⬝ ppi_resp_pt g = ppi_resp_pt f)

  variables {A : Type*} {P : A → Type*} {f g : Π*(a : A), P a}

  infix ` ~~* `:50 := ppi_homotopy
  abbreviation ppi_to_homotopy_pt [unfold 5] := @ppi_homotopy.homotopy_pt
  abbreviation ppi_to_homotopy [coercion] [unfold 5] (p : f ~~* g) : Πa, f a = g a :=
  ppi_homotopy.homotopy p

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
            ...  ≃ Σ(p : ppi.to_fun f = ppi.to_fun g),
                     pathover (λh, h pt = pt) (ppi_resp_pt f) p (ppi_resp_pt g)
                   : sigma_eq_equiv _ _
            ...  ≃ Σ(p : ppi.to_fun f = ppi.to_fun g),
                     ppi_resp_pt f = ap (λh, h pt) p ⬝ ppi_resp_pt g
                   : sigma_equiv_sigma_right
                       (λp, eq_pathover_equiv_Fl p (ppi_resp_pt f) (ppi_resp_pt g))
            ...  ≃ Σ(p : ppi.to_fun f = ppi.to_fun g),
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

  definition is_trunc_pmap (k : ℕ₋₂) (B : (n.+1+2+k)-Type*)
    : is_trunc k.+1 (A →* B) :=
  @is_trunc_equiv_closed _ _ k.+1 (ppi_equiv_pmap A B)
    (is_trunc_ppi A n k (λ a, B))

end
