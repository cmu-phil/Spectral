/-
Copyright (c) 2018 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import .pointed_pi

open eq pointed equiv sigma is_equiv trunc option pi function fiber sigma.ops

namespace pointed

section bpmap
/- binary pointed maps -/
structure bpmap (A B C : Type*) : Type :=
  (f : A → B →* C)
  (q : Πb, f pt b = pt)
  (r : q pt = respect_pt (f pt))

attribute [coercion] bpmap.f
variables {A B C D A' B' C' : Type*} {f f' : bpmap A B C}
definition respect_pt1 [unfold 4] (f : bpmap A B C) (b : B) : f pt b = pt :=
bpmap.q f b

definition respect_pt2 [unfold 4] (f : bpmap A B C) (a : A) : f a pt = pt :=
respect_pt (f a)

definition respect_ptpt [unfold 4] (f : bpmap A B C) : respect_pt1 f pt = respect_pt2 f pt :=
bpmap.r f

definition bpconst [constructor] (A B C : Type*) : bpmap A B C :=
bpmap.mk (λa, pconst B C) (λb, idp) idp

definition bppmap [constructor] (A B C : Type*) : Type* :=
pointed.MK (bpmap A B C) (bpconst A B C)

definition pmap_of_bpmap [constructor] (f : bppmap A B C) : ppmap A (ppmap B C) :=
begin
  fapply pmap.mk,
  { intro a, exact pmap.mk (f a) (respect_pt2 f a) },
  { exact eq_of_phomotopy (phomotopy.mk (respect_pt1 f) (respect_ptpt f)) }
end

definition bpmap_of_pmap [constructor] (f : ppmap A (ppmap B C)) : bppmap A B C :=
begin
  apply bpmap.mk (λa, f a) (ap010 pmap.to_fun (respect_pt f)),
  exact respect_pt (phomotopy_of_eq (respect_pt f))
end

protected definition bpmap.sigma_char [constructor] (A B C : Type*) :
  bpmap A B C ≃ Σ(f : A → B →* C) (q : Πb, f pt b = pt), q pt = respect_pt (f pt) :=
begin
  fapply equiv.MK,
  { intro f, exact ⟨f, respect_pt1 f, respect_ptpt f⟩ },
  { intro fqr, exact bpmap.mk fqr.1 fqr.2.1 fqr.2.2 },
  { intro fqr, induction fqr with f qr, induction qr with q r, reflexivity },
  { intro f, induction f, reflexivity }
end

definition to_homotopy_pt_square {f g : A →* B} (h : f ~* g) :
  square (respect_pt f) (respect_pt g) (h pt) idp :=
square_of_eq (to_homotopy_pt h)⁻¹

definition bpmap_eq_equiv [constructor] (f f' : bpmap A B C):
  f = f' ≃ Σ(h : Πa, f a ~* f' a) (q : Πb, square (respect_pt1 f b) (respect_pt1 f' b) (h pt b) idp), cube (vdeg_square (respect_ptpt f)) (vdeg_square (respect_ptpt f'))
       vrfl ids
       (q pt) (to_homotopy_pt_square (h pt)) :=
begin
  refine eq_equiv_fn_eq (bpmap.sigma_char A B C) f f' ⬝e _,
  refine !sigma_eq_equiv ⬝e _, esimp,
  refine sigma_equiv_sigma (!eq_equiv_homotopy ⬝e pi_equiv_pi_right (λa, !pmap_eq_equiv)) _,
  intro h, exact sorry
end

definition bpmap_eq [constructor] (h : Πa, f a ~* f' a)
  (q : Πb, square (respect_pt1 f b) (respect_pt1 f' b) (h pt b) idp)
  (r : cube (vdeg_square (respect_ptpt f)) (vdeg_square (respect_ptpt f'))
       vrfl ids
       (q pt) (to_homotopy_pt_square (h pt))) : f = f' :=
(bpmap_eq_equiv f f')⁻¹ᵉ ⟨h, q, r⟩

definition pmap_equiv_bpmap [constructor] (A B C : Type*) : pmap A (ppmap B C) ≃ bpmap A B C :=
begin
  refine !pmap.sigma_char ⬝e _ ⬝e !bpmap.sigma_char⁻¹ᵉ,
  refine sigma_equiv_sigma_right (λf, pmap_eq_equiv (f pt) !pconst) ⬝e _,
  refine sigma_equiv_sigma_right (λf, !phomotopy.sigma_char)
end

definition pmap_equiv_bpmap' [constructor] (A B C : Type*) : pmap A (ppmap B C) ≃ bpmap A B C :=
begin
  refine equiv_change_fun (pmap_equiv_bpmap A B C) _,
  exact bpmap_of_pmap, intro f, reflexivity
end

definition ppmap_pequiv_bppmap [constructor] (A B C : Type*) :
  ppmap A (ppmap B C) ≃* bppmap A B C :=
pequiv_of_equiv (pmap_equiv_bpmap' A B C) idp

definition bpmap_functor [constructor] (f : A' →* A) (g : B' →* B) (h : C →* C')
  (k : bpmap A B C) : bpmap A' B' C' :=
begin
  fapply bpmap.mk (λa', h ∘* k (f a') ∘* g),
  { intro b', refine ap h _ ⬝ respect_pt h,
    exact ap010 (λa b, k a b) (respect_pt f) (g b') ⬝ respect_pt1 k (g b') },
  { apply whisker_right, apply ap02 h, esimp,
    induction A with A a₀, induction B with B b₀, induction f with f f₀, induction g with g g₀,
    esimp at *, induction f₀, induction g₀, esimp, apply whisker_left, exact respect_ptpt k },
end

definition bppmap_functor [constructor] (f : A' →* A) (g : B' →* B) (h : C →* C') :
  bppmap A B C →* bppmap A' B' C' :=
begin
  apply pmap.mk (bpmap_functor f g h),
  induction A with A a₀, induction B with B b₀, induction C' with C' c₀',
  induction f with f f₀, induction g with g g₀, induction h with h h₀, esimp at *,
  induction f₀, induction g₀, induction h₀,
  reflexivity
end

  definition ppcompose_left' [constructor] (g : B →* C) : ppmap A B →* ppmap A C :=
  pmap.mk (pcompose g)
    begin induction C with C c₀, induction g with g g₀, esimp at *, induction g₀, reflexivity end

  definition ppcompose_right' [constructor] (f : A →* B) : ppmap B C →* ppmap A C :=
  pmap.mk (λg, g ∘* f)
    begin induction B with B b₀, induction f with f f₀, esimp at *, induction f₀, reflexivity end

definition ppmap_pequiv_bppmap_natural (f : A' →* A) (g : B' →* B) (h : C →* C') :
  psquare (ppmap_pequiv_bppmap A B C) (ppmap_pequiv_bppmap A' B' C')
          (ppcompose_right' f ∘* ppcompose_left' (ppcompose_right' g ∘* ppcompose_left' h))
          (bppmap_functor f g h) :=
begin
  induction A with A a₀, induction B with B b₀, induction C' with C' c₀',
  induction f with f f₀, induction g with g g₀, induction h with h h₀, esimp at *,
  induction f₀, induction g₀, induction h₀,
  fapply phomotopy.mk,
  { intro k, fapply bpmap_eq,
    { intro a, exact !passoc⁻¹* },
    { intro b, apply vdeg_square, esimp,
      refine ap02 _ !idp_con ⬝ _ ⬝ (ap (λx, ap010 pmap.to_fun x b) !idp_con)⁻¹ᵖ,
      refine ap02 _ !ap_eq_ap010⁻¹ ⬝ !ap_compose' ⬝ !ap_compose ⬝ !ap_eq_ap010 },
    { exact sorry }},
  { exact sorry }
end

/- maybe this is useful for pointed naturality in C? -/
definition ppmap_pequiv_bppmap_natural_right (h : C →* C') :
  psquare (ppmap_pequiv_bppmap A B C) (ppmap_pequiv_bppmap A B C')
          (ppcompose_left' (ppcompose_left' h))
          (bppmap_functor !pid !pid h) :=
begin
  induction A with A a₀, induction B with B b₀, induction C' with C' c₀',
  induction h with h h₀, esimp at *, induction h₀,
  fapply phomotopy.mk,
  { intro k, fapply bpmap_eq,
    { intro a, exact pwhisker_left _ !pcompose_pid },
    { intro b, apply vdeg_square, esimp,
      refine ap02 _ !idp_con ⬝ _,
      refine ap02 _ !ap_eq_ap010⁻¹ ⬝ !ap_compose' ⬝ !ap_compose ⬝ !ap_eq_ap010 },
    { exact sorry }},
  { exact sorry }
end
end bpmap

/- fiberwise pointed maps -/
structure dbpmap {A : Type*} (B C : A → Type*) : Type :=
  (f : Πa, B a →* C a)
  (q : Πb, f pt b = pt)
  (r : q pt = respect_pt (f pt))

attribute [coercion] dbpmap.f
variables {A A' : Type*} {B C : A → Type*} {B' C' : A' → Type*} {f f' : dbpmap B C}
definition respect_ptd1 [unfold 4] (f : dbpmap B C) (b : B pt) : f pt b = pt :=
dbpmap.q f b

definition respect_ptd2 [unfold 4] (f : dbpmap B C) (a : A) : f a pt = pt :=
respect_pt (f a)

definition respect_dptpt [unfold 4] (f : dbpmap B C) : respect_ptd1 f pt = respect_ptd2 f pt :=
dbpmap.r f

definition dbpconst [constructor] (B C : A → Type*) : dbpmap B C :=
dbpmap.mk (λa, pconst (B a) (C a)) (λb, idp) idp

definition dbppmap [constructor] (B C : A → Type*) : Type* :=
pointed.MK (dbpmap B C) (dbpconst B C)

definition ppi_of_dbpmap [constructor] (f : dbppmap B C) : Π*a, B a →** C a :=
begin
  fapply ppi.mk,
  { intro a, exact pmap.mk (f a) (respect_ptd2 f a) },
  { exact eq_of_phomotopy (phomotopy.mk (respect_ptd1 f) (respect_dptpt f)) }
end

definition dbpmap_of_ppi [constructor] (f : Π*a, B a →** C a) : dbppmap B C :=
begin
  apply dbpmap.mk (λa, f a) (ap010 pmap.to_fun (respect_pt f)),
  exact respect_pt (phomotopy_of_eq (respect_pt f))
end

protected definition dbpmap.sigma_char [constructor] (B C : A → Type*) :
  dbpmap B C ≃ Σ(f : Πa, B a →* C a) (q : Πb, f pt b = pt), q pt = respect_pt (f pt) :=
begin
  fapply equiv.MK,
  { intro f, exact ⟨f, respect_ptd1 f, respect_dptpt f⟩ },
  { intro fqr, exact dbpmap.mk fqr.1 fqr.2.1 fqr.2.2 },
  { intro fqr, induction fqr with f qr, induction qr with q r, reflexivity },
  { intro f, induction f, reflexivity }
end

definition dbpmap_eq_equiv [constructor] (f f' : dbpmap B C):
  f = f' ≃ Σ(h : Πa, f a ~* f' a) (q : Πb, square (respect_ptd1 f b) (respect_ptd1 f' b) (h pt b) idp), cube (vdeg_square (respect_dptpt f)) (vdeg_square (respect_dptpt f'))
       vrfl ids
       (q pt) (to_homotopy_pt_square (h pt)) :=
begin
  refine eq_equiv_fn_eq (dbpmap.sigma_char B C) f f' ⬝e _,
  refine !sigma_eq_equiv ⬝e _, esimp,
  refine sigma_equiv_sigma (!eq_equiv_homotopy ⬝e pi_equiv_pi_right (λa, !pmap_eq_equiv)) _,
  intro h, exact sorry
end

definition dbpmap_eq [constructor] (h : Πa, f a ~* f' a)
  (q : Πb, square (respect_ptd1 f b) (respect_ptd1 f' b) (h pt b) idp)
  (r : cube (vdeg_square (respect_dptpt f)) (vdeg_square (respect_dptpt f'))
       vrfl ids
       (q pt) (to_homotopy_pt_square (h pt))) : f = f' :=
(dbpmap_eq_equiv f f')⁻¹ᵉ ⟨h, q, r⟩

definition ppi_equiv_dbpmap [constructor] (B C : A → Type*) : (Π*a, B a →** C a) ≃ dbpmap B C :=
begin
  refine !ppi.sigma_char ⬝e _ ⬝e !dbpmap.sigma_char⁻¹ᵉ,
  refine sigma_equiv_sigma_right (λf, pmap_eq_equiv (f pt) !pconst) ⬝e _,
  refine sigma_equiv_sigma_right (λf, !phomotopy.sigma_char)
end

definition ppi_equiv_dbpmap' [constructor] (B C : A → Type*) : (Π*a, B a →** C a) ≃ dbpmap B C :=
begin
  refine equiv_change_fun (ppi_equiv_dbpmap B C) _,
  exact dbpmap_of_ppi, intro f, reflexivity
end

definition pppi_pequiv_dbppmap [constructor] (B C : A → Type*) :
  (Π*a, B a →** C a) ≃* dbppmap B C :=
pequiv_of_equiv (ppi_equiv_dbpmap' B C) idp

definition dbpmap_functor [constructor] (f : A' →* A) (g : Πa, B' a →* B (f a)) (h : Πa, C (f a) →* C' a)
  (k : dbpmap B C) : dbpmap B' C' :=
begin
  fapply dbpmap.mk (λa', h a' ∘* k (f a') ∘* g a'),
  { intro b', refine ap (h pt) _ ⬝ respect_pt (h pt),
    exact sorry }, --ap010 (λa b, k a b) (respect_pt f) (g pt b') ⬝ respect_ptd1 k (g pt b') },
  { exact sorry },
    -- apply whisker_right, apply ap02 h, esimp,
    -- induction A with A a₀, induction B with B b₀, induction f with f f₀, induction g with g g₀,
    -- esimp at *, induction f₀, induction g₀, esimp, apply whisker_left, exact respect_dptpt k },
end

end pointed
