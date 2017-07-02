/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Short exact sequences
-/
import homotopy.chain_complex eq2
open pointed is_trunc equiv is_equiv eq algebra group trunc function

structure is_exact_t {A B : Type} {C : Type*} (f : A → B) (g : B → C) :=
  ( im_in_ker : Π(a:A), g (f a) = pt)
  ( ker_in_im : Π(b:B), (g b = pt) → fiber f b)

structure is_exact {A B : Type} {C : Type*} (f : A → B) (g : B → C) :=
  ( im_in_ker : Π(a:A), g (f a) = pt)
  ( ker_in_im : Π(b:B), (g b = pt) → image f b)

namespace algebra

definition is_exact_g {A B C : Group} (f : A →g B) (g : B →g C) :=
is_exact f g

definition is_exact_ag {A B C : AbGroup} (f : A →g B) (g : B →g C) :=
is_exact f g

definition is_exact_g.mk {A B C : Group} {f : A →g B} {g : B →g C}
  (H₁ : Πa, g (f a) = 1) (H₂ : Πb, g b = 1 → image f b) : is_exact_g f g :=
is_exact.mk H₁ H₂

definition is_exact.im_in_ker2 {A B : Type} {C : Set*} {f : A → B} {g : B → C} (H : is_exact f g)
  {b : B} (h : image f b) : g b = pt :=
begin
  induction h with a p, exact ap g p⁻¹ ⬝ is_exact.im_in_ker H a
end

-- TO DO: give less univalency proof
definition is_exact_homotopy {A B : Type} {C : Type*} {f f' : A → B} {g g' : B → C}
  (p : f ~ f') (q : g ~ g') (H : is_exact f g) : is_exact f' g' :=
begin
  induction p using homotopy.rec_on_idp,
  induction q using homotopy.rec_on_idp,
  exact H
end

definition is_exact_trunc_functor {A B : Type} {C : Type*} {f : A → B} {g : B → C}
  (H : is_exact_t f g) : @is_exact _ _ (ptrunc 0 C) (trunc_functor 0 f) (trunc_functor 0 g) :=
begin
  constructor,
  { intro a, esimp, induction a with a,
    exact ap tr (is_exact_t.im_in_ker H a) },
  { intro b p, induction b with b, note q := !tr_eq_tr_equiv p, induction q with q,
    induction is_exact_t.ker_in_im H b q with a r,
    exact image.mk (tr a) (ap tr r) }
end

definition is_contr_middle_of_is_exact {A B : Type} {C : Type*} {f : A → B} {g : B → C} (H : is_exact f g)
  [is_contr A] [is_set B] [is_contr C] : is_contr B :=
begin
  apply is_contr.mk (f pt),
  intro b,
  induction is_exact.ker_in_im H b !is_prop.elim,
  exact ap f !is_prop.elim ⬝ p
end

definition is_surjective_of_is_exact_of_is_contr {A B : Type} {C : Type*} {f : A → B} {g : B → C}
  (H : is_exact f g) [is_contr C] : is_surjective f :=
λb, is_exact.ker_in_im H b !is_prop.elim

section chain_complex
open succ_str chain_complex
definition is_exact_of_is_exact_at {N : succ_str} {A : chain_complex N} {n : N}
  (H : is_exact_at A n) : is_exact (cc_to_fn A (S n)) (cc_to_fn A n) :=
is_exact.mk (cc_is_chain_complex A n) H
end chain_complex

structure is_short_exact {A B : Type} {C : Type*} (f : A → B) (g : B → C) :=
  (is_emb    : is_embedding f)
  (im_in_ker : Π(a:A), g (f a) = pt)
  (ker_in_im : Π(b:B), (g b = pt) → image f b)
  (is_surj   : is_surjective g)

structure is_short_exact_t {A B : Type} {C : Type*} (f : A → B) (g : B → C) :=
  (is_emb    : is_embedding f)
  (im_in_ker : Π(a:A), g (f a) = pt)
  (ker_in_im : Π(b:B), (g b = pt) → fiber f b)
  (is_surj   : is_split_surjective g)

lemma is_short_exact_of_is_exact {X A B C Y : Group}
  (k : X →g A) (f : A →g B) (g : B →g C) (l : C →g Y)
  (hX : is_contr X) (hY : is_contr Y)
  (kf : is_exact k f) (fg : is_exact f g) (gl : is_exact g l) : is_short_exact f g :=
begin
  constructor,
  { apply to_is_embedding_homomorphism, intro a p,
    induction is_exact.ker_in_im kf a p with x q,
    exact q⁻¹ ⬝ ap k !is_prop.elim ⬝ to_respect_one k },
  { exact is_exact.im_in_ker fg },
  { exact is_exact.ker_in_im fg },
  { intro c, exact is_exact.ker_in_im gl c !is_prop.elim },
end

lemma is_short_exact_equiv {A B A' B' : Type} {C C' : Type*}
  {f' : A' → B'} {g' : B' → C'} (f : A → B) (g : B → C)
  (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃* C')
  (h₁ : hsquare f f' eA eB) (h₂ : hsquare g g' eB eC)
  (H : is_short_exact f' g') : is_short_exact f g :=
begin
  constructor,
  { apply is_embedding_homotopy_closed_rev (homotopy_top_of_hsquare h₁),
    apply is_embedding_compose, apply is_embedding_of_is_equiv,
    apply is_embedding_compose, apply is_short_exact.is_emb H, apply is_embedding_of_is_equiv },
  { intro a, refine homotopy_top_of_hsquare' (hhconcat h₁ h₂) a ⬝ _,
    refine ap eC⁻¹ _ ⬝ respect_pt eC⁻¹ᵉ*, exact is_short_exact.im_in_ker H (eA a) },
  { intro b p, note q := eq_of_inv_eq ((homotopy_top_of_hsquare' h₂ b)⁻¹ ⬝ p) ⬝ respect_pt eC,
    induction is_short_exact.ker_in_im H (eB b) q with a' r,
    apply image.mk (eA⁻¹ a'),
    exact eq_of_fn_eq_fn eB ((homotopy_top_of_hsquare h₁⁻¹ʰᵗʸᵛ a')⁻¹ ⬝ r) },
  { apply is_surjective_homotopy_closed_rev (homotopy_top_of_hsquare' h₂),
    apply is_surjective_compose, apply is_surjective_of_is_equiv,
    apply is_surjective_compose, apply is_short_exact.is_surj H, apply is_surjective_of_is_equiv }
end

lemma is_exact_of_is_short_exact {A B : Type} {C : Type*}
  {f : A → B} {g : B → C} (H : is_short_exact f g) : is_exact f g :=
begin
  constructor,
  { exact is_short_exact.im_in_ker H },
  { exact is_short_exact.ker_in_im H }
end

end algebra
