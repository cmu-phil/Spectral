/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Short exact sequences
-/
import .quotient_group
open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     is_trunc function sphere unit sum prod

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
