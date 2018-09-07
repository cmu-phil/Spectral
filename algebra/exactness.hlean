/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Short exact sequences
-/
import homotopy.chain_complex eq2 .quotient_group
open pointed is_trunc equiv is_equiv eq algebra group trunc function fiber sigma property

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

definition is_contr_middle_of_is_exact {A B : Type} {C : Type*} {f : A → B} {g : B → C}
  (H : is_exact f g) [is_contr A] [is_set B] [is_contr C] : is_contr B :=
begin
  apply is_contr.mk (f pt),
  intro b,
  induction is_exact.ker_in_im H b !is_prop.elim,
  exact ap f !is_prop.elim ⬝ p
end

definition is_surjective_of_is_exact_of_is_contr {A B : Type} {C : Type*} {f : A → B} {g : B → C}
  (H : is_exact f g) [is_contr C] : is_surjective f :=
λb, is_exact.ker_in_im H b !is_prop.elim

definition is_embedding_of_is_exact_g {A B C : Group} {g : B →g C} {f : A →g B}
  (gf : is_exact_g f g) [is_contr A] : is_embedding g :=
begin
  apply to_is_embedding_homomorphism, intro a p,
  induction is_exact.ker_in_im gf a p with x q,
  exact q⁻¹ ⬝ ap f !is_prop.elim ⬝ to_respect_one f
end

definition map_left_of_is_exact {G₃' G₃ G₂ : Type} {G₁ : Type*}
  {g : G₃ → G₂} {g' : G₃' → G₂} {f : G₂ → G₁} (H1 : is_exact g f) (H2 : is_exact g' f)
  (Hg' : is_embedding g') : G₃ → G₃' :=
begin
  intro a,
  have fiber g' (g a),
  begin
    have is_prop (fiber g' (g a)), from !is_prop_fiber_of_is_embedding,
    induction is_exact.ker_in_im H2 (g a) (is_exact.im_in_ker H1 a) with a' p,
    exact fiber.mk a' p
  end,
  exact point this
end

definition map_left_of_is_exact_compute {G₃' G₃ G₂ : Type} {G₁ : Type*}
  {g : G₃ → G₂} {g' : G₃' → G₂} {f : G₂ → G₁} (H1 : is_exact g f) (H2 : is_exact g' f)
  (Hg' : is_embedding g') (a : G₃) : g' (map_left_of_is_exact H1 H2 Hg' a) = g a :=
@point_eq _ _ g' _ _

definition map_left_of_is_exact_compose {G₃'' G₃' G₃ G₂ : Type} {G₁ : Type*}
  {g : G₃ → G₂} {g' : G₃' → G₂} {g'' : G₃'' → G₂} {f : G₂ → G₁}
  (H1 : is_exact g f) (H2 : is_exact g' f) (H3 : is_exact g'' f)
  (Hg' : is_embedding g') (Hg'' : is_embedding g'') (a : G₃) :
  map_left_of_is_exact H2 H3 Hg'' (map_left_of_is_exact H1 H2 Hg' a) =
  map_left_of_is_exact H1 H3 Hg'' a :=
begin
  refine @is_injective_of_is_embedding _ _ g'' _ _ _ _,
  refine !map_left_of_is_exact_compute ⬝ _ ⬝ !map_left_of_is_exact_compute⁻¹,
  exact map_left_of_is_exact_compute H1 H2 Hg' a
end

definition map_left_of_is_exact_id {G₃ G₂ : Type} {G₁ : Type*}
  {g : G₃ → G₂} {f : G₂ → G₁} (H1 : is_exact g f) (Hg : is_embedding g) (a : G₃) :
  map_left_of_is_exact H1 H1 Hg a = a :=
begin
  refine @is_injective_of_is_embedding _ _ g _ _ _ _,
  exact map_left_of_is_exact_compute H1 H1 Hg a
end

definition map_left_of_is_exact_homotopy {G₃' G₃ G₂ : Type} {G₁ : Type*}
  {g : G₃ → G₂} {g' g'' : G₃' → G₂} {f : G₂ → G₁} (H1 : is_exact g f) (H2 : is_exact g' f)
  (H3 : is_exact g'' f) (Hg' : is_embedding g') (Hg'' : is_embedding g'') (p : g' ~ g'') :
  map_left_of_is_exact H1 H2 Hg' ~ map_left_of_is_exact H1 H3 Hg'' :=
begin
  intro a,
  refine @is_injective_of_is_embedding _ _ g' _ _ _ _,
  exact !map_left_of_is_exact_compute ⬝ (!p ⬝ !map_left_of_is_exact_compute)⁻¹,
end

definition homomorphism_left_of_is_exact_g {G₃' G₃ G₂ G₁ : Group}
  {g : G₃ →g G₂} {g' : G₃' →g G₂} {f : G₂ →g G₁} (H1 : is_exact_g g f) (H2 : is_exact_g g' f)
  (Hg' : is_embedding g') : G₃ →g G₃' :=
begin
  apply homomorphism.mk (map_left_of_is_exact H1 H2 Hg'),
  { intro a a', refine @is_injective_of_is_embedding _ _ g' _ _ _ _,
    exact !point_eq ⬝ to_respect_mul g a a' ⬝
      (to_respect_mul g' _ _ ⬝ ap011 mul !point_eq !point_eq)⁻¹ }
end

definition isomorphism_left_of_is_exact_g {G₃' G₃ G₂ G₁ : Group}
  {g : G₃ →g G₂} {g' : G₃' →g G₂} {f : G₂ →g G₁} (H1 : is_exact g f) (H2 : is_exact g' f)
  (Hg : is_embedding g) (Hg' : is_embedding g') : G₃ ≃g G₃' :=
begin
  fapply isomorphism.mk, exact homomorphism_left_of_is_exact_g H1 H2 Hg',
  fapply adjointify, exact homomorphism_left_of_is_exact_g H2 H1 Hg,
  { intro a, refine @is_injective_of_is_embedding _ _ g' _ _ _ _,
    refine map_left_of_is_exact_compute H1 H2 Hg' _ ⬝ map_left_of_is_exact_compute H2 H1 Hg a },
  { intro a, refine @is_injective_of_is_embedding _ _ g _ _ _ _,
    refine map_left_of_is_exact_compute H2 H1 Hg _ ⬝ map_left_of_is_exact_compute H1 H2 Hg' a },
end

definition is_exact_incl_of_subgroup {G H : Group} (f : G →g H) :
  is_exact (incl_of_subgroup (kernel f)) f :=
begin
  apply is_exact.mk,
  { intro x, cases x with x p, exact p },
  { intro x p, exact image.mk ⟨x, p⟩ idp }
end

definition isomorphism_kernel_of_is_exact {G₄ G₃ G₂ G₁ : Group}
  {h : G₄ →g G₃} {g : G₃ →g G₂} {f : G₂ →g G₁} (H1 : is_exact h g) (H2 : is_exact g f)
  (HG : is_contr G₄) : G₃ ≃g Kernel f :=
isomorphism_left_of_is_exact_g H2 (is_exact_incl_of_subgroup f)
  (is_embedding_of_is_exact_g H1) (is_embedding_incl_of_subgroup _)

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
  (kf : is_exact_g k f) (fg : is_exact_g f g) (gl : is_exact_g g l) : is_short_exact f g :=
begin
  constructor,
  { exact is_embedding_of_is_exact_g kf },
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
    exact inj eB ((homotopy_top_of_hsquare h₁⁻¹ʰᵗʸᵛ a')⁻¹ ⬝ r) },
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

lemma is_equiv_left_of_is_short_exact {A B C : Group} {f : A →g B} {g : B →g C}
  (H : is_short_exact f g) (HC : is_contr C) : is_equiv f :=
begin
  apply is_equiv_of_is_surjective_of_is_embedding,
    exact is_short_exact.is_emb H,
    apply is_surjective_of_is_exact_of_is_contr, exact is_exact_of_is_short_exact H
end

lemma is_equiv_right_of_is_short_exact {A B C : Group} {f : A →g B} {g : B →g C}
  (H : is_short_exact f g) (HA : is_contr A) : is_equiv g :=
begin
  apply is_equiv_of_is_surjective_of_is_embedding,
    apply is_embedding_of_is_exact_g, exact is_exact_of_is_short_exact H,
    exact is_short_exact.is_surj H
end

definition is_contr_right_of_is_short_exact {A B : Type} {C : Type*} {f : A → B} {g : B → C}
  (H : is_short_exact f g) (HB : is_contr B) (HC : is_set C) : is_contr C :=
is_contr_of_is_surjective g (is_short_exact.is_surj H) HB HC

definition is_contr_left_of_is_short_exact {A B : Type} {C : Type*} {f : A → B} {g : B → C}
  (H : is_short_exact f g) (HB : is_contr B) (a₀ : A) : is_contr A :=
is_contr_of_is_embedding f (is_short_exact.is_emb H) _ a₀

/- TODO: move and remove other versions -/

  definition is_surjective_qg_map {A : Group} (N : property A) [is_normal_subgroup A N] :
    is_surjective (qg_map N) :=
  begin
    intro x, induction x,
    fapply image.mk,
    exact a, reflexivity,
    apply is_prop.elimo
  end

  definition is_surjective_ab_qg_map {A : AbGroup} (N : property A) [is_normal_subgroup A N] :
    is_surjective (ab_qg_map N) :=
  is_surjective_ab_qg_map _

  definition qg_map_eq_one {A : Group} {K : property A} [is_normal_subgroup A K] (g : A)
      (H : g ∈ K) :
    qg_map K g = 1 :=
  begin
    apply set_quotient.eq_of_rel,
    have e : g * 1⁻¹ = g,
    from calc
      g * 1⁻¹ = g * 1 : one_inv
        ...   = g : mul_one,
    exact transport (λx, K x) e⁻¹ H
  end

  definition ab_qg_map_eq_one {A : AbGroup} {K : property A} [is_subgroup A K] (g : A)
      (H : g ∈ K) :
    ab_qg_map K g = 1 :=
  ab_qg_map_eq_one g H

definition is_short_exact_normal_subgroup {G : Group} (S : property G) [is_normal_subgroup G S] :
  is_short_exact (incl_of_subgroup S) (qg_map S) :=
begin
  fconstructor,
  { exact is_embedding_incl_of_subgroup S },
  { intro a, fapply qg_map_eq_one, induction a with b p, exact p },
  { intro b p, fapply image.mk,
    { apply sigma.mk b, fapply rel_of_qg_map_eq_one, exact p },
    reflexivity },
  { exact is_surjective_qg_map S },
end

end algebra
