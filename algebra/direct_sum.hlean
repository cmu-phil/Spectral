/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import .quotient_group .free_commutative_group .product_group

open eq is_equiv algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops

namespace group

  section

    parameters {I : Type} [is_set I] (Y : I → AbGroup)
    variables {A' : AbGroup} {Y' : I → AbGroup}

    definition dirsum_carrier : AbGroup := free_ab_group (Σi, Y i)
    local abbreviation ι [constructor] := @free_ab_group_inclusion
    inductive dirsum_rel : dirsum_carrier → Type :=
    | rmk : Πi y₁ y₂, dirsum_rel (ι ⟨i, y₁⟩ * ι ⟨i, y₂⟩ *  (ι ⟨i, y₁ * y₂⟩)⁻¹)

    definition dirsum : AbGroup := quotient_ab_group_gen dirsum_carrier (λg, ∥dirsum_rel g∥)

    -- definition dirsum_carrier_incl [constructor] (i : I) : Y i →g dirsum_carrier :=

    definition dirsum_incl [constructor] (i : I) : Y i →g dirsum :=
    homomorphism.mk (λy, class_of (ι ⟨i, y⟩))
      begin intro g h, symmetry, apply gqg_eq_of_rel, apply tr, apply dirsum_rel.rmk end

    parameter {Y}
    definition dirsum.rec {P : dirsum → Type} [H : Πg, is_prop (P g)]
      (h₁ : Πi (y : Y i), P (dirsum_incl i y)) (h₂ : P 1) (h₃ : Πg h, P g → P h → P (g * h)) :
      Πg, P g :=
    begin
      refine @set_quotient.rec_prop _ _ _ H _,
      refine @set_quotient.rec_prop _ _ _ (λx, !H) _,
      esimp, intro l, induction l with s l ih,
        exact h₂,
      induction s with v v,
        induction v with i y,
        exact h₃ _ _ (h₁ i y) ih,
      induction v with i y,
      refine h₃ (gqg_map _ _ (class_of [inr ⟨i, y⟩])) _ _ ih,
      refine transport P _ (h₁ i y⁻¹),
      refine _ ⬝ !one_mul,
      refine _ ⬝ ap (λx, mul x _) (to_respect_zero (dirsum_incl i)),
      apply gqg_eq_of_rel',
      apply tr, esimp,
      refine transport dirsum_rel _ (dirsum_rel.rmk i y⁻¹ y),
      rewrite [mul.left_inv, mul.assoc],
    end

    definition dirsum_homotopy {φ ψ : dirsum →g A'}
      (h : Πi (y : Y i), φ (dirsum_incl i y) = ψ (dirsum_incl i y)) : φ ~ ψ :=
    begin
      refine dirsum.rec _ _ _,
          exact h,
        refine !to_respect_zero ⬝ !to_respect_zero⁻¹,
      intro g₁ g₂ h₁ h₂, rewrite [* to_respect_mul, h₁, h₂]
    end

    definition dirsum_elim_resp_quotient (f : Πi, Y i →g A') (g : dirsum_carrier)
      (r : ∥dirsum_rel g∥) : free_ab_group_elim (λv, f v.1 v.2) g = 1 :=
    begin
      induction r with r, induction r,
      rewrite [to_respect_mul, to_respect_inv, to_respect_mul, ▸*, ↑foldl, *one_mul,
        to_respect_mul], apply mul.right_inv
    end

    definition dirsum_elim [constructor] (f : Πi, Y i →g A') : dirsum →g A' :=
    gqg_elim _ (free_ab_group_elim (λv, f v.1 v.2)) (dirsum_elim_resp_quotient f)

    definition dirsum_elim_compute (f : Πi, Y i →g A') (i : I) (y : Y i) :
      dirsum_elim f (dirsum_incl i y) = f i y :=
    begin
      apply one_mul
    end

    definition dirsum_elim_unique (f : Πi, Y i →g A') (k : dirsum →g A')
      (H : Πi, k ∘g dirsum_incl i ~ f i) : k ~ dirsum_elim f :=
    begin
      apply gqg_elim_unique,
      apply free_ab_group_elim_unique,
      intro x, induction x with i y, exact H i y
    end

  end

  definition binary_dirsum (G H : AbGroup) : dirsum (bool.rec G H) ≃g G ×ag H :=
  let branch := bool.rec G H in
  let to_hom := (dirsum_elim (bool.rec (product_inl G H) (product_inr G H))
                : dirsum (bool.rec G H) →g G ×ag H) in
  let from_hom := (Group_sum_elim (dirsum (bool.rec G H))
                    (dirsum_incl branch bool.ff) (dirsum_incl branch bool.tt)
                  : G ×g H →g dirsum branch) in
  begin
    fapply isomorphism.mk,
    { exact dirsum_elim (bool.rec (product_inl G H) (product_inr G H)) },
    fapply adjointify,
    { exact from_hom },
    { intro gh, induction gh with g h,
        exact prod_eq (mul_one (1 * g) ⬝ one_mul g) (ap (λ o, o * h) (mul_one 1) ⬝ one_mul h) },
    { refine dirsum.rec _ _ _,
      { intro b x,
        refine ap from_hom (dirsum_elim_compute (bool.rec (product_inl G H) (product_inr G H)) b x) ⬝ _,
        induction b,
        { exact ap (λ y, dirsum_incl branch bool.ff x * y) (to_respect_one (dirsum_incl branch bool.tt)) ⬝ mul_one _ },
        { exact ap (λ y, y * dirsum_incl branch bool.tt x) (to_respect_one (dirsum_incl branch bool.ff)) ⬝ one_mul _ }
      },
      { refine ap from_hom (to_respect_one to_hom) ⬝ to_respect_one from_hom },
      { intro g h gβ hβ,
        refine ap from_hom (to_respect_mul to_hom _ _) ⬝ to_respect_mul from_hom _ _ ⬝ _,
        exact ap011 mul gβ hβ
      }
    }
  end

  variables {I J : Set} {Y Y' Y'' : I → AbGroup}

  definition dirsum_functor [constructor] (f : Πi, Y i →g Y' i) : dirsum Y →g dirsum Y' :=
  dirsum_elim (λi, dirsum_incl Y' i ∘g f i)

  theorem dirsum_functor_compose (f' : Πi, Y' i →g Y'' i) (f : Πi, Y i →g Y' i) :
    dirsum_functor f' ∘a dirsum_functor f ~ dirsum_functor (λi, f' i ∘a f i) :=
  begin
    apply dirsum_homotopy,
    intro i y, reflexivity,
  end

  variable (Y)
  definition dirsum_functor_gid : dirsum_functor (λi, gid (Y i)) ~ gid (dirsum Y) :=
  begin
    apply dirsum_homotopy,
    intro i y, reflexivity,
  end
  variable {Y}

  definition dirsum_functor_mul (f f' : Πi, Y i →g Y' i) :
    homomorphism_mul (dirsum_functor f) (dirsum_functor f') ~
    dirsum_functor (λi, homomorphism_mul (f i) (f' i)) :=
  begin
    apply dirsum_homotopy,
    intro i y, exact sorry
  end

  definition dirsum_functor_homotopy {f f' : Πi, Y i →g Y' i} (p : f ~2 f') :
    dirsum_functor f ~ dirsum_functor f' :=
  begin
    apply dirsum_homotopy,
    intro i y, exact sorry
  end

  definition dirsum_functor_left [constructor] (f : J → I) : dirsum (Y ∘ f) →g dirsum Y :=
  dirsum_elim (λj, dirsum_incl Y (f j))

end group
