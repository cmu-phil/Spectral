/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import algebra.group_theory hit.set_quotient types.list types.sum ..move_to_lib

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod sum list trunc function equiv
     prod.ops decidable is_equiv

universe variable u

namespace group

  variables {G G' : Group} {g g' h h' k : G} {A B : AbGroup}

  /- Free Group of a set -/
  variables (X : Type) [is_set X] {l l' : list (X ⊎ X)}
  namespace free_group

  inductive free_group_rel : list (X ⊎ X) → list (X ⊎ X) → Type :=
  | rrefl   : Πl, free_group_rel l l
  | cancel1 : Πx, free_group_rel [inl x, inr x] []
  | cancel2 : Πx, free_group_rel [inr x, inl x] []
  | resp_append : Π{l₁ l₂ l₃ l₄}, free_group_rel l₁ l₂ → free_group_rel l₃ l₄ →
                             free_group_rel (l₁ ++ l₃) (l₂ ++ l₄)
  | rtrans : Π{l₁ l₂ l₃}, free_group_rel l₁ l₂ → free_group_rel l₂ l₃ →
                             free_group_rel l₁ l₃

  open free_group_rel
  local abbreviation R [reducible] := free_group_rel
  attribute free_group_rel.rrefl [refl]

  definition free_group_carrier [reducible] : Type := set_quotient (λx y, ∥R X x y∥)
  local abbreviation FG := free_group_carrier

  definition is_reflexive_R : is_reflexive (λx y, ∥R X x y∥) :=
  begin constructor, intro s, apply tr, unfold R end
  local attribute is_reflexive_R [instance]

  variable {X}
  theorem rel_respect_flip (r : R X l l') : R X (map sum.flip l) (map sum.flip l') :=
  begin
    induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
    { reflexivity},
    { repeat esimp [map], exact cancel2 x},
    { repeat esimp [map], exact cancel1 x},
    { rewrite [+map_append], exact resp_append IH₁ IH₂},
    { exact rtrans IH₁ IH₂}
  end

  theorem rel_respect_reverse (r : R X l l') : R X (reverse l) (reverse l') :=
  begin
    induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂,
    { reflexivity},
    { repeat esimp [map], exact cancel2 x},
    { repeat esimp [map], exact cancel1 x},
    { rewrite [+reverse_append], exact resp_append IH₂ IH₁},
    { exact rtrans IH₁ IH₂}
  end

  definition free_group_one [constructor] : FG X := class_of []
  definition free_group_inv [unfold 3] : FG X → FG X :=
  quotient_unary_map (reverse ∘ map sum.flip)
                     (λl l', trunc_functor -1 (rel_respect_reverse ∘ rel_respect_flip))
  definition free_group_mul [unfold 3 4] : FG X → FG X → FG X :=
  quotient_binary_map append (λl l', trunc.elim (λr m m', trunc.elim (λs, tr (resp_append r s))))

  section
  local notation 1 := free_group_one
  local postfix ⁻¹ := free_group_inv
  local infix * := free_group_mul

  theorem free_group_mul_assoc (g₁ g₂ g₃ : FG X) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    refine set_quotient.rec_prop _ g₁,
    refine set_quotient.rec_prop _ g₂,
    refine set_quotient.rec_prop _ g₃,
    clear g₁ g₂ g₃, intro g₁ g₂ g₃,
    exact ap class_of !append.assoc
  end

  theorem free_group_one_mul (g : FG X) : 1 * g = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !append_nil_left
  end

  theorem free_group_mul_one (g : FG X) : g * 1 = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !append_nil_right
  end

  theorem free_group_mul_left_inv (g : FG X) : g⁻¹ * g = 1 :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    apply eq_of_rel, apply tr,
    induction g with s l IH,
    { reflexivity},
    { rewrite [▸*, map_cons, reverse_cons, concat_append],
      refine rtrans _ IH,
      apply resp_append, reflexivity,
      change R X ([flip s, s] ++ l) ([] ++ l),
      apply resp_append,
        induction s, apply cancel2, apply cancel1,
        reflexivity}
  end

  end
  end free_group open free_group
--  export [reduce_hints] free_group
  variables (X)
  definition group_free_group [constructor] : group (free_group_carrier X) :=
  group.mk _ free_group_mul free_group_mul_assoc free_group_one free_group_one_mul
           free_group_mul_one free_group_inv free_group_mul_left_inv

  definition free_group [constructor] : Group :=
  Group.mk _ (group_free_group X)

  /- The universal property of the free group -/
  variables {X G}
  definition free_group_inclusion [constructor] (x : X) : free_group X :=
  class_of [inl x]

  definition fgh_helper [unfold 6] (f : X → G) (g : G) (x : X ⊎ X) : G :=
  g * sum.rec (λx, f x) (λx, (f x)⁻¹) x

  theorem fgh_helper_respect_rel (f : X → G) (r : free_group_rel X l l')
    : Π(g : G), foldl (fgh_helper f) g l = foldl (fgh_helper f) g l' :=
  begin
    induction r with l x x l₁ l₂ l₃ l₄ r₁ r₂ IH₁ IH₂ l₁ l₂ l₃ r₁ r₂ IH₁ IH₂: intro g,
    { reflexivity},
    { unfold [foldl], apply mul_inv_cancel_right},
    { unfold [foldl], apply inv_mul_cancel_right},
    { rewrite [+foldl_append, IH₁, IH₂]},
    { exact !IH₁ ⬝ !IH₂}
  end

  theorem fgh_helper_mul (f : X → G) (l)
    : Π(g : G), foldl (fgh_helper f) g l = g * foldl (fgh_helper f) 1 l :=
  begin
    induction l with s l IH: intro g,
    { unfold [foldl], exact !mul_one⁻¹},
    { rewrite [+foldl_cons, IH], refine _ ⬝ (ap (λx, g * x) !IH⁻¹),
      rewrite [-mul.assoc, ↑fgh_helper, one_mul]}
  end

  definition free_group_hom [constructor] (f : X → G) : free_group X →g G :=
  begin
    fapply homomorphism.mk,
    { intro g, refine set_quotient.elim _ _ g,
      { intro l, exact foldl (fgh_helper f) 1 l},
      { intro l l' r, esimp at *, refine trunc.rec _ r, clear r, intro r,
        exact fgh_helper_respect_rel f r 1}},
    { refine set_quotient.rec_prop _, intro l, refine set_quotient.rec_prop _, intro l',
      esimp, refine !foldl_append ⬝ _, esimp, apply fgh_helper_mul}
  end

  definition free_group_hom_eq [constructor] {φ ψ : free_group X →g G}
    (H : Πx, φ (free_group_inclusion x) = ψ (free_group_inclusion x)) : φ ~ ψ :=
  begin
    refine set_quotient.rec_prop _, intro l,
    induction l with s l IH,
    { exact respect_one φ ⬝ (respect_one ψ)⁻¹ },
    { refine respect_mul φ (class_of [s]) (class_of l) ⬝ _ ⬝
        (respect_mul ψ (class_of [s]) (class_of l))⁻¹,
      refine ap011 mul _ IH, induction s with x x, exact H x,
      refine respect_inv φ (class_of [inl x]) ⬝ ap inv (H x) ⬝
        (respect_inv ψ (class_of [inl x]))⁻¹ }
  end

  definition fn_of_free_group_hom [unfold_full] (φ : free_group X →g G) : X → G :=
  φ ∘ free_group_inclusion

  variables (X G)
  definition free_group_hom_equiv_fn : (free_group X →g G) ≃ (X → G) :=
  begin
    fapply equiv.MK,
    { exact fn_of_free_group_hom},
    { exact free_group_hom},
    { intro f, apply eq_of_homotopy, intro x, esimp, unfold [foldl], apply one_mul},
    { intro φ, apply homomorphism_eq, apply free_group_hom_eq, intro x, apply one_mul }
  end

end group

/- alternative definition of free group on a set with decidable equality -/

namespace list

variables {X : Type.{u}} {v w : X ⊎ X} {l : list (X ⊎ X)}

inductive is_reduced {X : Type} : list (X ⊎ X) → Type :=
| nil       : is_reduced []
| singleton : Πv, is_reduced [v]
| cons      : Π⦃v w l⦄, sum.flip v ≠ w → is_reduced (w::l) → is_reduced (v::w::l)

definition is_reduced_code (H : is_reduced l) : Type.{u} :=
begin
  cases l with v l, { exact is_reduced.nil = H },
  cases l with w l, { exact is_reduced.singleton v = H },
  exact Σ(pH : sum.flip v ≠ w × is_reduced (w::l)), is_reduced.cons pH.1 pH.2 = H
end

definition is_reduced_encode (H : is_reduced l) : is_reduced_code H :=
begin
  induction H with v v w l p Hl IH,
  { exact idp },
  { exact idp },
  { exact ⟨(p, Hl), idp⟩ }
end

definition is_prop_is_reduced (l : list (X ⊎ X)) : is_prop (is_reduced l) :=
begin
  apply is_prop.mk, intro H₁ H₂, induction H₁ with v v w l p Hl IH,
  { exact is_reduced_encode H₂ },
  { exact is_reduced_encode H₂ },
  { cases is_reduced_encode H₂ with pH' q, cases pH' with p' Hl', esimp at q,
    subst q, exact ap011 (λx y, is_reduced.cons x y) !is_prop.elim (IH Hl') }
end

definition rlist (X : Type) : Type :=
Σ(l : list (X ⊎ X)), is_reduced l

local attribute [instance] is_prop_is_reduced
definition rlist_eq {l l' : rlist X} (p : l.1 = l'.1) : l = l' :=
subtype_eq p

definition is_trunc_rlist {n : ℕ₋₂} {X : Type} (H : is_trunc (n.+2) X) :
  is_trunc (n.+2) (rlist X) :=
begin
  apply is_trunc_sigma, { apply is_trunc_list, apply is_trunc_sum },
  intro l, exact is_trunc_succ_of_is_prop _ _ _
end

definition is_reduced_invert (v : X ⊎ X) : is_reduced (v::l) → is_reduced l :=
begin
  assert H : Π⦃l'⦄, is_reduced l' → l' = v::l → is_reduced l,
  { intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
    { cases p },
    { cases cons_eq_cons p with q r, subst r, apply is_reduced.nil },
    { cases cons_eq_cons p with q r, subst r, exact Hl' }},
  intro Hl, exact H Hl idp
end

definition is_reduced_invert_rev (v : X ⊎ X) : is_reduced (l++[v]) → is_reduced l :=
begin
  assert H : Π⦃l'⦄, is_reduced l' → l' = l++[v] → is_reduced l,
  { intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
    { induction l: cases p },
    { induction l with v'' l IH, apply is_reduced.nil, esimp [append] at p,
      cases cons_eq_cons p with q r, induction l: cases r },
    { induction l with v'' l IH', cases p, induction l with v''' l IH'',
      apply is_reduced.singleton, do 2 esimp [append] at p, cases cons_eq_cons p with q r,
      cases cons_eq_cons r with r₁ r₂, subst r₁, subst q, subst r₂,
      apply is_reduced.cons p' (IH _ idp) }},
  intro Hl, exact H Hl idp
end

definition rnil [constructor] : rlist X :=
⟨[], !is_reduced.nil⟩

definition rsingleton [constructor] (x : X ⊎ X) : rlist X :=
⟨[x], !is_reduced.singleton⟩

definition is_reduced_doubleton [constructor] {x y : X ⊎ X} (p : flip x ≠ y) :
  is_reduced [x, y] :=
is_reduced.cons p !is_reduced.singleton

definition rdoubleton [constructor] {x y : X ⊎ X} (p : flip x ≠ y) : rlist X :=
⟨[x, y], is_reduced_doubleton p⟩

definition is_reduced_concat (Hn : sum.flip v ≠ w) (Hl : is_reduced (concat v l)) :
  is_reduced (concat w (concat v l)) :=
begin
  assert H : Π⦃l'⦄, is_reduced l' → l' = concat v l → is_reduced (concat w l'),
  { clear Hl, intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
    { exfalso, exact concat_neq_nil _ _ p⁻¹ },
    { cases concat_eq_singleton p⁻¹ with q r, subst q,
      exact is_reduced_doubleton Hn },
    { do 2 esimp [concat], apply is_reduced.cons p', cases l with x l,
      { cases p },
      { apply IH l, esimp [concat] at p, revert p, generalize concat v l, intro l'' p,
        cases cons_eq_cons p with q r, exact r }}},
  exact H Hl idp
end

definition is_reduced_reverse (H : is_reduced l) : is_reduced (reverse l) :=
begin
  induction H with v v w l p Hl IH,
  { apply is_reduced.nil },
  { apply is_reduced.singleton },
  { refine is_reduced_concat _ IH, intro q, apply p, subst q, apply flip_flip }
end

definition rreverse [constructor] (l : rlist X) : rlist X := ⟨reverse l.1, is_reduced_reverse l.2⟩

definition rreverse_rreverse (l : rlist X) : rreverse (rreverse l) = l :=
subtype_eq (reverse_reverse l.1)

definition is_reduced_flip (H : is_reduced l) : is_reduced (map flip l) :=
begin
  induction H with v v w l p Hl IH,
  { apply is_reduced.nil },
  { apply is_reduced.singleton },
  { refine is_reduced.cons _ IH, intro q, apply p, exact !flip_flip⁻¹ ⬝ ap flip q ⬝ !flip_flip }
end

definition rflip [constructor] (l : rlist X) : rlist X := ⟨map flip l.1, is_reduced_flip l.2⟩

definition rcons' [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X)) : list (X ⊎ X) :=
begin
  cases l with w l,
  { exact [v] },
  { exact if q : sum.flip v = w then l else v::w::l }
end

definition is_reduced_rcons [decidable_eq X] (v : X ⊎ X) (Hl : is_reduced l) :
  is_reduced (rcons' v l) :=
begin
  cases l with w l, apply is_reduced.singleton,
  apply dite (sum.flip v = w): intro q,
  { have is_set (X ⊎ X), from !is_trunc_sum,
    rewrite [↑rcons', dite_true q _], exact is_reduced_invert w Hl },
  { rewrite [↑rcons', dite_false q], exact is_reduced.cons q Hl, }
end

definition rcons [constructor] [decidable_eq X] (v : X ⊎ X) (l : rlist X) : rlist X :=
⟨rcons' v l.1, is_reduced_rcons v l.2⟩

definition rcons_eq [decidable_eq X] : is_reduced (v::l) → rcons' v l = v :: l :=
begin
  assert H : Π⦃l'⦄, is_reduced l' → l' = v::l → rcons' v l = l',
  { intro l' Hl', revert l, induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
    { cases p },
    { cases cons_eq_cons p with q r, subst r, cases p, reflexivity },
    { cases cons_eq_cons p with q r, subst q, subst r, rewrite [↑rcons', dite_false p'], }},
  intro Hl, exact H Hl idp
end

definition rcons_eq2 [decidable_eq X] (H : is_reduced (v::l)) :
  ⟨v :: l, H⟩ = rcons v ⟨l, is_reduced_invert _ H⟩ :=
subtype_eq (rcons_eq H)⁻¹

definition rcons_rcons_eq [decidable_eq X] (p : flip v = w) (l : rlist X) :
  rcons v (rcons w l) = l :=
begin
  have is_set (X ⊎ X), from !is_trunc_sum,
  induction l with l Hl,
  apply rlist_eq, esimp,
  induction l with u l IH,
  { exact dite_true p _ },
  { apply dite (sum.flip w = u): intro q,
    { rewrite [↑rcons' at {1}, dite_true q _], subst p, induction (!flip_flip⁻¹ ⬝ q),
      exact rcons_eq Hl },
    { rewrite [↑rcons', dite_false q, dite_true p _] }}
end

definition rlist.rec [decidable_eq X] {P : rlist X → Type}
  (P1 : P rnil) (Pcons : Πv l, P l → P (rcons v l)) (l : rlist X) : P l :=
begin
  induction l with l Hl, induction Hl with v v w l p Hl IH,
  { exact P1 },
  { exact Pcons v rnil P1 },
  { exact transport P (subtype_eq (rcons_eq (is_reduced.cons p Hl))) (Pcons v ⟨w :: l, Hl⟩ IH) }
end

definition reduce_list' [decidable_eq X] (l : list (X ⊎ X)) : list (X ⊎ X) :=
begin
  induction l with v l IH,
  { exact [] },
  { exact rcons' v IH }
end

definition is_reduced_reduce_list [decidable_eq X] (l : list (X ⊎ X)) :
  is_reduced (reduce_list' l) :=
begin
  induction l with v l IH, apply is_reduced.nil,
  apply is_reduced_rcons, exact IH
end

definition reduce_list [constructor] [decidable_eq X] (l : list (X ⊎ X)) : rlist X :=
⟨reduce_list' l, is_reduced_reduce_list l⟩

definition rappend' [decidable_eq X] (l : list (X ⊎ X)) (l' : rlist X) : rlist X := foldr rcons l' l
definition rappend_rcons' [decidable_eq X] (x : X ⊎ X) (l₁ : list (X ⊎ X)) (l₂ : rlist X) :
  rappend' (rcons' x l₁) l₂ = rcons x (rappend' l₁ l₂) :=
begin
  induction l₁ with x' l₁ IH,
  { reflexivity },
  { apply dite (sum.flip x = x'): intro p,
    { have is_set (X ⊎ X), from !is_trunc_sum, rewrite [↑rcons', dite_true p _],
      exact (rcons_rcons_eq p _)⁻¹ },
    { rewrite [↑rcons', dite_false p] }}
end

definition rappend_cons' [decidable_eq X] (x : X ⊎ X) (l₁ : list (X ⊎ X)) (l₂ : rlist X) :
  rappend' (x::l₁) l₂ = rcons x (rappend' l₁ l₂) :=
idp

definition rappend [decidable_eq X] (l l' : rlist X) : rlist X := rappend' l.1 l'

definition rappend_rcons [decidable_eq X] (x : X ⊎ X) (l₁ l₂ : rlist X) :
  rappend (rcons x l₁) l₂ = rcons x (rappend l₁ l₂) :=
rappend_rcons' x l₁.1 l₂

definition rappend_assoc [decidable_eq X] (l₁ l₂ l₃ : rlist X) :
  rappend (rappend l₁ l₂) l₃ = rappend l₁ (rappend l₂ l₃) :=
begin
  induction l₁ with l₁ h, unfold rappend, clear h, induction l₁ with x l₁ IH,
  { reflexivity },
  { rewrite [rappend_cons', ▸*, rappend_rcons', IH] }
end

definition rappend_rnil [decidable_eq X] (l : rlist X) : rappend l rnil = l :=
begin
  induction l with l H, apply rlist_eq, esimp, induction H with v v w l p Hl IH,
  { reflexivity },
  { reflexivity },
  { rewrite [↑rappend at *, rappend_cons', ↑rcons, IH, ↑rcons', dite_false p] }
end

definition rnil_rappend [decidable_eq X] (l : rlist X) : rappend rnil l = l :=
by reflexivity

definition rsingleton_rappend [decidable_eq X] (x : X ⊎ X) (l : rlist X) :
  rappend (rsingleton x) l = rcons x l :=
by reflexivity

definition rappend_left_inv [decidable_eq X] (l : rlist X) :
  rappend (rflip (rreverse l)) l = rnil :=
begin
  induction l with l H, apply rlist_eq, induction l with x l IH,
  { reflexivity },
  { have is_set (X ⊎ X), from !is_trunc_sum,
    rewrite [↑rappend, ↑rappend', reverse_cons, map_concat, foldr_concat],
    refine ap (λx, (rappend' _ x).1) (rlist_eq (dite_true !flip_flip _)) ⬝
      IH (is_reduced_invert _ H) }
end

definition rappend'_eq [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X)) (H : is_reduced (l ++ [v])) :
  ⟨l ++ [v], H⟩ = rappend' l (rsingleton v) :=
begin
  assert Hlem : Π⦃l'⦄ (Hl' : is_reduced l'), l' = l ++ [v] → rappend' l (rsingleton v) = ⟨l', Hl'⟩,
  { intro l' Hl', clear H, revert l,
    induction Hl' with v' v' w' l' p' Hl' IH: intro l p,
    { induction l: cases p },
    { induction l with v'' l IH,
      { cases cons_eq_cons p with q r, subst q },
      { esimp [append] at p, cases cons_eq_cons p with q r, induction l: cases r }},
    { induction l with v'' l IH', cases p,
      induction l with v''' l IH'',
      { do 2 esimp [append] at p, cases cons_eq_cons p with q r, subst q,
        cases cons_eq_cons r with q r', subst q, subst r', apply subtype_eq, exact dite_false p' },
      { do 2 esimp [append] at p, cases cons_eq_cons p with q r,
        cases cons_eq_cons r with r₁ r₂, subst r₁, subst q, subst r₂,
        rewrite [rappend_cons', IH (w' :: l) idp],
        apply subtype_eq, apply rcons_eq, apply is_reduced.cons p' Hl' }}},
  exact (Hlem H idp)⁻¹
end

definition rappend_eq [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X)) (H : is_reduced (l ++ [v])) :
  ⟨l ++ [v], H⟩ = rappend ⟨l, is_reduced_invert_rev _ H⟩ (rsingleton v) :=
rappend'_eq v l H

definition rreverse_cons [decidable_eq X] (v : X ⊎ X) (l : list (X ⊎ X))
  (H : is_reduced (v :: l)) : rreverse ⟨v::l, H⟩ =
    rappend ⟨reverse l, is_reduced_reverse (is_reduced_invert _ H)⟩ (rsingleton v) :=
begin
  refine dpair_eq_dpair (reverse_cons _ _) !pathover_tr ⬝ _,
  refine dpair_eq_dpair (concat_eq_append _ _) !pathover_tr ⬝ _,
  refine !rappend_eq ⬝ _,
  exact ap (λx, rappend ⟨_, x⟩ _) !is_prop.elim
end

definition rreverse_rcons [decidable_eq X] (v : X ⊎ X) (l : rlist X) :
  rreverse (rcons v l) = rappend (rreverse l) (rsingleton v) :=
begin
  induction l with l Hl, induction l with v' l IH, reflexivity,
  { symmetry, refine ap (λx, rappend x _) !rreverse_cons ⬝ _,
    apply dite (sum.flip v = v'): intro p,
    { have is_set (X ⊎ X), from !is_trunc_sum,
      rewrite [↑rcons, ↑rcons', dpair_eq_dpair (dite_true p _) !pathover_tr ],
      refine !rappend_assoc ⬝ _, refine ap (rappend _) !rsingleton_rappend ⬝ _,
      refine ap (rappend _) (subtype_eq _) ⬝ !rappend_rnil,
      exact dite_true (ap flip p⁻¹ ⬝ flip_flip v) _ },
    { rewrite [↑rcons, ↑rcons', dpair_eq_dpair (dite_false p) !pathover_tr],
      note H1 := is_reduced_reverse (transport is_reduced (dite_false p) (is_reduced_rcons v Hl)),
      rewrite [+reverse_cons at H1, +concat_eq_append at H1],
      note H2 := is_reduced_invert_rev _ H1,
      refine ap (λx, rappend x _) (rappend_eq _ _ H2)⁻¹ ⬝ _,
      refine (rappend_eq _ _ H1)⁻¹ ⬝ _, apply subtype_eq,
      rewrite [-+concat_eq_append] }}

end

definition rlist.rec_rev [decidable_eq X] {P : rlist X → Type}
  (P1 : P rnil) (Pappend : Πl v, P l → P (rappend l (rsingleton v))) : Π(l : rlist X), P l :=
begin
  assert H : Π(l : rlist X), P (rreverse l),
  { refine rlist.rec _ _, exact P1, intro v l p,
    rewrite [rreverse_rcons], apply Pappend, exact p },
  intro l, exact transport P (rreverse_rreverse l) (H (rreverse l))
end

end list open list

namespace group
  open sigma.ops

  variables (X : Type) [decidable_eq X] {G : InfGroup}
  definition group_dfree_group [constructor] : group (rlist X) :=
  group.mk (is_trunc_rlist _) rappend rappend_assoc rnil rnil_rappend rappend_rnil
           (rflip ∘ rreverse) rappend_left_inv

  definition dfree_group [constructor] : Group :=
  Group.mk _ (group_dfree_group X)

  variable {X}
  definition dfree_group_inclusion [constructor] [reducible] (x : X) : dfree_group X :=
  rsingleton (inl x)

  definition rsingleton_inr [constructor] (x : X) :
    rsingleton (inr x) = (dfree_group_inclusion x)⁻¹ :> dfree_group X :=
  by reflexivity

  local attribute [instance] is_prop_is_reduced
  definition dfree_group.rec {P : dfree_group X → Type}
    (P1 : P 1) (Pcons : Πv g, P g → P (rsingleton v * g)) : Π(g : dfree_group X), P g :=
  rlist.rec P1 Pcons

  definition dfree_group.rec_rev {P : dfree_group X → Type}
    (P1 : P 1) (Pcons : Πg v, P g → P (g * rsingleton v)) : Π(g : dfree_group X), P g :=
  rlist.rec_rev P1 Pcons

  -- definition dfree_group.rec2 [constructor] {P : dfree_group X → Type}
  --   (P1 : P 1) (Pcons : Πg x, P g → P (dfree_group_inclusion x * g))
  --   (Pinv : Πg, P g → P g⁻¹) : Π(g : dfree_group X), P g :=
  -- begin
  --   refine dfree_group.rec _ _, exact P1,
  --   intro g v p, induction v with x x, exact Pcons g x p,

  -- end

  definition dfgh_helper [unfold 6] (f : X → G) (g : G) (x : X ⊎ X) : G :=
  g * sum.rec (λx, f x) (λx, (f x)⁻¹) x

  theorem dfgh_helper_mul (f : X → G) (l : list (X ⊎ X))
    : Π(g : G), foldl (dfgh_helper f) g l = g * foldl (dfgh_helper f) 1 l :=
  begin
    induction l with s l IH: intro g,
    { unfold [foldl], exact !mul_one⁻¹},
    { rewrite [+foldl_cons, IH], refine _ ⬝ (ap (λx, g * x) !IH⁻¹),
      rewrite [-mul.assoc, ↑dfgh_helper, one_mul] }
  end

  definition dfgh_helper_rcons (f : X → G) (g : G) (x : X ⊎ X) {l : list (X ⊎ X)} :
    foldl (dfgh_helper f) g (rcons' x l) = foldl (dfgh_helper f) g (x :: l) :=
  begin
    cases l with x' l, reflexivity,
    apply dite (sum.flip x = x'): intro q,
    { have is_set (X ⊎ X), from !is_trunc_sum,
      rewrite [↑rcons', dite_true q _, foldl_cons, foldl_cons, -q],
      induction x with x, rewrite [↑dfgh_helper,mul_inv_cancel_right],
      rewrite [↑dfgh_helper,inv_mul_cancel_right] },
    { rewrite [↑rcons', dite_false q] }
  end

  definition dfgh_helper_rappend (f : X → G) (g : G) (l l' : rlist X) :
    foldl (dfgh_helper f) g (rappend l l').1 = foldl (dfgh_helper f) g (l.1 ++ l'.1) :=
  begin
    revert g, induction l with l lH, unfold rappend, clear lH,
    induction l with v l IH: intro g, reflexivity,
    rewrite [rappend_cons', ↑rcons, dfgh_helper_rcons, foldl_cons, IH]
  end

  local attribute [coercion] InfGroup_of_Group
  definition dfree_group_inf_hom [constructor] (G : InfGroup) (f : X → G) : dfree_group X →∞g G :=
  inf_homomorphism.mk (λx, foldl (dfgh_helper f) 1 x.1)
                      (λl₁ l₂, !dfgh_helper_rappend ⬝ !foldl_append ⬝ !dfgh_helper_mul)

  definition dfree_group_inf_hom_eq [constructor] {G : InfGroup} {φ ψ : dfree_group X →∞g G}
    (H : Πx, φ (dfree_group_inclusion x) = ψ (dfree_group_inclusion x)) : φ ~ ψ :=
  begin
    assert H2 : Πv, φ (rsingleton v) = ψ (rsingleton v),
    { intro v, induction v with x x, exact H x,
      exact to_respect_inv_inf φ _ ⬝ ap inv (H x) ⬝ (to_respect_inv_inf ψ _)⁻¹ },
    refine dfree_group.rec _ _,
    { exact !to_respect_one_inf ⬝ !to_respect_one_inf⁻¹ },
    { intro v g p, exact !to_respect_mul_inf ⬝ ap011 mul (H2 v) p ⬝ !to_respect_mul_inf⁻¹ }
  end

  theorem dfree_group_inf_hom_inclusion [constructor] (G : InfGroup) (f : X → G) (x : X) :
    dfree_group_inf_hom G f (dfree_group_inclusion x) = f x :=
  by rewrite [▸*, foldl_cons, foldl_nil, ↑dfgh_helper, one_mul]

  definition dfree_group_hom [constructor] {G : Group} (f : X → G) : dfree_group X →g G :=
  homomorphism_of_inf_homomorphism (dfree_group_inf_hom G f)

  -- todo: use the inf-version
  definition dfree_group_hom_eq [constructor] {G : Group} {φ ψ : dfree_group X →g G}
    (H : Πx, φ (dfree_group_inclusion x) = ψ (dfree_group_inclusion x)) : φ ~ ψ :=
  begin
    assert H2 : Πv, φ (rsingleton v) = ψ (rsingleton v),
    { intro v, induction v with x x, exact H x,
      exact to_respect_inv φ _ ⬝ ap inv (H x) ⬝ (to_respect_inv ψ _)⁻¹ },
    refine dfree_group.rec _ _,
    { exact !to_respect_one ⬝ !to_respect_one⁻¹ },
    { intro v g p, exact !to_respect_mul ⬝ ap011 mul (H2 v) p ⬝ !to_respect_mul⁻¹ }
  end

  definition is_mul_hom_dfree_group_fun {G : InfGroup} {f : dfree_group X → G}
    (H1 : f 1 = 1) (H2 : Πv g, f (rsingleton v * g) = f (rsingleton v) * f g) : is_mul_hom f :=
  begin
    refine dfree_group.rec _ _,
    { intro g, exact ap f (one_mul g) ⬝ (ap (λx, x * _) H1 ⬝ one_mul (f g))⁻¹ },
    { intro g v p h,
      exact ap f !mul.assoc ⬝ !H2 ⬝ ap (mul _) !p ⬝ (ap (λx, x * _) !H2 ⬝ !mul.assoc)⁻¹ }
  end

  definition dfree_group_hom_of_fun [constructor] {G : InfGroup} (f : dfree_group X → G)
    (H1 : f 1 = 1) (H2 : Πv g, f (rsingleton v * g) = f (rsingleton v) * f g) :
    dfree_group X →∞g G :=
  inf_homomorphism.mk f (is_mul_hom_dfree_group_fun H1 H2)

  variable (X)

  definition free_group_of_dfree_group [constructor] : dfree_group X →g free_group X :=
  dfree_group_hom free_group_inclusion

  definition dfree_group_of_free_group [constructor] : free_group X →g dfree_group X :=
  free_group_hom dfree_group_inclusion

  definition dfree_group_isomorphism : dfree_group X ≃g free_group X :=
  begin
    apply isomorphism.MK (free_group_of_dfree_group X) (dfree_group_of_free_group X),
    { apply free_group_hom_eq, intro x, reflexivity },
    { apply dfree_group_hom_eq, intro x, reflexivity }
  end

end group
