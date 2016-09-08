/-
Copyright (c) 2015 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Basic concepts of group theory
-/

import algebra.group_theory hit.set_quotient types.sigma types.list types.sum

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function
     equiv
namespace group

  /- #Subgroups -/
  /-- Recall that a subtype of a type A is the same thing as a family of mere propositions over A. Thus, we define a subgroup of a group G to be a family of mere propositions over (the underlying type of) G, closed under the constants and operations --/

  /-- Question: Why is this called subgroup_rel. Because it is a unary relation? --/
  structure subgroup_rel.{u} (G : Group.{u}) : Type.{u+1} :=
    (R : G → Prop.{u})
    (Rone : R one)
    (Rmul : Π{g h}, R g → R h → R (g * h))
    (Rinv : Π{g}, R g → R (g⁻¹))

  /-- Every group G has at least two subgroups, the trivial subgroup containing only one, and the full subgroup. --/
  definition trivial_subgroup.{u} (G : Group.{u}) : subgroup_rel.{u} G :=
  begin
    fapply subgroup_rel.mk,
    { intro g, fapply trunctype.mk, exact (g = one), exact _ },
    { esimp },
    { intros g h p q, esimp at *, rewrite p, rewrite q, exact mul_one one},
    { intros g p, esimp at *, rewrite p, exact one_inv }
  end

  definition is_trivial_subgroup (G : Group) (R : subgroup_rel G) : Prop := sorry /- Π g, R g = trivial_subgroup g -/

  definition full_subgroup (G : Group) : subgroup_rel G :=
  begin
    exact sorry /- λ g, unit -/
  end

  definition is_full_subgroup (G : Group) (R : subgroup_rel G) : Prop := sorry /- Π g, R g -/

  /-- Every group homomorphism f : G -> H determines a subgroup of H, the image of f, and a subgroup of G, the kernel of f. In the following definition we define the image of f. Since a subgroup is required to be closed under the group operations, showing that the image of f is closed under the group operations is part of the definition of the image of f. --/

  /-- TODO. We need to find some reasonable way of dealing with universe levels. The reason why it currently is what it is, is because lean is inflexible with universe leves once tactic mode is started --/
  definition image_subgroup.{u1 u2} {G : Group.{u1}} {H : Group.{u2}} (f : G →g H) : subgroup_rel.{u2 (max u1 u2)} H :=
    begin
      fapply subgroup_rel.mk,
        -- definition of the subset
      { intro h, apply ttrunc, exact fiber f h},
        -- subset contains 1
      { apply trunc.tr, fapply fiber.mk, exact 1, apply respect_one},
        -- subset is closed under multiplication
      { intro h h', intro u v,
        induction u with p, induction v with q,
        induction p with x p, induction q with y q,
        induction p, induction q,
        apply tr, apply fiber.mk (x * y), apply respect_mul},
        -- subset is closed under inverses
      { intro g, intro t, induction t, induction a with x p, induction p,
        apply tr, apply fiber.mk x⁻¹, apply respect_inv }
    end 

  section kernels

  variables {G₁ G₂ : Group}

  -- TODO: maybe define this in more generality for pointed types? <-- Do you mean pointed sets?
  definition kernel_pred [constructor] (φ : G₁ →g G₂) (g : G₁) : Prop := trunctype.mk (φ g = 1) _

  theorem kernel_mul (φ : G₁ →g G₂) (g h : G₁) (H₁ : kernel_pred φ g) (H₂ : kernel_pred φ h) : kernel_pred φ (g *[G₁] h) :=
  begin
    esimp at *,
    exact calc
      φ (g * h) = (φ g) * (φ h) : to_respect_mul
            ... = 1 * (φ h)     : H₁
            ... = 1 * 1         : H₂
            ... = 1             : one_mul
  end

  theorem kernel_inv (φ : G₁ →g G₂) (g : G₁) (H : kernel_pred φ g) : kernel_pred φ (g⁻¹) :=
  begin
    esimp at *,
    exact calc
      φ g⁻¹ = (φ g)⁻¹ : to_respect_inv
        ... = 1⁻¹     : H
        ... = 1       : one_inv
  end

  definition kernel_subgroup [constructor] (φ : G₁ →g G₂) : subgroup_rel G₁ :=
  ⦃ subgroup_rel,
    R := kernel_pred φ,
    Rone := respect_one φ,
    Rmul := kernel_mul φ,
    Rinv := kernel_inv φ
  ⦄

  end kernels

  /-- Now we should be able to show that if f is a homomorphism for which the kernel is trivial and the image is full, then f is an isomorphism, except that no one defined the proposition that f is an isomorphism :/ --/
  definition is_iso_from_kertriv_imfull {G H : Group} (f : G →g H) : is_trivial_subgroup G (kernel f) → is_full_subgroup H (image_subgroup f) → unit /- replace unit by is_isomorphism f -/ := sorry

  /- #Normal subgroups -/

  /-- Next, we formalize some aspects of normal subgroups. Recall that a normal subgroup H of a group G is a subgroup which is invariant under all inner automorophisms on G. --/

  definition aut.{u} (G : Group.{u}) : Group.{u} :=
  begin
    fapply Group.mk, 
    exact (G ≃g G),
    fapply group.mk,
    { intros e f, fapply isomorphism.mk, exact f ∘g e, exact is_equiv.is_equiv_compose f e},
    { /-is_set G ≃g G-/ exact sorry},
    { /-associativity-/ intros e f g, exact sorry},
    { /-identity-/ fapply isomorphism.mk, exact sorry, exact sorry},
    { /-identity is left unit-/ exact sorry},
    { /-identity is right unit-/ exact sorry},
    { /-inverses-/ exact sorry},
    { /-inverse is right inverse?-/ exact sorry},
  end

  definition inner_aut (G : Group) : G →g (G ≃g G) := sorry /-- h ↦ h * g * h⁻¹ --/

  /-- There is a problem with the following definition, namely that there is no mere proposition that says that N is normal --/
  structure normal_subgroup_rel (G : Group) extends subgroup_rel G :=
    (is_normal : Π{g} h, R g → R (h * g * h⁻¹))
  /-- expect something like (is_normal : isNormal R) where isNormal R is a predefined predicate on subgroups of G --/

  attribute subgroup_rel.R [coercion]
  abbreviation subgroup_to_rel      [unfold 2] := @subgroup_rel.R
  abbreviation subgroup_has_one     [unfold 2] := @subgroup_rel.Rone
  abbreviation subgroup_respect_mul [unfold 2] := @subgroup_rel.Rmul
  abbreviation subgroup_respect_inv [unfold 2] := @subgroup_rel.Rinv
  abbreviation is_normal_subgroup   [unfold 2] := @normal_subgroup_rel.is_normal

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : CommGroup}

  theorem is_normal_subgroup' (h : G) (r : N g) : N (h⁻¹ * g * h) :=
  inv_inv h ▸ is_normal_subgroup N h⁻¹ r

  definition normal_subgroup_rel_comm.{u} (R : subgroup_rel.{_ u} A) : normal_subgroup_rel.{_ u} A :=
  ⦃normal_subgroup_rel, R,
    is_normal := abstract begin
      intros g h r, xrewrite [mul.comm h g, mul_inv_cancel_right], exact r
      end end⦄

  theorem is_normal_subgroup_rev (h : G) (r : N (h * g * h⁻¹)) : N g :=
  have H : h⁻¹ * (h * g * h⁻¹) * h = g, from calc
    h⁻¹ * (h * g * h⁻¹) * h = h⁻¹ * (h * g) * h⁻¹ * h : by rewrite [-mul.assoc h⁻¹]
                        ... = h⁻¹ * (h * g)           : by rewrite [inv_mul_cancel_right]
                        ... = g                       : inv_mul_cancel_left,
  H ▸ is_normal_subgroup' N h r

  theorem is_normal_subgroup_rev' (h : G) (r : N (h⁻¹ * g * h)) : N g :=
  is_normal_subgroup_rev N h⁻¹ ((inv_inv h)⁻¹ ▸ r)

  theorem normal_subgroup_insert (r : N k) (r' : N (g * h)) : N (g * (k * h)) :=
  have H1 : N ((g * h) * (h⁻¹ * k * h)), from
    subgroup_respect_mul N r' (is_normal_subgroup' N h r),
  have H2 : (g * h) * (h⁻¹ * k * h) = g * (k * h), from calc
    (g * h) * (h⁻¹ * k * h) = g * (h * (h⁻¹ * k * h))   : mul.assoc
                        ... = g * (h * (h⁻¹ * (k * h))) : by rewrite [mul.assoc h⁻¹]
                        ... = g * (k * h)               : by rewrite [mul_inv_cancel_left],
  show N (g * (k * h)), from H2 ▸ H1
  /-- In the following, we show that the kernel of any group homomorphism f : G₁ →g G₂ is a normal subgroup of G₁ --/
  theorem is_normal_subgroup_kernel {G₁ G₂ : Group} (φ : G₁ →g G₂) (g : G₁) (h : G₁)
    : kernel_pred φ g → kernel_pred φ (h * g * h⁻¹) :=
  begin
    esimp at *,
    intro p,
    exact calc
      φ (h * g * h⁻¹) = (φ (h * g)) * φ (h⁻¹)   : to_respect_mul
                  ... = (φ h) * (φ g) * (φ h⁻¹) : to_respect_mul
                  ... = (φ h) * 1 * (φ h⁻¹)     : p
                  ... = (φ h) * (φ h⁻¹)         : mul_one
                  ... = (φ h) * (φ h)⁻¹         : to_respect_inv
                  ... = 1                       : mul.right_inv
  end

  /-- Thus, we extend the kernel subgroup to a normal subgroup --/
  definition normal_subgroup_kernel [constructor] {G₁ G₂ : Group} (φ : G₁ →g G₂) : normal_subgroup_rel G₁ :=
  ⦃ normal_subgroup_rel,
    kernel_subgroup φ,
    is_normal := is_normal_subgroup_kernel φ
  ⦄

  -- this is just (Σ(g : G), H g), but only defined if (H g) is a prop
  definition sg : Type := {g : G | H g}
  local attribute sg [reducible]
  variable {H}
  definition subgroup_one [constructor] : sg H := ⟨one, !subgroup_has_one⟩
  definition subgroup_inv [unfold 3] : sg H → sg H :=
  λv, ⟨v.1⁻¹, subgroup_respect_inv H v.2⟩
  definition subgroup_mul [unfold 3 4] : sg H → sg H → sg H :=
  λv w, ⟨v.1 * w.1, subgroup_respect_mul H v.2 w.2⟩

  section
  local notation 1 := subgroup_one
  local postfix ⁻¹ := subgroup_inv
  local infix * := subgroup_mul

  theorem subgroup_mul_assoc (g₁ g₂ g₃ : sg H) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  subtype_eq !mul.assoc

  theorem subgroup_one_mul (g : sg H) : 1 * g = g :=
  subtype_eq !one_mul

  theorem subgroup_mul_one (g : sg H) : g * 1 = g :=
  subtype_eq !mul_one

  theorem subgroup_mul_left_inv (g : sg H) : g⁻¹ * g = 1 :=
  subtype_eq !mul.left_inv

  theorem subgroup_mul_comm {G : CommGroup} {H : subgroup_rel G} (g h : sg H)
    : g * h = h * g :=
  subtype_eq !mul.comm

  end

  variable (H)
  definition group_sg [constructor] : group (sg H) :=
  group.mk subgroup_mul _ subgroup_mul_assoc subgroup_one subgroup_one_mul subgroup_mul_one
           subgroup_inv subgroup_mul_left_inv

  definition subgroup [constructor] : Group :=
  Group.mk _ (group_sg H)

  definition comm_group_sg [constructor] {G : CommGroup} (H : subgroup_rel G)
    : comm_group (sg H) :=
  ⦃comm_group, group_sg H, mul_comm := subgroup_mul_comm⦄

  definition comm_subgroup [constructor] {G : CommGroup} (H : subgroup_rel G)
    : CommGroup :=
  CommGroup.mk _ (comm_group_sg H)

end group
