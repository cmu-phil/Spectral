/-
Copyright (c) 2018 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/

import algebra.group_theory hit.set_quotient types.list homotopy.vankampen
       homotopy.susp .pushout ..algebra.free_group

open eq pointed equiv is_equiv is_trunc set_quotient sum list susp trunc algebra
     group pi pushout is_conn fiber unit function category paths

-- special purpose lemmas
definition tr_trunc_eq (A : Type) (a : A) {x y : A} (p : x = y) (q : x = a)
  : transport (λ(z : A), trunc 0 (z = a)) p (tr q) = tr (p⁻¹ ⬝ q) :=
by induction p; induction q; reflexivity

namespace susp
  section
  universe variable u
  parameters (A : pType.{u}) [H : is_set A]
  include H

  local notation `F` := Π₁⇒ (λ(a : A), star)

  local abbreviation C : Groupoid := Groupoid_bpushout (@id A) F F
  local abbreviation N : C := inl star
  local abbreviation S : C := inr star

--  local notation `N` := a

  -- hom group of fundamental groupoid is fundamental group
  -- the fundamental group of the suspension is the free group on A
  -- could go via van Kampen, but would have to compose with opposite, which is not so well developed
  -- definition fundamental_group_of_susp : π₁(⅀ A) ≃g free_group A :=
  -- sorry

  /-
  van Kampen instead?
  
     game plan:
1. lift to 1-connected cover
2. apply flattening lemma
3. provide equivalences F A ≃ ∥N = N∥ ≃ ∥S = N∥
4. move to is_contr
5. induction induction induction!
  -/

  definition pglueNS (a : A) : hom N S :=
  class_of [ bpushout_prehom_index.DE (@id A) F F a ]

  definition pglueSN (a : A) : hom S N :=
  class_of [ bpushout_prehom_index.ED (@id A) F F a ]

  definition f : A × hom N N → hom S N :=
  prod.rec (λ a p, p ∘ pglueSN a)

  definition g : A × trunc 0 (@susp.north A = @susp.north A) → trunc 0 (@susp.south A = @susp.north A) :=
  prod.rec (λ a p, tconcat (tr (merid a)⁻¹) p)

  --set_option pp.notation false
  --set_option pp.implicit true


  definition foo : (Σ(z : susp A), trunc 0 (z = susp.north)) ≃ pushout prod.pr2 g :=
  begin
    apply equiv.trans !pushout.flattening',
    fapply pushout.equiv,
    { apply sigma.equiv_prod },
    { apply sigma.sigma_unit_left },
    { apply sigma.sigma_unit_left },
    { intro z, induction z with a p, induction p with p, reflexivity },
    { intro z, induction z with a p, induction p with p, apply tr_trunc_eq }
  end

  definition bar : pushout prod.pr2 g ≃ pushout prod.pr2 f :=
  begin
    fapply pushout.equiv,
    { apply prod.prod_equiv_prod_right, apply vankampen },
    { apply vankampen },
    { apply vankampen },
    { intro z, induction z with a p, reflexivity },
    { intro z, induction z with a p, 
      change (encode (@id A) (λ(z : A), star) (λ(z : A), star) (tconcat (tr (merid a)⁻¹) p))
        = (encode (@id A) (λ(z : A), star) (λ(z : A), star) p ∘ pglueSN a),
      revert p, fapply @trunc.rec 0 (@susp.north A = @susp.north A),
      { intro p, apply is_trunc_succ, apply is_trunc_eq, apply is_set_code }, intro p,
      apply trans (encode_tcon (@id A) (λ(z : A), star) (λ(z : A), star) (tr (merid a)⁻¹) (tr p)),
      apply ap (λ h, encode (@id A) (λ(z : A), star) (λ(z : A), star) (tr p) ∘ h),
      apply encode_decode_singleton }
  end

  definition is_contr_susp_fiber_tr : is_contr (Σ(z : susp A), trunc 0 (z = susp.north)) := sorry

  definition pfiber_susp_equiv_sigma : pfiber (ptr 1 (⅀ A)) ≃ (Σ(z : susp A), trunc 0 (z = susp.north)) := 
  begin
    apply equiv.trans !fiber.sigma_char,
    apply sigma.sigma_equiv_sigma_right,
    intro z, apply tr_eq_tr_equiv
  end

  definition is_trunc_susp_of_is_set : is_trunc 1 (susp A) :=
  begin
    apply is_trunc_of_is_equiv_tr,
    apply is_equiv_of_is_contr_fun,
    fapply @is_conn.elim -1 (ptrunc 1 (⅀ A)),
    change is_contr (pfiber (ptr 1 (⅀ A))),
    apply is_contr_equiv_closed_rev pfiber_susp_equiv_sigma,
    apply is_contr_susp_fiber_tr
  end

  end

end susp
