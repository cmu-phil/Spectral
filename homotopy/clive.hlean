/-----
This is Clive's file for playing around with (h)Lean/Git/Emacs
------/

import types.trunc types.arrow_2 types.fiber homotopy.circle

open eq is_trunc is_equiv nat equiv trunc function circle



namespace clive

/-- Very easy goal: prove (loop⁻¹)⁻¹ = loop : base = base --/
theorem symm_symm_loop_eq_loop : (loop⁻¹)⁻¹ = loop :=
eq.rec_on loop idp

/-- Another easy goal: define a group and prove that the left inverse law follows form the right inverse law --/
structure group (X : Type) :=
gpstr :: (unit      : X)
         (mult       : X → X → X)
         (inv       : X → X)
         (assoc_law : Π(a b c : X), mult (mult a b) c = mult a (mult b c))
         (inv_law   : Π(a : X), mult a (inv a) = unit)
         (unit_law  : Π(a : X), mult a unit = a)

constants (X : Type) (G : group X)
open group

theorem group_cancel_right : Π(X : Type), Π(G : group X), Π(a b c : X), (mult G a c = mult G b c) → a = b := sorry

theorem inv_mul_left_eq_unit : Π(X : Type), Π(G : group X), Π(a : X), mult G (inv G a) a = unit G :=
  take (X : Type) (G : group X) (a : X),
  have q : mult G (mult G (inv G a) a) (inv G a) = mult G (unit G) (inv G a), from
  calc
    mult G (mult G (inv G a) a) (inv G a) = mult G (inv G a) (mult G a (inv G a)) : assoc_law
    ... = mult G (inv G a) (unit G) : sorry
    ... = inv G a : unit_law
    ... = mult G  (unit G) (inv G a) : sorry,
  group_cancel_right X G (mult G (inv G a) a) (unit G) (inv G a) q


end clive
