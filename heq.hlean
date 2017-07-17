-- Author: Floris van Doorn

open eq is_trunc

variables {I : Set} {P : I → Type} {i j k : I} {x x₁ x₂ : P i} {y y₁ y₂ : P j} {z : P k}
          {Q : Π⦃i⦄, P i → Type}

structure heq (x : P i) (y : P j) : Type :=
  (p : i = j)
  (q : x =[p] y)

namespace eq
notation x ` ==[`:50 P:0 `] `:0 y:50 := @heq _ P _ _ x y
infix ` == `:50 := heq -- mostly for printing, since it will be almost always ambiguous what P is

definition pathover_of_heq {p : i = j} (q : x ==[P] y) : x =[p] y :=
change_path !is_set.elim (heq.q q)

definition eq_of_heq (p : x₁ ==[P] x₂) : x₁ = x₂ :=
eq_of_pathover_idp (pathover_of_heq p)

definition heq.elim (p : x ==[P] y) (q : Q x) : Q y :=
begin
  induction p with p r, induction r, exact q
end

definition heq.refl [refl] (x : P i) : x ==[P] x :=
heq.mk idp idpo

definition heq.rfl : x ==[P] x :=
heq.refl x

definition heq.symm [symm] (p : x ==[P] y) : y ==[P] x :=
begin
  induction p with p q, constructor, exact q⁻¹ᵒ
end

definition heq_of_eq (p : x₁ = x₂) : x₁ ==[P] x₂ :=
heq.mk idp (pathover_idp_of_eq p)

definition heq.trans [trans] (p : x ==[P] y) (p₂ : y ==[P] z) : x ==[P] z :=
begin
  induction p with p q, induction p₂ with p₂ q₂, constructor, exact q ⬝o q₂
end

infix ` ⬝he `:72 := heq.trans
postfix `⁻¹ʰᵉ`:(max+10) := heq.symm


definition heq_of_heq_of_eq (p : x ==[P] y) (p₂ : y = y₂) : x ==[P] y₂ :=
p ⬝he heq_of_eq p₂

definition heq_of_eq_of_heq (p : x = x₂) (p₂ : x₂ ==[P] y) : x ==[P] y :=
heq_of_eq p ⬝he p₂

infix ` ⬝hep `:73 := concato_eq
infix ` ⬝phe `:74 := eq_concato

definition heq_tr (p : i = j) (x : P i) : x ==[P] transport P p x :=
heq.mk p !pathover_tr

definition tr_heq (p : i = j) (x : P i) : transport P p x ==[P] x :=
(heq_tr p x)⁻¹ʰᵉ

end eq
