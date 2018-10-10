import types.trunc types.sum types.lift types.unit

open pi prod sum unit bool trunc is_trunc is_equiv eq equiv lift pointed

namespace choice
universe variables u v

-- the following brilliant name is from Agda
definition unchoose [unfold 4] (n : ℕ₋₂) {X : Type} (A : X → Type) : trunc n (Πx, A x) → Πx, trunc n (A x) :=
trunc.elim (λf x, tr (f x))

definition has_choice [class] (n : ℕ₋₂) (X : Type.{u}) : Type.{max u (v+1)} :=
Π(A : X → Type.{v}), is_equiv (unchoose n A)

definition choice_equiv [constructor] {n : ℕ₋₂} {X : Type} [H : has_choice.{u v} n X]
  (A : X → Type) : trunc n (Πx, A x) ≃ (Πx, trunc n (A x)) :=
equiv.mk _ (H A)

definition has_choice_of_succ (X : Type) (H : Πk, has_choice.{_ v} (k.+1) X) (n : ℕ₋₂) :
  has_choice.{_ v} n X :=
begin
  cases n with n,
  { intro A, exact is_equiv_of_is_contr _ _ _ },
  { exact H n }
end

/- currently we prove it using univalence, which means we cannot apply it to lift. -/
definition has_choice_equiv_closed (n : ℕ₋₂) {A B : Type} (f : A ≃ B) (hA : has_choice.{u v} n B)
  : has_choice.{u v} n A :=
begin
  induction f using rec_on_ua_idp, exact hA
end

definition has_choice_empty [instance] (n : ℕ₋₂) : has_choice.{_ v} n empty :=
begin
  intro A, fapply adjointify,
  { intro f, apply tr, intro x, induction x },
  { intro f, apply eq_of_homotopy, intro x, induction x },
  { intro g, induction g with g, apply ap tr, apply eq_of_homotopy, intro x, induction x }
end

definition has_choice_unit [instance] : Πn, has_choice.{_ v} n unit :=
begin
  intro n A, fapply adjointify,
  { intro f, induction f ⋆ with a, apply tr, intro u, induction u, exact a },
  { intro f, apply eq_of_homotopy, intro u, induction u, esimp, generalize f ⋆, intro a,
    induction a, reflexivity },
  { intro g, induction g with g, apply ap tr, apply eq_of_homotopy,
    intro u, induction u, reflexivity }
end

definition has_choice_sum [instance] (n : ℕ₋₂) (A B : Type.{u})
  [has_choice.{_ v} n A] [has_choice.{_ v} n B] : has_choice.{_ v} n (A ⊎ B) :=
begin
  intro P, fapply is_equiv_of_equiv_of_homotopy,
  { exact calc
     trunc n (Πx, P x) ≃ trunc n ((Πa, P (inl a)) × Πb, P (inr b))
       : trunc_equiv_trunc n !equiv_sum_rec⁻¹ᵉ
     ... ≃ trunc n (Πa, P (inl a)) × trunc n (Πb, P (inr b)) : trunc_prod_equiv
     ... ≃ (Πa, trunc n (P (inl a))) × Πb, trunc n (P (inr b))
       : by exact prod_equiv_prod (choice_equiv _) (choice_equiv _)
     ... ≃ Πx, trunc n (P x) : equiv_sum_rec },
  { intro f, induction f, apply eq_of_homotopy, intro x, esimp, induction x with a b: reflexivity }
end

definition has_choice_bool [instance] (n : ℕ₋₂) : has_choice.{_ v} n bool :=
has_choice_equiv_closed n bool_equiv_unit_sum_unit _

definition has_choice_lift.{u'} [instance] (n : ℕ₋₂) (A : Type) [has_choice.{_ v} n A] :
  has_choice.{_ v} n (lift.{u u'} A) :=
sorry --has_choice_equiv_closed n !equiv_lift⁻¹ᵉ _

definition has_choice_punit [instance] (n : ℕ₋₂) : has_choice.{_ v} n punit := has_choice_unit n
definition has_choice_pbool [instance] (n : ℕ₋₂) : has_choice.{_ v} n pbool := has_choice_bool n
definition has_choice_plift [instance] (n : ℕ₋₂) (A : Type*) [has_choice.{_ v} n A]
  : has_choice.{_ v} n (plift A) := has_choice_lift n A
definition has_choice_psum [instance] (n : ℕ₋₂) (A B : Type*) [has_choice.{_ v} n A] [has_choice.{_ v} n B]
  : has_choice.{_ v} n (psum A B) := has_choice_sum n A B

end choice
