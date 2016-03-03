

import  homotopy.wedge types.pi

open eq homotopy is_trunc pointed susp nat pi equiv is_equiv trunc

section freudenthal

parameters {A : Type*} (n : ℕ) [is_conn n A]

--set_option pp.notation false

protected definition my_wedge_extension.ext : Π {A : Type*} {B : Type*} (n m : ℕ) [cA : is_conn n (carrier A)] [cB : is_conn m (carrier B)]
(P : carrier A → carrier B → (m+n)-Type) (f : Π (a : carrier A), trunctype.carrier (P a (Point B)))
(g : Π (b : carrier B), trunctype.carrier (P (Point A) b)),
  f (Point A) = g (Point B) → (Π (a : carrier A) (b : carrier B), trunctype.carrier (P a b)) :=
sorry

definition code_fun (a : A) (q : north = north :> susp A)
  : trunc (n * 2) (fiber (pmap.to_fun (loop_susp_unit A)) q) → trunc (n * 2) (fiber merid (q ⬝ merid a)) :=
begin
  intro x, induction x with x,
  esimp at *, cases x with a' p,
--  apply my_wedge_extension.ext n n,
  exact sorry
end

definition code (y : susp A) :  north = y → Type :=
susp.rec_on y
  (λp, trunc (2*n) (fiber (loop_susp_unit A) p))
  (λq, trunc (2*n) (fiber merid q))
  begin
    intros,
    apply arrow_pathover_constant_right,
    intro q, rewrite [transport_eq_r],
    apply ua,
    exact sorry
  end

definition freudenthal_suspension  : is_conn_map (n*2) (loop_susp_unit A) :=
sorry



end freudenthal
