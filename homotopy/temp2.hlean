
import .smash_adjoint

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge is_trunc
     function red_susp unit smash

variables {A A' B B' C C' D E F X X' : Type*}















































































-- definition concat2o {A B : Type} {f g h : A → B} {a₁ a₂ : A} {p₁ : f a₁ = g a₁} {p₂ : f a₂ = g a₂}
--   {q₁ : g a₁ = h a₁} {q₂ : g a₂ = h a₂} {r : a₁ = a₂} (s₁ : p₁ =[r] p₂) (s₂ : q₁ =[r] q₂) :
--   p₁ ⬝ q₁ =[r] p₂ ⬝ q₂ :=
-- apo011 (λx, concat) s₁ s₂

-- infixl ` ◾o' `:75 := concat2o

-- definition apd_con_fn {A B : Type} {f g h : A → B} {a₁ a₂ : A} (p : f ~ g) (q : g ~ h) (r : a₁ = a₂)
--   : apd (λa, p a ⬝ q a) r = apd p r ◾o' apd q r :=
-- begin
--   induction r, reflexivity
-- end

-- definition ap02o {A : Type} {B C : A → Type} {g h : Πa, B a} (f : Πa, B a → C a) {a₁ a₂ : A} {p₁ : g a₁ = h a₁}
--   {p₂ : g a₂ = h a₂} {q : a₁ = a₂} (r : p₁ =[q] p₂) : ap (f a₁) p₁ =[q] ap (f a₂) p₂ :=
-- apo (λx, ap (f x)) r

-- definition apo_eq_pathover {A A' B B' : Type} {a a' : A} {f g : A → B} {i : A → A'} {f' g' : A' → B'}
--   {p : a = a'} {q : f a = g a} (h : Πa, f a = g a → f' (i a) = g' (i a))
--   {r : f a' = g a'} (s : square q r (ap f p) (ap g p)) :
--    apo h (eq_pathover s) = eq_pathover _ :=
-- sorry

-- definition ap02o_eq_pathover {A A' B B' : Type} {a a' : A} {f g : A → B} {i : A → A'} {f' g' : A' → B'}
--   {p : a = a'} {q : f a = g a} (h : Πa, f a = g a → f' (i a) = g' (i a))
--   {r : f a' = g a'} (s : square q r (ap f p) (ap g p)) :
--    apo h (eq_pathover s) = eq_pathover _ :=
-- sorry

-- definition apd_ap_fn {A : Type} {B C : A → Type} {g h : Πa, B a} (f : Πa, B a → C a) (p : g ~ h)
--   {a₁ a₂ : A} (r : a₁ = a₂) : apd (λa, ap (f a) (p a)) r = ap02o f (apd p r) :=
-- begin
--   induction r; reflexivity
-- end

-- definition apd_ap_fn {A : Type} {B C : A → Type} {g h : Πa, B a} (f : Πa, B a → C a) (p : g ~ h)
--   {a₁ a₂ : A} (r : a₁ = a₂) : apd (λa, ap (f a) (p a)) r = ap02o f (apd p r) :=
