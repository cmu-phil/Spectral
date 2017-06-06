import .spectrum .EM ..algebra.arrow_group ..algebra.direct_sum .fwedge ..choice .pushout ..move_to_lib ..algebra.product_group

open eq spectrum int trunc pointed EM group algebra circle sphere nat EM.ops equiv susp is_trunc
     function fwedge cofiber bool lift sigma is_equiv choice pushout algebra unit pi

namespace homology

/- homology theory -/
structure homology_theory.{u} : Type.{u+1} :=
  (HH : ℤ → pType.{u} → AbGroup.{u})
  (Hh : Π(n : ℤ) {X Y : Type*} (f : X →* Y), HH n X →g HH n Y)
  (Hid : Π(n : ℤ) {X : Type*} (x : HH n X), Hh n (pid X) x = x)
  (Hcompose : Π(n : ℤ) {X Y Z : Type*} (g : Y →* Z) (f : X →* Y) (x : HH n X),
    Hh n (g ∘* f) x = Hh n g (Hh n f x))
  (Hsusp : Π(n : ℤ) (X : Type*), HH (succ n) (psusp X) ≃g HH n X)
  (Hsusp_natural : Π(n : ℤ) {X Y : Type*} (f : X →* Y),
    Hsusp n Y ∘ Hh (succ n) (psusp_functor f) ~ Hh n f ∘ Hsusp n X)
  (Hexact : Π(n : ℤ) {X Y : Type*} (f : X →* Y), is_exact_g (Hh n f) (Hh n (pcod f)))
  (Hadditive : Π(n : ℤ) {I : Set.{u}} (X : I → Type*), is_equiv (
    dirsum_elim (λi, Hh n (pinl i)) : dirsum (λi, HH n (X i)) → HH n (⋁ X))
)
end homology
