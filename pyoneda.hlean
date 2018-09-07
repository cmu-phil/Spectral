/-
In this file we give a consequence of the Yoneda lemma for pointed types which we can state
internally. If we have a pointed equivalence α : A ≃* B, we can turn it into an equivalence
γ : (B →* X) ≃* (A →* X), natural in X. Naturality means that if we have f : X → X' then we
can fill the following square (using a pointed homotopy)
(B →* X)  --> (A →* X)
   |             |
   v             v
(B →* X') --> (B →* X')
such that if f is the constant map, then this square is equal to the canonical filler of that
square (where the fact that f is constant is used).

Conversely, if we have such a γ natural in X, we can obtain an equivalence A ≃* B.
Moreover, these operations are equivalences in the sense that going from α to γ to α is the
same as doing nothing, and going from γ to α to γ is the same as doing nothing. However, we
need higher coherences for γ to show that the proof of naturality is the same, which we didn't do.

Author: Floris van Doorn (informal proofs in collaboration with Stefano Piceghello)
-/

import .pointed

open equiv is_equiv eq
namespace pointed

  universe variable u

  definition ppcompose_right_ppcompose_left {A A' B B' : Type*} (f : A →* A') (g : B →* B'):
    psquare (ppcompose_right f) (ppcompose_right f) (ppcompose_left g) (ppcompose_left g) :=
  ptranspose !ppcompose_left_ppcompose_right

  -- definition pyoneda₂ {A B : pType.{u}} (γ : Π(X : pType.{u}), ppmap B X ≃* ppmap A X)
  --   (p : Π(X X' : Type*), _ ∘* pppcompose B X X' ~* (_ : ppmap _ _))
  --   : A ≃* B :=
  -- begin
  --   fapply pequiv.MK,
  --   { exact γ B (pid B) },
  --   { exact (γ A)⁻¹ᵉ* (pid A) },
  --   { refine phomotopy_of_eq (p _ _) ⬝* _,
  --     exact pap (γ A) !pcompose_pid ⬝* phomotopy_of_eq (to_right_inv (γ A) _) },
  --   { refine phomotopy_of_eq ((p _)⁻¹ʰ* _) ⬝* _,
  --     exact pap (γ B)⁻¹ᵉ* !pcompose_pid ⬝* phomotopy_of_eq (to_left_inv (γ B) _) }
  -- end

-- print ⁻¹ʰᵗʸʰ
-- print eq.hhinverse
  definition pyoneda_weak {A B : pType.{u}} (γ : Π(X : pType.{u}), ppmap B X ≃* ppmap A X)
    (p : Π⦃X X' : Type*⦄ (f : X →* X') (g : B →* X), f ∘* γ X g ~* γ X' (f ∘* g)) : A ≃* B :=
  begin
    fapply pequiv.MK,
    { exact γ B (pid B) },
    { exact (γ A)⁻¹ᵉ* (pid A) },
    { refine p _ _ ⬝* _,
      exact pap (γ A) !pcompose_pid ⬝* phomotopy_of_eq (to_right_inv (γ A) _) },
    { -- refine (p _)⁻¹ʰᵗʸʰ _ ⬝* _,
      -- exact pap (γ B)⁻¹ᵉ* !pcompose_pid ⬝* phomotopy_of_eq (to_left_inv (γ B) _)
      exact sorry
      }
  end

  definition pyoneda {A B : pType.{u}} (γ : Π(X : pType.{u}), ppmap B X ≃* ppmap A X)
    (p : Π⦃X X' : Type*⦄ (f : X →* X'), psquare (γ X) (γ X') (ppcompose_left f) (ppcompose_left f))
    : A ≃* B :=
--  pyoneda_weak γ p
  begin
    fapply pequiv.MK,
    { exact γ B (pid B) },
    { exact (γ A)⁻¹ᵉ* (pid A) },
    { refine phomotopy_of_eq (p _ _) ⬝* _,
      exact pap (γ A) !pcompose_pid ⬝* phomotopy_of_eq (to_right_inv (γ A) _) },
    { refine phomotopy_of_eq ((p _)⁻¹ʰ* _) ⬝* _,
      exact pap (γ B)⁻¹ᵉ* !pcompose_pid ⬝* phomotopy_of_eq (to_left_inv (γ B) _) }
  end

  definition pyoneda_right_inv {A B : pType.{u}} (α : A ≃* B) :
    pyoneda (λX, ppmap_pequiv_ppmap_left α) (λX X' f, proof !ppcompose_right_ppcompose_left qed) ~*
    α :=
  phomotopy.mk homotopy.rfl idp

  definition pyoneda_left_inv {A B : pType.{u}} (γ : Π(X : pType.{u}), ppmap B X ≃* ppmap A X)
    (p : Π⦃X X' : Type*⦄ (f : X →* X'), psquare (γ X) (γ X') (ppcompose_left f) (ppcompose_left f))
    (H : Π⦃X⦄ (X' : Type*) (g : B →* X), phomotopy_of_eq (p (pconst X X') g) =
      !pconst_pcompose ⬝* (pap (γ X') !pconst_pcompose ⬝* phomotopy_of_eq (respect_pt (γ X')))⁻¹*)
    (X : Type*) : ppcompose_right (pyoneda γ p) ~* γ X :=
 begin
    fapply phomotopy_mk_ppmap,
    { intro f, refine phomotopy_of_eq (p _ _) ⬝* _, exact pap (γ X) !pcompose_pid },
    { refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      refine !trans_assoc ⬝ _,
      refine H X (pid B) ◾** idp ⬝ !trans_assoc ⬝ idp ◾** _ ⬝ !trans_refl,
      apply trans_left_inv }
  end

  definition pyoneda_weak_left_inv {A B : pType.{u}} (γ : Π(X : pType.{u}), ppmap B X ≃* ppmap A X)
    (p : Π⦃X : Type*⦄ (X' : Type*) (g : B →* X), ppcompose_right (γ X g) ~* γ X' ∘* ppcompose_right g)
    (X : Type*) : ppcompose_right (pyoneda_weak γ (λX X' f g, phomotopy_of_eq (p X' g f))) ~* γ X :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro f, refine phomotopy_of_eq (p _ _ _) ⬝* _, exact pap (γ X) !pcompose_pid },
    { refine _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      refine !trans_assoc ⬝ _,
      refine (ap phomotopy_of_eq (eq_con_inv_of_con_eq (to_homotopy_pt (p X (pid B)))) ⬝
        !phomotopy_of_eq_con ⬝ !phomotopy_of_eq_of_phomotopy ◾**
        (!phomotopy_of_eq_inv ⬝ (!phomotopy_of_eq_con ⬝ (!phomotopy_of_eq_ap ⬝
        ap (pap' _) !phomotopy_of_eq_of_phomotopy) ◾** idp)⁻²**)) ◾** idp ⬝ _,
      refine !trans_assoc ⬝ idp ◾** _ ⬝ !trans_refl,
      apply trans_left_inv }
  end


end pointed
