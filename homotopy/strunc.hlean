import .spectrum .EM

open int trunc eq is_trunc lift unit pointed equiv is_equiv algebra EM
namespace spectrum

definition trunc_int.{u} (k : ℤ) (X : Type.{u}) : Type.{u} :=
begin
  induction k with k k, exact trunc k X,
  cases k with k, exact trunc -1 X,
  exact lift unit
end

definition ptrunc_int.{u} (k : ℤ) (X : pType.{u}) : pType.{u} :=
begin
  induction k with k k, exact ptrunc k X,
  exact plift punit
end

definition ptrunc_int_pequiv_ptrunc_int (k : ℤ) {X Y : Type*} (e : X ≃* Y) :
  ptrunc_int k X ≃* ptrunc_int k Y :=
begin
  induction k with k k,
    exact ptrunc_pequiv_ptrunc k e,
  exact !pequiv_plift⁻¹ᵉ* ⬝e* !pequiv_plift
end

definition ptrunc_int_change_int {k l : ℤ} (X : Type*) (p : k = l) :
  ptrunc_int k X ≃* ptrunc_int l X :=
pequiv_ap (λn, ptrunc_int n X) p

definition loop_ptrunc_int_pequiv (k : ℤ) (X : Type*) :
  Ω (ptrunc_int (k+1) X) ≃* ptrunc_int k (Ω X) :=
begin
  induction k with k k,
    exact loop_ptrunc_pequiv k X,
  cases k with k,
    change Ω (ptrunc 0 X) ≃* plift punit,
    exact !loop_pequiv_punit_of_is_set ⬝e* !pequiv_plift,
  exact loop_pequiv_loop !pequiv_plift⁻¹ᵉ* ⬝e* !loop_punit ⬝e* !pequiv_plift
end

definition strunc_int [constructor] (k : ℤ) (E : spectrum) : spectrum :=
spectrum.MK (λ(n : ℤ), ptrunc_int (k + n) (E n))
            (λ(n : ℤ), ptrunc_int_pequiv_ptrunc_int (k + n) (equiv_glue E n) ⬝e*
                       (loop_ptrunc_int_pequiv (k + n) (E (n+1)))⁻¹ᵉ* ⬝e*
                       loop_pequiv_loop (ptrunc_int_change_int _ (add.assoc k n 1)))

definition strunc_int_change_int [constructor] {k l : ℤ} (E : spectrum) (p : k = l) :
  strunc_int k E →ₛ strunc_int l E :=
begin induction p, reflexivity end

end spectrum
