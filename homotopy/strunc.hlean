import .spectrum .EM

-- TODO move this
namespace int

  definition max0_le_of_le {n : ℤ} {m : ℕ} (H : n ≤ of_nat m)
    : nat.le (max0 n) m :=
  begin
    induction n with n n,
    { exact le_of_of_nat_le_of_nat H },
    { exact nat.zero_le m }
  end

end int

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
-- NB the carrier of ptrunc_int k X is not definitionally 
-- equal to trunc_int k (carrier X)

definition ptr_int (k : ℤ) (X : pType) : X →* ptrunc_int k X :=
pmap.mk (λ x, int.cases_on k (λ k', tr x) (λ k', up star))
  (int.cases_on k (λ k', idp) (λ k', idp))

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

definition strunc [constructor] (k : ℤ) (E : spectrum) : spectrum :=
spectrum.MK (λ(n : ℤ), ptrunc_int (k + n) (E n))
            (λ(n : ℤ), ptrunc_int_pequiv_ptrunc_int (k + n) (equiv_glue E n) ⬝e*
                       (loop_ptrunc_int_pequiv (k + n) (E (n+1)))⁻¹ᵉ* ⬝e*
                       loop_pequiv_loop (ptrunc_int_change_int _ (add.assoc k n 1)))

definition strunc_change_int [constructor] {k l : ℤ} (E : spectrum) (p : k = l) :
  strunc k E →ₛ strunc l E :=
begin induction p, reflexivity end

definition is_trunc_int.{u} (k : ℤ) (X : Type.{u}) : Type.{u} :=
begin
  induction k with k k,
  { -- case ≥ 0
    exact is_trunc k X },
  { cases k with k,
    { -- case = -1
      exact is_trunc -1 X },
    { -- case < -1
      exact is_contr X } }
end

definition is_trunc_int_change_int {k l : ℤ} (X : Type) (p : k = l)
  : is_trunc_int k X → is_trunc_int l X :=
begin induction p, exact id end

definition is_trunc_int_loop (A : pType) (k : ℤ)
  : is_trunc_int (k + 1) A → is_trunc_int k (Ω A) :=
begin
  intro H, induction k with k k, 
  { apply is_trunc_loop, exact H },
  { cases k with k,
    { apply is_trunc_loop, exact H},
    { apply is_trunc_loop, cases k with k,
      { exact H },
      { apply is_trunc_succ, exact H } } }
end

definition is_trunc_of_is_trunc_int (k : ℤ) (X : Type)
  : is_trunc_int k X → is_trunc (max0 k) X :=
begin
  intro H, induction k with k k,
  { exact H },
  { cases k with k,
    { apply is_trunc_succ, exact H },
    { apply is_trunc_of_is_contr, exact H } }
end

definition is_strunc (k : ℤ) (E : spectrum) : Type :=
Π (n : ℤ), is_trunc_int (k + n) (E n)

definition is_strunc_change_int {k l : ℤ} (E : spectrum) (p : k = l)
  : is_strunc k E → is_strunc l E :=
begin induction p, exact id end

definition is_trunc_trunc_int (k : ℤ) (X : Type)
  : is_trunc_int k (trunc_int k X) :=
begin
  induction k with k k,
  { -- case ≥ 0
    exact is_trunc_trunc k X },
  { cases k with k,
    { -- case = -1
      exact is_trunc_trunc -1 X },
    { -- case < -1
      apply is_trunc_lift } }
end

definition is_trunc_ptrunc_int (k : ℤ) (X : pType)
  : is_trunc_int k (ptrunc_int k X) :=
begin
  induction k with k k,
  { -- case ≥ 0
    exact is_trunc_trunc k X },
  { cases k with k,
    { -- case = -1
      apply is_trunc_lift, apply is_trunc_unit },
    { -- case < -1
      apply is_trunc_lift, apply is_trunc_unit } }
end

definition is_strunc_strunc (k : ℤ) (E : spectrum)
  : is_strunc k (strunc k E) :=
λ n, is_trunc_ptrunc_int (k + n) (E n)

definition is_strunc_EM_spectrum (G : AbGroup)
  : is_strunc 0 (EM_spectrum G) :=
begin
  intro n, induction n with n n,
  { -- case ≥ 0
    apply is_trunc_int_change_int (EM G n) (zero_add n)⁻¹,
    apply is_trunc_EM },
  { induction n with n IH,
    { -- case = -1
      apply is_trunc_loop, exact ab_group.is_set_carrier G },
    { -- case < -1
      apply is_trunc_int_loop, exact IH }}
end

definition trivial_shomotopy_group_of_is_strunc (E : spectrum)
  {n k : ℤ} (K : is_strunc n E) (H : n < k)
  : is_contr (πₛ[k] E) :=
let m := n + (2 - k) in
have I : m < 2, from
  calc
    m = (2 - k) + n : int.add_comm n (2 - k)
  ... < (2 - k) + k : add_lt_add_left H (2 - k)
  ... = 2           : sub_add_cancel 2 k,
@trivial_homotopy_group_of_is_trunc (E (2 - k)) (max0 m) 2
  (is_trunc_of_is_trunc_int m (E (2 - k)) (K (2 - k)))
  (nat.succ_le_succ (max0_le_of_le (le_sub_one_of_lt I)))

definition str [constructor] (k : ℤ) (E : spectrum) : E →ₛ strunc k E :=
smap.mk (λ n, ptr_int (k + n) (E n))
  sorry

end spectrum
