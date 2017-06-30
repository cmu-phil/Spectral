import .spectrum .EM

-- TODO move this
open trunc_index nat

namespace int

  /-
    The function from integers to truncation indices which sends positive numbers to themselves, and negative
    numbers to negative 2. In particular -1 is sent to -2, but since we only work with pointed types, that
    doesn't matter for us -/
  definition maxm2 [unfold 1] : ℤ → ℕ₋₂ :=
  λ n, int.cases_on n trunc_index.of_nat (λk, -2)

  definition maxm2_le_maxm0 (n : ℤ) : maxm2 n ≤ max0 n :=
  begin
    induction n with n n,
    { exact le.tr_refl n },
    { exact minus_two_le 0 }
  end

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

definition ptrunc_maxm2_change_int {k l : ℤ} (X : Type*) (p : k = l)
  : ptrunc (maxm2 k) X ≃* ptrunc (maxm2 l) X :=
pequiv_ap (λ n, ptrunc (maxm2 n) X) p

definition loop_ptrunc_maxm2_pequiv (k : ℤ) (X : Type*) :
  Ω (ptrunc (maxm2 (k+1)) X) ≃* ptrunc (maxm2 k) (Ω X) :=
begin
  induction k with k k,
  { exact loop_ptrunc_pequiv k X },
  { refine _ ⬝e* (pequiv_punit_of_is_contr _ !is_trunc_trunc)⁻¹ᵉ*,
    apply @loop_pequiv_punit_of_is_set,
    cases k with k,
    { change is_set (trunc 0 X), apply _ },
    { change is_set (trunc -2 X), apply _ }}
end

definition is_trunc_of_is_trunc_maxm2 (k : ℤ) (X : Type)
  : is_trunc (maxm2 k) X → is_trunc (max0 k) X :=
λ H, @is_trunc_of_le X _ _ (maxm2_le_maxm0 k) H

definition strunc [constructor] (k : ℤ) (E : spectrum) : spectrum :=
spectrum.MK (λ(n : ℤ), ptrunc (maxm2 (k + n)) (E n))
            (λ(n : ℤ), ptrunc_pequiv_ptrunc (maxm2 (k + n)) (equiv_glue E n)
              ⬝e* (loop_ptrunc_maxm2_pequiv (k + n) (E (n+1)))⁻¹ᵉ*
              ⬝e* (loop_pequiv_loop
                   (ptrunc_maxm2_change_int _ (add.assoc k n 1))))

definition strunc_change_int [constructor] {k l : ℤ} (E : spectrum) (p : k = l) :
  strunc k E →ₛ strunc l E :=
begin induction p, reflexivity end

definition is_trunc_maxm2_loop (A : pType) (k : ℤ)
  : is_trunc (maxm2 (k + 1)) A → is_trunc (maxm2 k) (Ω A) :=
begin
  intro H, induction k with k k,
  { apply is_trunc_loop, exact H },
  { apply is_contr_loop, cases k with k,
    { exact H },
    { have H2 : is_contr A, from H, apply _ } }
end

definition is_strunc [reducible] (k : ℤ) (E : spectrum) : Type :=
Π (n : ℤ), is_trunc (maxm2 (k + n)) (E n)

definition is_strunc_change_int {k l : ℤ} (E : spectrum) (p : k = l)
  : is_strunc k E → is_strunc l E :=
begin induction p, exact id end

definition is_strunc_strunc (k : ℤ) (E : spectrum)
  : is_strunc k (strunc k E) :=
λ n, is_trunc_trunc (maxm2 (k + n)) (E n)

definition is_trunc_maxm2_change_int {k l : ℤ} (X : pType) (p : k = l)
  : is_trunc (maxm2 k) X → is_trunc (maxm2 l) X :=
by induction p; exact id

definition strunc_functor [constructor] (k : ℤ) {E F : spectrum} (f : E →ₛ F) :
  strunc k E →ₛ strunc k F :=
smap.mk (λn, ptrunc_functor (maxm2 (k + n)) (f n)) sorry

definition is_strunc_EM_spectrum (G : AbGroup)
  : is_strunc 0 (EM_spectrum G) :=
begin
  intro n, induction n with n n,
  { -- case ≥ 0
    apply is_trunc_maxm2_change_int (EM G n) (zero_add n)⁻¹,
    apply is_trunc_EM },
  { change is_contr (EM_spectrum G (-[1+n])),
    induction n with n IH,
    { -- case = -1
      apply is_contr_loop, exact is_trunc_EM G 0 },
    { -- case < -1
      apply is_trunc_loop, apply is_trunc_succ, exact IH }}
end

definition strunc_elim [constructor] {k : ℤ} {E F : spectrum} (f : E →ₛ F)
  (H : is_strunc k F) : strunc k E →ₛ F :=
smap.mk (λn, ptrunc.elim (maxm2 (k + n)) (f n))
        (λn, sorry)

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
  (is_trunc_of_is_trunc_maxm2 m (E (2 - k)) (K (2 - k)))
  (nat.succ_le_succ (max0_le_of_le (le_sub_one_of_lt I)))

definition str [constructor] (k : ℤ) (E : spectrum) : E →ₛ strunc k E :=
smap.mk (λ n, ptr (maxm2 (k + n)) (E n))
  (λ n, sorry)

end spectrum
