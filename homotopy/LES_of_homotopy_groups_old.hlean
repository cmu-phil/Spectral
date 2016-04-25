/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

The old formalization of the LES of homotopy groups, where all the odd levels have a composition
  with negation
-/

import homotopy.LES_of_homotopy_groups

open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc nat trunc algebra function

/--------------
    PART 1 is the same as the new formalization
 --------------/

namespace chain_complex

  namespace old
  universe variable u
  variables {X Y : pType.{u}} (f : X →* Y) (n : ℕ)
  include f


/--------------
    PART 2
 --------------/

  /- Now we are ready to define the long exact sequence of homotopy groups.
     First we define its carrier -/
  definition homotopy_groups : ℕ → Type*
  | 0     := Y
  | 1     := X
  | 2     := pfiber f
  | (k+3) := Ω (homotopy_groups k)

  definition homotopy_groups_add3 [unfold_full] :
    homotopy_groups f (n+3) = Ω (homotopy_groups f n) :=
  by reflexivity

  definition homotopy_groups_mul3
    : Πn, homotopy_groups f (3 * n) = Ω[n] Y :> Type*
  | 0     := proof rfl qed
  | (k+1) := proof ap (λX, Ω X) (homotopy_groups_mul3 k) qed

  definition homotopy_groups_mul3add1
    : Πn, homotopy_groups f (3 * n + 1) = Ω[n] X :> Type*
  | 0     := by reflexivity
  | (k+1) := proof ap (λX, Ω X) (homotopy_groups_mul3add1 k) qed

  definition homotopy_groups_mul3add2
    : Πn, homotopy_groups f (3 * n + 2) = Ω[n] (pfiber f) :> Type*
  | 0     := by reflexivity
  | (k+1) := proof ap (λX, Ω X) (homotopy_groups_mul3add2 k) qed

  /- The maps between the homotopy groups -/
  definition homotopy_groups_fun
    : Π(n : ℕ), homotopy_groups f (n+1) →* homotopy_groups f n
  | 0     := proof f qed
  | 1     := proof ppoint f qed
  | 2     := proof boundary_map f qed
  | 3     := proof ap1 f ∘* pinverse qed
  | 4     := proof ap1 (ppoint f) ∘* pinverse qed
  | 5     := proof ap1 (boundary_map f) ∘* pinverse qed
  | (k+6) := proof ap1 (ap1 (homotopy_groups_fun k)) qed

  definition homotopy_groups_fun_add6 [unfold_full] :
    homotopy_groups_fun f (n + 6) = ap1 (ap1 (homotopy_groups_fun f n)) :=
  proof idp qed

  /- this is a simpler defintion of the functions, but which are the same as the previous ones
     (there is a pointed homotopy) -/
  definition homotopy_groups_fun'
    : Π(n : ℕ), homotopy_groups f (n+1) →* homotopy_groups f n
  | 0     := proof f qed
  | 1     := proof ppoint f qed
  | 2     := proof boundary_map f qed
  | (k+3) := proof ap1 (homotopy_groups_fun' k) ∘* pinverse qed

  definition homotopy_groups_fun'_add3 [unfold_full] :
    homotopy_groups_fun' f (n+3) = ap1 (homotopy_groups_fun' f n) ∘* pinverse :=
  proof idp qed

  theorem homotopy_groups_fun_eq
    : Π(n : ℕ), homotopy_groups_fun f n ~* homotopy_groups_fun' f n
  | 0     := by reflexivity
  | 1     := by reflexivity
  | 2     := by reflexivity
  | 3     := by reflexivity
  | 4     := by reflexivity
  | 5     := by reflexivity
  | (k+6) :=
    begin
      rewrite [homotopy_groups_fun_add6 f k],
      replace (k + 6) with (k + 3 + 3),
      rewrite [homotopy_groups_fun'_add3 f (k+3)],
      rewrite [homotopy_groups_fun'_add3 f k],
      refine _ ⬝* pwhisker_right _ !ap1_compose⁻¹*,
      refine _ ⬝* !passoc⁻¹*,
      refine !comp_pid⁻¹* ⬝* _,
      refine pconcat2 _ _,
      /- Currently ap1_phomotopy is defined using function extensionality -/
      { apply ap1_phomotopy, apply pap ap1, apply homotopy_groups_fun_eq},
      { refine _ ⬝* (pwhisker_right _ ap1_pinverse)⁻¹*, fapply phomotopy.mk,
        { intro q, esimp, exact !inv_inv⁻¹},
        { reflexivity}}
    end

  definition homotopy_groups_fun_add3 :
    homotopy_groups_fun f (n + 3) ~* ap1 (homotopy_groups_fun f n)  ∘* pinverse :=
  begin
    refine homotopy_groups_fun_eq f (n+3) ⬝* _,
    exact pwhisker_right _ (ap1_phomotopy (homotopy_groups_fun_eq f n)⁻¹*),
  end

  definition fiber_sequence_pequiv_homotopy_groups :
    Πn, fiber_sequence_carrier f n ≃* homotopy_groups f n
  | 0     := by reflexivity
  | 1     := by reflexivity
  | 2     := by reflexivity
  | (k+3) :=
    begin
      refine fiber_sequence_carrier_pequiv f k ⬝e* _,
      apply loop_pequiv_loop,
      exact fiber_sequence_pequiv_homotopy_groups k
    end

  definition fiber_sequence_pequiv_homotopy_groups_add3
    : fiber_sequence_pequiv_homotopy_groups f (n + 3) =
      ap1 (fiber_sequence_pequiv_homotopy_groups f n) ∘* fiber_sequence_carrier_pequiv f n :=
  by reflexivity

  definition fiber_sequence_pequiv_homotopy_groups_3_phomotopy
    : fiber_sequence_pequiv_homotopy_groups f 3 ~* fiber_sequence_carrier_pequiv f 0 :=
  begin
    refine fiber_sequence_pequiv_homotopy_groups_add3 f 0 ⬝p* _,
    refine pwhisker_right _ ap1_id ⬝* _,
    apply pid_comp
  end

  theorem fiber_sequence_phomotopy_homotopy_groups' :
    Π(n : ℕ),
    fiber_sequence_pequiv_homotopy_groups f n ∘* fiber_sequence_fun f n ~*
      homotopy_groups_fun' f n ∘* fiber_sequence_pequiv_homotopy_groups f (n + 1)
  | 0     := by reflexivity
  | 1     := by reflexivity
  | 2     :=
    begin
      refine !pid_comp ⬝* _,
      replace homotopy_groups_fun' f 2 with boundary_map f,
      refine _ ⬝* pwhisker_left _ (fiber_sequence_pequiv_homotopy_groups_3_phomotopy f)⁻¹*,
      apply phomotopy_of_pinv_right_phomotopy,
      reflexivity
    end
  | (k+3) :=
    begin
      replace (k + 3 + 1) with (k + 1 + 3),
      rewrite [fiber_sequence_pequiv_homotopy_groups_add3 f k,
               fiber_sequence_pequiv_homotopy_groups_add3 f (k+1)],
      refine !passoc ⬝* _,
      refine pwhisker_left _ (fiber_sequence_fun_phomotopy f k) ⬝* _,
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
      apply pwhisker_right,
      rewrite [homotopy_groups_fun'_add3],
      refine _ ⬝* !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ !ap1_compose_pinverse,
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
      apply pwhisker_right,
      refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose,
      apply ap1_phomotopy,
      exact fiber_sequence_phomotopy_homotopy_groups' k
    end

  theorem fiber_sequence_phomotopy_homotopy_groups (n : ℕ)
    (x : fiber_sequence_carrier f (n + 1)) :
    fiber_sequence_pequiv_homotopy_groups f n (fiber_sequence_fun f n x) =
      homotopy_groups_fun f n (fiber_sequence_pequiv_homotopy_groups f (n + 1) x) :=
  begin
    refine fiber_sequence_phomotopy_homotopy_groups' f n x ⬝ _,
    exact (homotopy_groups_fun_eq f n _)⁻¹
  end

  definition type_LES_of_homotopy_groups [constructor] : type_chain_complex +ℕ :=
  transfer_type_chain_complex
    (fiber_sequence f)
    (homotopy_groups_fun f)
    (fiber_sequence_pequiv_homotopy_groups f)
    (fiber_sequence_phomotopy_homotopy_groups f)

  definition is_exact_type_LES_of_homotopy_groups : is_exact_t (type_LES_of_homotopy_groups f) :=
  begin
    intro n,
    apply is_exact_at_t_transfer,
    apply is_exact_fiber_sequence
  end

  /- the long exact sequence of homotopy groups -/
  definition LES_of_homotopy_groups [constructor] : chain_complex +ℕ :=
  trunc_chain_complex
    (transfer_type_chain_complex
      (fiber_sequence f)
      (homotopy_groups_fun f)
      (fiber_sequence_pequiv_homotopy_groups f)
      (fiber_sequence_phomotopy_homotopy_groups f))

  /- the fiber sequence is exact -/
  definition is_exact_LES_of_homotopy_groups : is_exact (LES_of_homotopy_groups f) :=
  begin
    intro n,
    apply is_exact_at_trunc,
    apply is_exact_type_LES_of_homotopy_groups
  end

  /- for a numeral, the carrier of the fiber sequence is definitionally what we want
     (as pointed sets) -/
  example : LES_of_homotopy_groups f 6 = π*[2] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups f 7 = π*[2] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups f 8 = π*[2] (pfiber f) :> Set* := by reflexivity

  /- for a numeral, the functions of the fiber sequence is definitionally what we want
     (as pointed function). All these functions have at most one "pinverse" in them, and these
     inverses are inside the π→*[2*k].
  -/
  example : cc_to_fn (LES_of_homotopy_groups f)  6 = π→*[2] f
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_homotopy_groups f)  7 = π→*[2] (ppoint f)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_homotopy_groups f)  8 = π→*[2] (boundary_map f)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_homotopy_groups f)  9 = π→*[2] (ap1 f ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_homotopy_groups f) 10 = π→*[2] (ap1 (ppoint f) ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_homotopy_groups f) 11 = π→*[2] (ap1 (boundary_map f) ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_homotopy_groups f) 12 = π→*[4] f
    :> (_ →* _) := by reflexivity

  /- the carrier of the fiber sequence is what we want for natural numbers of the form
     3n, 3n+1 and 3n+2 -/
  definition LES_of_homotopy_groups_mul3 (n : ℕ)
    : LES_of_homotopy_groups f (3 * n) = π*[n] Y :> Set* :=
  begin
   apply ptrunctype_eq_of_pType_eq,
   exact ap (ptrunc 0) (homotopy_groups_mul3 f n)
  end

  definition LES_of_homotopy_groups_mul3add1 (n : ℕ)
    : LES_of_homotopy_groups f (3 * n + 1) = π*[n] X :> Set* :=
  begin
   apply ptrunctype_eq_of_pType_eq,
   exact ap (ptrunc 0) (homotopy_groups_mul3add1 f n)
  end

  definition LES_of_homotopy_groups_mul3add2 (n : ℕ)
    : LES_of_homotopy_groups f (3 * n + 2) = π*[n] (pfiber f) :> Set* :=
  begin
   apply ptrunctype_eq_of_pType_eq,
   exact ap (ptrunc 0) (homotopy_groups_mul3add2 f n)
  end

  definition LES_of_homotopy_groups_mul3' (n : ℕ)
    : LES_of_homotopy_groups f (3 * n) = π*[n] Y :> Type :=
  begin
   exact ap (ptrunc 0) (homotopy_groups_mul3 f n)
  end

  definition LES_of_homotopy_groups_mul3add1' (n : ℕ)
    : LES_of_homotopy_groups f (3 * n + 1) = π*[n] X :> Type :=
  begin
   exact ap (ptrunc 0) (homotopy_groups_mul3add1 f n)
  end

  definition LES_of_homotopy_groups_mul3add2' (n : ℕ)
    : LES_of_homotopy_groups f (3 * n + 2) = π*[n] (pfiber f) :> Type :=
  begin
   exact ap (ptrunc 0) (homotopy_groups_mul3add2 f n)
  end

  definition group_LES_of_homotopy_groups (n : ℕ) : group (LES_of_homotopy_groups f (n + 3)) :=
  group_homotopy_group 0 (homotopy_groups f n)

  definition comm_group_LES_of_homotopy_groups (n : ℕ) : comm_group (LES_of_homotopy_groups f (n + 6)) :=
  comm_group_homotopy_group 0 (homotopy_groups f n)

end old end chain_complex

open group prod succ_str fin

/--------------
    PART 3
 --------------/

namespace chain_complex namespace old

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)

  definition homotopy_groups2 [reducible] : +6ℕ → Type*
  | (n, fin.mk 0 H) := Ω[2*n] Y
  | (n, fin.mk 1 H) := Ω[2*n] X
  | (n, fin.mk 2 H) := Ω[2*n] (pfiber f)
  | (n, fin.mk 3 H) := Ω[2*n + 1] Y
  | (n, fin.mk 4 H) := Ω[2*n + 1] X
  | (n, fin.mk k H) := Ω[2*n + 1] (pfiber f)

  definition homotopy_groups2_add1 (n : ℕ) : Π(x : fin (succ 5)),
    homotopy_groups2 (n+1, x) = Ω Ω(homotopy_groups2 (n, x))
  | (fin.mk 0 H) := by reflexivity
  | (fin.mk 1 H) := by reflexivity
  | (fin.mk 2 H) := by reflexivity
  | (fin.mk 3 H) := by reflexivity
  | (fin.mk 4 H) := by reflexivity
  | (fin.mk 5 H) := by reflexivity
  | (fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun2 : Π(n : +6ℕ), homotopy_groups2 (S n) →* homotopy_groups2 n
  | (n, fin.mk 0 H) := proof Ω→[2*n] f qed
  | (n, fin.mk 1 H) := proof Ω→[2*n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof Ω→[2*n] (boundary_map f) ∘* pcast (loop_space_succ_eq_in Y (2*n)) qed
  | (n, fin.mk 3 H) := proof Ω→[2*n + 1] f ∘* pinverse qed
  | (n, fin.mk 4 H) := proof Ω→[2*n + 1] (ppoint f) ∘* pinverse qed
  | (n, fin.mk 5 H) :=
    proof (Ω→[2*n + 1] (boundary_map f) ∘* pinverse) ∘* pcast (loop_space_succ_eq_in Y (2*n+1)) qed
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun2_add1_0 (n : ℕ) (H : 0 < succ 5)
    : homotopy_groups_fun2 (n+1, fin.mk 0 H) ~*
      cast proof idp qed ap1 (ap1 (homotopy_groups_fun2 (n, fin.mk 0 H))) :=
  by reflexivity

  definition homotopy_groups_fun2_add1_1 (n : ℕ) (H : 1 < succ 5)
    : homotopy_groups_fun2 (n+1, fin.mk 1 H) ~*
      cast proof idp qed ap1 (ap1 (homotopy_groups_fun2 (n, fin.mk 1 H))) :=
  by reflexivity

  definition homotopy_groups_fun2_add1_2 (n : ℕ) (H : 2 < succ 5)
    : homotopy_groups_fun2 (n+1, fin.mk 2 H) ~*
      cast proof idp qed ap1 (ap1 (homotopy_groups_fun2 (n, fin.mk 2 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    refine !pcast_ap_loop_space ⬝* ap1_phomotopy !pcast_ap_loop_space,
  end

  definition homotopy_groups_fun2_add1_3 (n : ℕ) (H : 3 < succ 5)
    : homotopy_groups_fun2 (n+1, fin.mk 3 H) ~*
      cast proof idp qed ap1 (ap1 (homotopy_groups_fun2 (n, fin.mk 3 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    exact ap1_pinverse⁻¹* ⬝* ap1_phomotopy !ap1_pinverse⁻¹*
  end

  definition homotopy_groups_fun2_add1_4 (n : ℕ) (H : 4 < succ 5)
    : homotopy_groups_fun2 (n+1, fin.mk 4 H) ~*
      cast proof idp qed ap1 (ap1 (homotopy_groups_fun2 (n, fin.mk 4 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    exact ap1_pinverse⁻¹* ⬝* ap1_phomotopy !ap1_pinverse⁻¹*
  end

  definition homotopy_groups_fun2_add1_5 (n : ℕ) (H : 5 < succ 5)
    : homotopy_groups_fun2 (n+1, fin.mk 5 H) ~*
      cast proof idp qed ap1 (ap1 (homotopy_groups_fun2 (n, fin.mk 5 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pconcat2,
    { esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
      apply pwhisker_left,
      exact ap1_pinverse⁻¹* ⬝* ap1_phomotopy !ap1_pinverse⁻¹*},
    { refine !pcast_ap_loop_space ⬝* ap1_phomotopy !pcast_ap_loop_space}
  end

  definition nat_of_str [unfold 2] [reducible] {n : ℕ} : ℕ × fin (succ n) → ℕ :=
  λx, succ n * pr1 x + val (pr2 x)

  definition str_of_nat {n : ℕ} : ℕ → ℕ × fin (succ n) :=
  λm, (m / (succ n), mk_mod n m)

  definition nat_of_str_6S [unfold 2] [reducible]
    : Π(x : stratified +ℕ 5), nat_of_str x + 1 = nat_of_str (@S (stratified +ℕ 5) x)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk 3 H) := by reflexivity
  | (n, fin.mk 4 H) := by reflexivity
  | (n, fin.mk 5 H) := by reflexivity
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition fin_prod_nat_equiv_nat [constructor] (n : ℕ) : ℕ × fin (succ n) ≃ ℕ :=
  equiv.MK nat_of_str str_of_nat
    abstract begin
      intro m, unfold [nat_of_str, str_of_nat, mk_mod],
      refine _ ⬝ (eq_div_mul_add_mod m (succ n))⁻¹,
      rewrite [mul.comm]
    end end
    abstract begin
      intro x, cases x with m k,
      cases k with k H,
      apply prod_eq: esimp [str_of_nat],
      { rewrite [add.comm, add_mul_div_self_left _ _ (!zero_lt_succ),
                 div_eq_zero_of_lt H, zero_add]},
      { apply eq_of_veq, esimp [mk_mod],
        rewrite [add.comm, add_mul_mod_self_left, mod_eq_of_lt H]}
    end end

  /-
    note: in the following theorem the (n+1) case is 6 times the same,
    so maybe this can be simplified
  -/
  definition homotopy_groups2_pequiv' : Π(n : ℕ) (x : fin (nat.succ 5)),
    homotopy_groups f (nat_of_str (n, x)) ≃* homotopy_groups2 (n, x)
  |  0    (fin.mk 0 H)     := by reflexivity
  |  0    (fin.mk 1 H)     := by reflexivity
  |  0    (fin.mk 2 H)     := by reflexivity
  |  0    (fin.mk 3 H)     := by reflexivity
  |  0    (fin.mk 4 H)     := by reflexivity
  |  0    (fin.mk 5 H)     := by reflexivity
  | (n+1) (fin.mk 0 H)     :=
    begin
      -- uncomment the next two lines to have prettier subgoals
      -- esimp, replace (succ 5 * (n + 1) + 0) with (6*n+3+3),
      -- rewrite [+homotopy_groups_add3, homotopy_groups2_add1],
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv' n (fin.mk 0 H)
    end
  | (n+1) (fin.mk 1 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv' n (fin.mk 1 H)
    end
  | (n+1) (fin.mk 2 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv' n (fin.mk 2 H)
    end
  | (n+1) (fin.mk 3 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv' n (fin.mk 3 H)
    end
  | (n+1) (fin.mk 4 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv' n (fin.mk 4 H)
    end
  | (n+1) (fin.mk 5 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv' n (fin.mk 5 H)
    end
  | n     (fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups2_pequiv : Π(x : +6ℕ),
    homotopy_groups f (nat_of_str x) ≃* homotopy_groups2 x
  | (n, x) := homotopy_groups2_pequiv' n x

  /- all cases where n>0 are basically the same -/
  definition homotopy_groups_fun2_phomotopy (x : +6ℕ) :
    homotopy_groups2_pequiv x ∘* homotopy_groups_fun f (nat_of_str x) ~*
      (homotopy_groups_fun2 x ∘* homotopy_groups2_pequiv (S x))
    ∘* pcast (ap (homotopy_groups f) (nat_of_str_6S x)) :=
  begin
    cases x with n x, cases x with k H,
    cases k with k, rotate 1, cases k with k, rotate 1, cases k with k, rotate 1,
    cases k with k, rotate 1, cases k with k, rotate 1, cases k with k, rotate 2,
    { /-k=0-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!homotopy_groups_fun2_add1_0)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=1-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!homotopy_groups_fun2_add1_1)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=2-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        refine _ ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!homotopy_groups_fun2_add1_2)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=3-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!homotopy_groups_fun2_add1_3)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=4-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!homotopy_groups_fun2_add1_4)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=5-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
        refine !comp_pid⁻¹* ⬝* pconcat2 _ _,
        { exact (comp_pid (ap1 (boundary_map f) ∘* pinverse))⁻¹*},
        { refine cast (ap (λx, _ ~* loop_pequiv_loop x) !loop_pequiv_loop_rfl)⁻¹ _,
          refine cast (ap (λx, _ ~* x) !loop_pequiv_loop_rfl)⁻¹ _, reflexivity}},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!homotopy_groups_fun2_add1_5)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=k'+6-/ exfalso, apply lt_le_antisymm H, apply le_add_left}
  end

  definition type_LES_of_homotopy_groups2 [constructor] : type_chain_complex +6ℕ :=
  transfer_type_chain_complex2
    (type_LES_of_homotopy_groups f)
    !fin_prod_nat_equiv_nat
    nat_of_str_6S
    @homotopy_groups_fun2
    @homotopy_groups2_pequiv
    begin
      intro m x,
      refine homotopy_groups_fun2_phomotopy m x ⬝ _,
      apply ap (homotopy_groups_fun2 m), apply ap (homotopy_groups2_pequiv (S m)),
      esimp, exact ap010 cast !ap_compose⁻¹ x
    end

  definition is_exact_type_LES_of_homotopy_groups2 : is_exact_t (type_LES_of_homotopy_groups2) :=
  begin
    intro n,
    apply is_exact_at_t_transfer2,
    apply is_exact_type_LES_of_homotopy_groups
  end

  definition LES_of_homotopy_groups2 [constructor] : chain_complex +6ℕ :=
  trunc_chain_complex type_LES_of_homotopy_groups2

/--------------
    PART 4
 --------------/

  definition homotopy_groups3 [reducible] : +6ℕ → Set*
  | (n, fin.mk 0 H) := π*[2*n] Y
  | (n, fin.mk 1 H) := π*[2*n] X
  | (n, fin.mk 2 H) := π*[2*n] (pfiber f)
  | (n, fin.mk 3 H) := π*[2*n + 1] Y
  | (n, fin.mk 4 H) := π*[2*n + 1] X
  | (n, fin.mk k H) := π*[2*n + 1] (pfiber f)

  definition homotopy_groups3eq2 [reducible]
    : Π(n : +6ℕ), ptrunc 0 (homotopy_groups2 n) ≃* homotopy_groups3 n
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk 3 H) := by reflexivity
  | (n, fin.mk 4 H) := by reflexivity
  | (n, fin.mk 5 H) := by reflexivity
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun3 : Π(n : +6ℕ), homotopy_groups3 (S n) →* homotopy_groups3 n
  | (n, fin.mk 0 H) := proof π→*[2*n] f qed
  | (n, fin.mk 1 H) := proof π→*[2*n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof π→*[2*n] (boundary_map f) ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n))) qed
  | (n, fin.mk 3 H) := proof π→*[2*n + 1] f ∘* tinverse qed
  | (n, fin.mk 4 H) := proof π→*[2*n + 1] (ppoint f) ∘* tinverse qed
  | (n, fin.mk 5 H) :=
    proof (π→*[2*n + 1] (boundary_map f) ∘* tinverse)
          ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n+1))) qed
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun3eq2 [reducible]
    : Π(n : +6ℕ), homotopy_groups3eq2 n ∘* ptrunc_functor 0 (homotopy_groups_fun2 n) ~*
      homotopy_groups_fun3 n ∘* homotopy_groups3eq2 (S n)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pwhisker_left, apply ptrunc_functor_pcast,
    end
  | (n, fin.mk 3 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pwhisker_left, apply ptrunc_functor_pinverse
    end
  | (n, fin.mk 4 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pwhisker_left, apply ptrunc_functor_pinverse
    end
  | (n, fin.mk 5 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pconcat2,
      { refine !ptrunc_functor_pcompose ⬝* _,
        apply pwhisker_left, apply ptrunc_functor_pinverse},
      { apply ptrunc_functor_pcast}
    end
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition LES_of_homotopy_groups3 [constructor] : chain_complex +6ℕ :=
  transfer_chain_complex
    LES_of_homotopy_groups2
    homotopy_groups_fun3
    homotopy_groups3eq2
    homotopy_groups_fun3eq2

  definition is_exact_LES_of_homotopy_groups3 : is_exact (LES_of_homotopy_groups3) :=
  begin
    intro n,
    apply is_exact_at_transfer,
    apply is_exact_at_trunc,
    apply is_exact_type_LES_of_homotopy_groups2
  end

  end

  open is_trunc
  universe variable u
  variables {X Y : pType.{u}} (f : X →* Y) (n : ℕ)
  include f

  /- the carrier of the fiber sequence is definitionally what we want (as pointed sets) -/
  example : LES_of_homotopy_groups3 f (str_of_nat 6)  = π*[2] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups3 f (str_of_nat 7)  = π*[2] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups3 f (str_of_nat 8)  = π*[2] (pfiber f) :> Set* := by reflexivity
  example : LES_of_homotopy_groups3 f (str_of_nat 9)  = π*[3] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups3 f (str_of_nat 10) = π*[3] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups3 f (str_of_nat 11) = π*[3] (pfiber f) :> Set* := by reflexivity

  definition LES_of_homotopy_groups3_0 : LES_of_homotopy_groups3 f (n, 0) = π*[2*n] Y :=
  by reflexivity
  definition LES_of_homotopy_groups3_1 : LES_of_homotopy_groups3 f (n, 1) = π*[2*n] X :=
  by reflexivity
  definition LES_of_homotopy_groups3_2 : LES_of_homotopy_groups3 f (n, 2) = π*[2*n] (pfiber f) :=
  by reflexivity
  definition LES_of_homotopy_groups3_3 : LES_of_homotopy_groups3 f (n, 3) = π*[2*n + 1] Y :=
  by reflexivity
  definition LES_of_homotopy_groups3_4 : LES_of_homotopy_groups3 f (n, 4) = π*[2*n + 1] X :=
  by reflexivity
  definition LES_of_homotopy_groups3_5 : LES_of_homotopy_groups3 f (n, 5) = π*[2*n + 1] (pfiber f):=
  by reflexivity

  /- the functions of the fiber sequence is definitionally what we want (as pointed function).
      -/

  definition LES_of_homotopy_groups_fun3_0 :
    cc_to_fn (LES_of_homotopy_groups3 f) (n, 0) = π→*[2*n] f :=
  by reflexivity
  definition LES_of_homotopy_groups_fun3_1 :
    cc_to_fn (LES_of_homotopy_groups3 f) (n, 1) = π→*[2*n] (ppoint f) :=
  by reflexivity
  definition LES_of_homotopy_groups_fun3_2 : cc_to_fn (LES_of_homotopy_groups3 f) (n, 2) =
    π→*[2*n] (boundary_map f) ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n))) :=
  by reflexivity
  definition LES_of_homotopy_groups_fun3_3 :
    cc_to_fn (LES_of_homotopy_groups3 f) (n, 3) = π→*[2*n + 1] f ∘* tinverse :=
  by reflexivity
  definition LES_of_homotopy_groups_fun3_4 :
    cc_to_fn (LES_of_homotopy_groups3 f) (n, 4) = π→*[2*n + 1] (ppoint f) ∘* tinverse :=
  by reflexivity
  definition LES_of_homotopy_groups_fun3_5 : cc_to_fn (LES_of_homotopy_groups3 f) (n, 5) =
    (π→*[2*n + 1] (boundary_map f) ∘* tinverse) ∘*
    pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n+1))) :=
  by reflexivity

  definition group_LES_of_homotopy_groups3_0 :
    Π(k : ℕ) (H : k + 3 < succ 5), group (LES_of_homotopy_groups3 f (0, fin.mk (k+3) H))
  | 0     H := begin rexact group_homotopy_group 0 Y end
  | 1     H := begin rexact group_homotopy_group 0 X end
  | 2     H := begin rexact group_homotopy_group 0 (pfiber f) end
  | (k+3) H := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition comm_group_LES_of_homotopy_groups3 (n : ℕ) : Π(x : fin (succ 5)),
    comm_group (LES_of_homotopy_groups3 f (n + 1, x))
  | (fin.mk 0 H) := proof comm_group_homotopy_group (2*n) Y qed
  | (fin.mk 1 H) := proof comm_group_homotopy_group (2*n) X qed
  | (fin.mk 2 H) := proof comm_group_homotopy_group (2*n) (pfiber f) qed
  | (fin.mk 3 H) := proof comm_group_homotopy_group (2*n+1) Y qed
  | (fin.mk 4 H) := proof comm_group_homotopy_group (2*n+1) X qed
  | (fin.mk 5 H) := proof comm_group_homotopy_group (2*n+1) (pfiber f) qed
  | (fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition CommGroup_LES_of_homotopy_groups3 (n : +6ℕ) : CommGroup.{u} :=
  CommGroup.mk (LES_of_homotopy_groups3 f (pr1 n + 1, pr2 n))
               (comm_group_LES_of_homotopy_groups3 f (pr1 n) (pr2 n))

  definition homomorphism_LES_of_homotopy_groups_fun3 : Π(k : +6ℕ),
    CommGroup_LES_of_homotopy_groups3 f (S k) →g CommGroup_LES_of_homotopy_groups3 f k
  | (k, fin.mk 0 H) :=
    proof homomorphism.mk (cc_to_fn (LES_of_homotopy_groups3 f) (k + 1, 0))
                          (phomotopy_group_functor_mul _ _) qed
  | (k, fin.mk 1 H) :=
    proof homomorphism.mk (cc_to_fn (LES_of_homotopy_groups3 f) (k + 1, 1))
                          (phomotopy_group_functor_mul _ _) qed
  | (k, fin.mk 2 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_homotopy_groups3 f) (k + 1, 2)),
      exact abstract begin rewrite [LES_of_homotopy_groups_fun3_2],
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[2 * (k + 1)] (boundary_map f)) _ _ _,
      { apply group_homotopy_group ((2 * k) + 1)},
      { apply phomotopy_group_functor_mul},
      { rewrite [▸*, -ap_compose', ▸*],
        apply is_homomorphism_cast_loop_space_succ_eq_in} end end
    end
  | (k, fin.mk 3 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_homotopy_groups3 f) (k + 1, 3)),
      exact abstract begin rewrite [LES_of_homotopy_groups_fun3_3],
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[2 * (k + 1) + 1] f) tinverse _ _,
      { apply group_homotopy_group (2 * (k+1))},
      { apply phomotopy_group_functor_mul},
      { apply is_homomorphism_inverse} end end
    end
  | (k, fin.mk 4 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_homotopy_groups3 f) (k + 1, 4)),
      exact abstract begin rewrite [LES_of_homotopy_groups_fun3_4],
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[2 * (k + 1) + 1] (ppoint f)) tinverse _ _,
      { apply group_homotopy_group (2 * (k+1))},
      { apply phomotopy_group_functor_mul},
      { apply is_homomorphism_inverse} end end
    end
  | (k, fin.mk 5 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_homotopy_groups3 f) (k + 1, 5)),
      exact abstract begin rewrite [LES_of_homotopy_groups_fun3_5],
      refine @is_homomorphism_compose _ _ _ _ _ _
               (π→*[2 * (k + 1) + 1] (boundary_map f) ∘ tinverse) _ _ _,
      { refine @is_homomorphism_compose _ _ _ _ _ _
                 (π→*[2 * (k + 1) + 1] (boundary_map f)) tinverse _ _,
        { apply group_homotopy_group (2 * (k+1))},
        { apply phomotopy_group_functor_mul},
        { apply is_homomorphism_inverse}},
      { rewrite [▸*, -ap_compose', ▸*],
        apply is_homomorphism_cast_loop_space_succ_eq_in} end end
    end
  | (k, fin.mk (l+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  --TODO: the maps 3, 4 and 5 are anti-homomorphisms.

  end old
end chain_complex
