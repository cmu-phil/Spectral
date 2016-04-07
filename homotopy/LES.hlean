import .LES_of_homotopy_groups
open eq pointed is_trunc trunc_index trunc group is_equiv equiv algebra prod fin fiber nat
     succ_str chain_complex

/--------------
    PART 3'
 --------------/

namespace chain_complex'

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)

  definition homotopy_groups2 [reducible] : +3ℕ → Type*
  | (n, fin.mk 0 H) := Ω[n] Y
  | (n, fin.mk 1 H) := Ω[n] X
  | (n, fin.mk k H) := Ω[n] (pfiber f)

  definition homotopy_groups2_add1 (n : ℕ) : Π(x : fin (succ 2)),
    homotopy_groups2 (n+1, x) = Ω(homotopy_groups2 (n, x))
  | (fin.mk 0 H) := by reflexivity
  | (fin.mk 1 H) := by reflexivity
  | (fin.mk 2 H) := by reflexivity
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun2 : Π(n : +3ℕ), homotopy_groups2 (S n) →* homotopy_groups2 n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof Ω→[n] (boundary_map f) ∘* pcast (loop_space_succ_eq_in Y n) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun2_add1_0 (n : ℕ) (H : 0 < succ 2)
    : homotopy_groups_fun2 (n+1, fin.mk 0 H) ~*
      cast proof idp qed ap1 (homotopy_groups_fun2 (n, fin.mk 0 H)) :=
  by reflexivity

  definition homotopy_groups_fun2_add1_1 (n : ℕ) (H : 1 < succ 2)
    : homotopy_groups_fun2 (n+1, fin.mk 1 H) ~*
      cast proof idp qed ap1 (homotopy_groups_fun2 (n, fin.mk 1 H)) :=
  by reflexivity

  definition homotopy_groups_fun2_add1_2 (n : ℕ) (H : 2 < succ 2)
    : homotopy_groups_fun2 (n+1, fin.mk 2 H) ~*
      cast proof idp qed ap1 (homotopy_groups_fun2 (n, fin.mk 2 H)) :=
  begin
    esimp,
    refine _ ⬝* !ap1_compose⁻¹*,
    exact pwhisker_left _ !pcast_ap_loop_space,
  end
exit
  definition nat_of_str_3S [unfold 2] [reducible]
    : Π(x : stratified +ℕ 2), nat_of_str x + 1 = nat_of_str (@S (stratified +ℕ 2) x)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups2_pequiv : Π(x : +3ℕ),
    homotopy_groups (nat_of_str x) ≃* homotopy_groups2 x
  |  (0,    (fin.mk 0 H))     := by reflexivity
  |  (0,    (fin.mk 1 H))     := by reflexivity
  |  (0,    (fin.mk 2 H))     := by reflexivity
  | ((n+1), (fin.mk 0 H))     :=
    begin
      -- uncomment the next two lines to have prettier subgoals
      -- esimp, replace (succ 5 * (n + 1) + 0) with (6*n+3+3),
      -- rewrite [+homotopy_groups_add3, homotopy_groups2_add1],
      apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv (n, fin.mk 0 H)
    end
  | ((n+1), (fin.mk 1 H))     :=
    begin
      apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv (n, fin.mk 1 H)
    end
  | ((n+1), (fin.mk 2 H))     :=
    begin
      apply loop_pequiv_loop,
      rexact homotopy_groups2_pequiv (n, fin.mk 2 H)
    end
  | (n,     (fin.mk (k+3) H)) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end
--  | (n, x) := homotopy_groups2_pequiv' n x

  /- all cases where n>0 are basically the same -/
  definition homotopy_groups_fun2_phomotopy (x : +6ℕ) :
    homotopy_groups2_pequiv x ∘* homotopy_groups_fun (nat_of_str x) ~*
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
        { exact !comp_pid⁻¹*},
        { refine cast (ap (λx, _ ~* loop_pequiv_loop x) !loopn_pequiv_loopn_rfl)⁻¹ _,
          refine cast (ap (λx, _ ~* x) !loopn_pequiv_loopn_rfl)⁻¹ _, reflexivity}},
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
    apply is_exact_at_transfer2,
    apply is_exact_type_LES_of_homotopy_groups
  end

  definition LES_of_homotopy_groups2 [constructor] : chain_complex +6ℕ :=
  trunc_chain_complex type_LES_of_homotopy_groups2

/--------------
    PART 4'
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
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[2 * (k + 1)] boundary_map f) _ _ _,
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

end chain_complex'
