/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

We define the fiber sequence of a pointed map f : X →* Y. We follow the proof in section 8.4 of
the book closely. First we define a sequence fiber_sequence as in Definition 8.4.3.
It has types X(n) : Type*
X(0)   := Y,
X(1)   := X,
X(n+1) := pfiber (f(n))
with functions f(n) : X(n+1) →* X(n)
f(0)   := f
f(n+1) := ppoint f(n)
We prove that this is an exact sequence.
Then we prove Lemma 8.4.3, by showing that X(n+3) ≃* Ω(X(n)) and that this equivalence sends
the map f(n+3) to -Ω(f(n)), i.e. the composition of Ω(f(n)) with path inversion.
This is the hardest part of this formalization, because we need to show that they are the same
as pointed maps (we define a pointed homotopy between them).

Using this equivalence we get a boundary_map : Ω(Y) → pfiber f and we can define a new
fiber sequence X'(n) : Type*
X'(0)   := Y,
X'(1)   := X,
X'(2)   := pfiber f
X'(n+3) := Ω(X'(n))
and maps f'(n) : X'(n+1) →* X'(n)
f'(0) := f
f'(1) := ppoint f
f'(2) := boundary_map f
f'(3) := -Ω(f)
f'(4) := -Ω(ppoint f)
f'(5) := -Ω(boundary_map f)
f'(n+6) := Ω²(f'(n))

We can show that these sequences are equivalent, hence the sequence (X',f') is an exact
sequence. Now we get the fiber sequence by taking the set-truncation of this sequence.

-/

import .chain_complex algebra.homotopy_group

open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc equiv.ops nat trunc algebra

namespace chain_complex

  definition fiber_sequence_helper [constructor] (v : Σ(X Y : Type*), X →* Y)
    : Σ(Z X : Type*), Z →* X :=
  ⟨pfiber v.2.2, v.1, ppoint v.2.2⟩

  definition fiber_sequence_helpern (v : Σ(X Y : Type*), X →* Y) (n : ℕ)
    : Σ(Z X : Type*), Z →* X :=
  iterate fiber_sequence_helper n v

  universe variable u
  variables {X Y : pType.{u}} (f : X →* Y) (n : ℕ)
  include f

  definition fiber_sequence_carrier : Type* :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.1

  definition fiber_sequence_fun
    : fiber_sequence_carrier f (n + 1) →* fiber_sequence_carrier f n :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.2

  /- Definition 8.4.3 -/
  definition fiber_sequence : left_type_chain_complex.{u} :=
  begin
    fconstructor,
    { exact fiber_sequence_carrier f},
    { exact fiber_sequence_fun f},
    { intro n x, cases n with n,
      { exact point_eq x},
      { exact point_eq x}}
  end

  definition is_exact_fiber_sequence : is_exact_lt (fiber_sequence f) :=
  λn x p, fiber.mk (fiber.mk x p) rfl

  /- (generalization of) Lemma 8.4.4(i)(ii) -/
  definition fiber_sequence_carrier_equiv
    : fiber_sequence_carrier f (n+3) ≃ Ω(fiber_sequence_carrier f n) :=
  calc
    fiber_sequence_carrier f (n+3) ≃ fiber (fiber_sequence_fun f (n+1)) pt : erfl
    ... ≃ Σ(x : fiber_sequence_carrier f _), fiber_sequence_fun f (n+1) x = pt
      : fiber.sigma_char
    ... ≃ Σ(x : fiber (fiber_sequence_fun f n) pt), fiber_sequence_fun f _ x = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), fiber_sequence_fun f _ x = pt),
            fiber_sequence_fun f _ (fiber.mk v.1 v.2) = pt
      : by exact sigma_equiv_sigma !fiber.sigma_char (λa, erfl)
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), fiber_sequence_fun f _ x = pt),
            v.1 = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier f _), x = pt),
            fiber_sequence_fun f _ v.1 = pt
      : sigma_assoc_comm_equiv
    ... ≃ fiber_sequence_fun f _ !center.1 = pt
      : @(sigma_equiv_of_is_contr_left _) !is_contr_sigma_eq'
    ... ≃ fiber_sequence_fun f _ pt = pt
      : erfl
    ... ≃ pt = pt
      : by exact !equiv_eq_closed_left !respect_pt
    ... ≃ Ω(fiber_sequence_carrier f n) : erfl

  /- computation rule -/
  definition fiber_sequence_carrier_equiv_eq
    (x : fiber_sequence_carrier f (n+1)) (p : fiber_sequence_fun f n x = pt)
    (q : fiber_sequence_fun f (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_equiv f n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun f n) q⁻¹ ⬝ p :=
  begin
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    refine transport_eq_Fl _ _ ⬝ _,
    apply whisker_right,
    refine inverse2 !ap_inv ⬝ !inv_inv ⬝ _,
    refine ap_compose (fiber_sequence_fun f n) pr₁ _ ⬝
           ap02 (fiber_sequence_fun f n) !ap_pr1_center_eq_sigma_eq',
  end

  definition fiber_sequence_carrier_equiv_inv_eq
    (p : Ω(fiber_sequence_carrier f n)) : (fiber_sequence_carrier_equiv f n)⁻¹ᵉ p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun f n) ⬝ p)) idp :=
  begin
    apply inv_eq_of_eq,
    refine _ ⬝ !fiber_sequence_carrier_equiv_eq⁻¹, esimp,
    exact !inv_con_cancel_left⁻¹
  end

  definition fiber_sequence_carrier_pequiv
    : fiber_sequence_carrier f (n+3) ≃* Ω(fiber_sequence_carrier f n) :=
  pequiv_of_equiv (fiber_sequence_carrier_equiv f n)
    begin
      esimp,
      apply con.left_inv
    end

  definition fiber_sequence_carrier_pequiv_eq
    (x : fiber_sequence_carrier f (n+1)) (p : fiber_sequence_fun f n x = pt)
    (q : fiber_sequence_fun f (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_pequiv f n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun f n) q⁻¹ ⬝ p :=
  fiber_sequence_carrier_equiv_eq f n x p q

  definition fiber_sequence_carrier_pequiv_inv_eq
    (p : Ω(fiber_sequence_carrier f n)) : (fiber_sequence_carrier_pequiv f n)⁻¹ᵉ* p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun f n) ⬝ p)) idp :=
  fiber_sequence_carrier_equiv_inv_eq f n p

  attribute pequiv._trans_of_to_pmap [unfold 3]

  /- Lemma 8.4.4(iii) -/
  definition fiber_sequence_fun_eq_helper
    (p : Ω(fiber_sequence_carrier f (n + 1))) :
    fiber_sequence_carrier_pequiv f n
      (fiber_sequence_fun f (n + 3)
        ((fiber_sequence_carrier_pequiv f (n + 1))⁻¹ᵉ* p)) =
          ap1 (fiber_sequence_fun f n) p⁻¹ :=
  begin
    refine ap (λx, fiber_sequence_carrier_pequiv f n (fiber_sequence_fun f (n + 3) x))
              (fiber_sequence_carrier_pequiv_inv_eq f (n+1) p) ⬝ _,
    /- the following three lines are rewriting some reflexivities: -/
    -- replace (n + 3) with (n + 2 + 1),
    -- refine ap (fiber_sequence_carrier_pequiv f n)
    --           (fiber_sequence_fun_eq1 f (n+2) _ idp) ⬝ _,
    refine fiber_sequence_carrier_pequiv_eq f n pt (respect_pt (fiber_sequence_fun f n)) _ ⬝ _,
    esimp,
    apply whisker_right,
    apply whisker_left,
    apply ap02, apply inverse2, apply idp_con,
  end

  theorem fiber_sequence_carrier_pequiv_eq_point_eq_idp :
    fiber_sequence_carrier_pequiv_eq f n
      (Point (fiber_sequence_carrier f (n+1)))
      (respect_pt (fiber_sequence_fun f n))
      (respect_pt (fiber_sequence_fun f (n + 1))) = idp :=
  begin
    apply con_inv_eq_idp,
    refine ap (λx, whisker_left _ (_ ⬝ x)) _ ⬝ _,
    { reflexivity},
    { reflexivity},
    esimp,
    refine ap (whisker_left _)
              (transport_eq_Fl_idp_left (fiber_sequence_fun f n)
                                        (respect_pt (fiber_sequence_fun f n))) ⬝ _,
    apply whisker_left_idp_con_eq_assoc
  end

  theorem fiber_sequence_fun_phomotopy_helper :
    (fiber_sequence_carrier_pequiv f n ∘*
      fiber_sequence_fun f (n + 3)) ∘*
        (fiber_sequence_carrier_pequiv f (n + 1))⁻¹ᵉ* ~*
          ap1 (fiber_sequence_fun f n) ∘* pinverse :=
  begin
    fapply phomotopy.mk,
    { exact (fiber_sequence_fun_eq_helper f n)},
    { esimp, rewrite [idp_con], refine _ ⬝ whisker_left _ !idp_con⁻¹,
      apply whisker_right,
      apply whisker_left,
      exact fiber_sequence_carrier_pequiv_eq_point_eq_idp f n}
  end

  theorem fiber_sequence_fun_eq : Π(x : fiber_sequence_carrier f (n + 4)),
    fiber_sequence_carrier_pequiv f n (fiber_sequence_fun f (n + 3) x) =
      ap1 (fiber_sequence_fun f n) (fiber_sequence_carrier_pequiv f (n + 1) x)⁻¹ :=
  homotopy_of_inv_homotopy
    (pequiv.to_equiv (fiber_sequence_carrier_pequiv f (n + 1)))
    (fiber_sequence_fun_eq_helper f n)

  theorem fiber_sequence_fun_phomotopy :
    fiber_sequence_carrier_pequiv f n ∘*
      fiber_sequence_fun f (n + 3) ~*
          (ap1 (fiber_sequence_fun f n) ∘* pinverse) ∘* fiber_sequence_carrier_pequiv f (n + 1) :=
  begin
    apply phomotopy_of_pinv_right_phomotopy,
    apply fiber_sequence_fun_phomotopy_helper
  end

  definition boundary_map : Ω Y →* pfiber f :=
  fiber_sequence_fun f 2 ∘* (fiber_sequence_carrier_pequiv f 0)⁻¹ᵉ*

  /- Now we are ready to define the long exact sequence of homotopy groups.
     First we define its carrier -/
  definition homotopy_groups : ℕ → Type*
  | 0     := Y
  | 1     := X
  | 2     := pfiber f
  | (k+3) := Ω (homotopy_groups k)

  definition homotopy_groups_add3 [unfold_full] :
    homotopy_groups f (n+3) = Ω (homotopy_groups f n) :=
  proof idp qed

  definition homotopy_groups_mul3
    : Πn, homotopy_groups f (3 * n) = Ω[n] Y :> Type*
  | 0     := proof rfl qed
  | (k+1) := proof ap (λX, Ω X) (homotopy_groups_mul3 k) qed

  definition homotopy_groups_mul3add1
    : Πn, homotopy_groups f (3 * n + 1) = Ω[n] X :> Type*
  | 0     := proof rfl qed
  | (k+1) := proof ap (λX, Ω X) (homotopy_groups_mul3add1 k) qed

  definition homotopy_groups_mul3add2
    : Πn, homotopy_groups f (3 * n + 2) = Ω[n] (pfiber f) :> Type*
  | 0     := proof rfl qed
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
  | 0     := proof phomotopy.rfl qed
  | 1     := proof phomotopy.rfl qed
  | 2     := proof phomotopy.rfl qed
  | 3     := proof phomotopy.rfl qed
  | 4     := proof phomotopy.rfl qed
  | 5     := proof phomotopy.rfl qed
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

  definition fiber_sequence_pequiv_homotopy_groups :
    Πn, fiber_sequence_carrier f n ≃* homotopy_groups f n
  | 0     := proof pequiv.rfl qed
  | 1     := proof pequiv.rfl qed
  | 2     := proof pequiv.rfl qed
  | (k+3) :=
    begin
      refine fiber_sequence_carrier_pequiv f k ⬝e* _,
      apply loop_space_pequiv,
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

  /- the long exact sequence of homotopy groups -/
  definition LES_of_homotopy_groups [constructor] : left_chain_complex :=
  trunc_left_chain_complex
    (transfer_left_type_chain_complex
      (fiber_sequence f)
      (homotopy_groups_fun f)
      (fiber_sequence_pequiv_homotopy_groups f)
      (fiber_sequence_phomotopy_homotopy_groups f))

  /- the fiber sequence is exact -/
  definition is_exact_LES_of_homotopy_groups : is_exact_l (LES_of_homotopy_groups f) :=
  begin
    intro n,
    apply is_exact_at_l_trunc,
    apply is_exact_at_lt_transfer,
    apply is_exact_fiber_sequence
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
  example : lcc_to_fn (LES_of_homotopy_groups f)  6 = π→*[2] f
    :> (_ →* _) := by reflexivity
  example : lcc_to_fn (LES_of_homotopy_groups f)  7 = π→*[2] (ppoint f)
    :> (_ →* _) := by reflexivity
  example : lcc_to_fn (LES_of_homotopy_groups f)  8 = π→*[2] (boundary_map f)
    :> (_ →* _) := by reflexivity
  example : lcc_to_fn (LES_of_homotopy_groups f)  9 = π→*[2] (ap1 f ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : lcc_to_fn (LES_of_homotopy_groups f) 10 = π→*[2] (ap1 (ppoint f) ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : lcc_to_fn (LES_of_homotopy_groups f) 11 = π→*[2] (ap1 (boundary_map f) ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : lcc_to_fn (LES_of_homotopy_groups f) 12 = π→*[4] f
    :> (_ →* _) := by reflexivity

  /- the carrier of the fiber sequence is what we want for natural numbers of the form
     3n, 3n+1 and 3n+2 -/
  definition LES_of_homotopy_groups_mul3 (n : ℕ) : LES_of_homotopy_groups f (3 * n) = π*[n] Y :> Set* :=
  begin
   apply ptrunctype_eq_of_pType_eq,
   exact ap (ptrunc 0) (homotopy_groups_mul3 f n)
  end

  definition LES_of_homotopy_groups_mul3add1 (n : ℕ) : LES_of_homotopy_groups f (3 * n + 1) = π*[n] X :> Set* :=
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

  definition group_LES_of_homotopy_groups (n : ℕ) : group (LES_of_homotopy_groups f (n + 3)) :=
  group_homotopy_group 0 (homotopy_groups f n)

  definition comm_group_LES_of_homotopy_groups (n : ℕ) : comm_group (LES_of_homotopy_groups f (n + 6)) :=
  comm_group_homotopy_group 0 (homotopy_groups f n)

  -- TODO: the pointed maps are what we want for 3n, 3n+1 and 3n+2
  -- TODO: they are group homomorphisms for n+3
end chain_complex
