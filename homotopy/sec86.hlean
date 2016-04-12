/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import homotopy.wedge homotopy.homotopy_group homotopy.circle .LES_applications

open eq is_conn is_trunc pointed susp nat pi equiv is_equiv trunc fiber trunc_index

  -- definition iterated_loop_ptrunc_pequiv_con' (n : ℕ₋₂) (k : ℕ) (A : Type*)
  --   (p q : Ω[k](ptrunc (n+k) (Ω A))) :
  --   iterated_loop_ptrunc_pequiv n k (Ω A) (loop_mul trunc_concat p q) =
  --   trunc_functor2 (loop_mul concat) (iterated_loop_ptrunc_pequiv n k (Ω A) p)
  --                                    (iterated_loop_ptrunc_pequiv n k (Ω A) q) :=
  -- begin
  --   revert n p q, induction k with k IH: intro n p q,
  --   { reflexivity},
  --   { exact sorry}
  -- end

  theorem elim_type_merid_inv {A : Type} (PN : Type) (PS : Type) (Pm : A → PN ≃ PS)
    (a : A) : transport (susp.elim_type PN PS Pm) (merid a)⁻¹ = to_inv (Pm a) :=
  by rewrite [tr_eq_cast_ap_fn,↑susp.elim_type,ap_inv,elim_merid]; apply cast_ua_inv_fn

  definition is_conn_trunc (A : Type) (n k : ℕ₋₂) [H : is_conn n A]
    : is_conn n (trunc k A) :=
  begin
    apply is_trunc_equiv_closed, apply trunc_trunc_equiv_trunc_trunc
  end

  section open sphere sphere.ops
  definition psphere_succ [unfold_full] (n : ℕ) : S. (n + 1) = psusp (S. n) := idp
  end

namespace freudenthal section

  /- The Freudenthal Suspension Theorem -/
  parameters {A : Type*} {n : ℕ} [is_conn n A]

  /-
    This proof is ported from Agda
    This is the 95% version of the Freudenthal Suspension Theorem, which means that we don't
    prove that loop_susp_unit : A →* Ω(psusp A) is 2n-connected (if A is n-connected),
    but instead we only prove that it induces an equivalence on the first 2n homotopy groups.
  -/

  definition up (a : A) : north = north :> susp A :=
  loop_susp_unit A a

  definition code_merid : A → ptrunc (n + n) A → ptrunc (n + n) A :=
  begin
    have is_conn n (ptrunc (n + n) A), from !is_conn_trunc,
    refine wedge_extension.ext n n (λ x y, ttrunc (n + n) A) _ _ _,
    { exact tr},
    { exact id},
    { reflexivity}
  end

  definition code_merid_β_left (a : A) : code_merid a pt = tr a :=
  by apply wedge_extension.β_left

  definition code_merid_β_right (b : ptrunc (n + n) A) : code_merid pt b = b :=
  by apply wedge_extension.β_right

  definition code_merid_coh : code_merid_β_left pt = code_merid_β_right pt :=
  begin
    symmetry, apply eq_of_inv_con_eq_idp, apply wedge_extension.coh
  end

  definition is_equiv_code_merid (a : A) : is_equiv (code_merid a) :=
  begin
    have Πa, is_trunc n.-2.+1 (is_equiv (code_merid a)),
      from λa, is_trunc_of_le _ !minus_one_le_succ,
    refine is_conn.elim (n.-1) _ _ a,
    { esimp, exact homotopy_closed id (homotopy.symm (code_merid_β_right))}
  end

  definition code_merid_equiv [constructor] (a : A) : trunc (n + n) A ≃ trunc (n + n) A :=
  equiv.mk _ (is_equiv_code_merid a)

  definition code_merid_inv_pt (x : trunc (n + n) A) : (code_merid_equiv pt)⁻¹ x = x :=
  begin
    refine ap010 @(is_equiv.inv _) _ x ⬝ _,
    { exact homotopy_closed id (homotopy.symm code_merid_β_right)},
    { apply is_conn.elim_β},
    { reflexivity}
  end

  definition code [unfold 4] : susp A → Type :=
  susp.elim_type (trunc (n + n) A) (trunc (n + n) A) code_merid_equiv

  definition is_trunc_code (x : susp A) : is_trunc (n + n) (code x) :=
  begin
    induction x with a: esimp,
    { exact _},
    { exact _},
    { apply is_prop.elimo}
  end
  local attribute is_trunc_code [instance]

  definition decode_north [unfold 4] : code north → trunc (n + n) (north = north :> susp A) :=
  trunc_functor (n + n) up

  definition decode_north_pt : decode_north (tr pt) = tr idp :=
  ap tr !con.right_inv

  definition decode_south [unfold 4] : code south → trunc (n + n) (north = south :> susp A) :=
  trunc_functor (n + n) merid

  definition encode' {x : susp A} (p : north = x) : code x :=
  transport code p (tr pt)

  definition encode [unfold 5] {x : susp A} (p : trunc (n + n) (north = x)) : code x :=
  begin
    induction p with p,
    exact transport code p (tr pt)
  end

  theorem encode_decode_north (c : code north) : encode (decode_north c) = c :=
  begin
    have H : Πc, is_trunc (n + n) (encode (decode_north c) = c), from _,
    esimp at *,
    induction c with a,
    rewrite [↑[encode, decode_north, up, code], con_tr, elim_type_merid, ▸*,
             code_merid_β_left, elim_type_merid_inv, ▸*, code_merid_inv_pt]
  end

  definition decode_coh_f (a : A) : tr (up pt) =[merid a] decode_south (code_merid a (tr pt)) :=
  begin
    refine _ ⬝op ap decode_south (code_merid_β_left a)⁻¹,
    apply trunc_pathover,
    apply eq_pathover_constant_left_id_right,
    apply square_of_eq,
    exact whisker_right !con.right_inv (merid a)
  end

  definition decode_coh_g (a' : A) : tr (up a') =[merid pt] decode_south (code_merid pt (tr a')) :=
  begin
    refine _ ⬝op ap decode_south (code_merid_β_right (tr a'))⁻¹,
    apply trunc_pathover,
    apply eq_pathover_constant_left_id_right,
    apply square_of_eq, refine !inv_con_cancel_right ⬝ !idp_con⁻¹
  end

  definition decode_coh_lem {A : Type} {a a' : A} (p : a = a')
    : whisker_right (con.right_inv p) p = inv_con_cancel_right p p ⬝ (idp_con p)⁻¹ :=
  by induction p; reflexivity

  theorem decode_coh (a : A) : decode_north =[merid a] decode_south :=
  begin
    apply arrow_pathover_left, intro c, esimp at *,
    induction c with a',
    rewrite [↑code, elim_type_merid, ▸*],
    refine wedge_extension.ext n n _ _ _ _ a a',
    { exact decode_coh_f},
    { exact decode_coh_g},
    { clear a a', unfold [decode_coh_f, decode_coh_g], refine ap011 concato_eq _ _,
      { refine ap (λp, trunc_pathover (eq_pathover_constant_left_id_right (square_of_eq p))) _,
        apply decode_coh_lem},
      { apply ap (λp, ap decode_south p⁻¹), apply code_merid_coh}}
  end

  definition decode [unfold 4] {x : susp A} (c : code x) : trunc (n + n) (north = x) :=
  begin
    induction x with a,
    { exact decode_north c},
    { exact decode_south c},
    { exact decode_coh a}
  end

  theorem decode_encode {x : susp A} (p : trunc (n + n) (north = x)) : decode (encode p) = p :=
  begin
    induction p with p, induction p, esimp, apply decode_north_pt
  end

  parameters (A n)
  definition equiv' : trunc (n + n) A ≃ trunc (n + n) (Ω (psusp A)) :=
  equiv.MK decode_north encode decode_encode encode_decode_north

  definition pequiv' : ptrunc (n + n) A ≃* ptrunc (n + n) (Ω (psusp A)) :=
  pequiv_of_equiv equiv' decode_north_pt

  -- We don't prove this:
  -- theorem freudenthal_suspension : is_conn_fun (n+n) (loop_susp_unit A) :=

end end freudenthal

open algebra
definition freudenthal_pequiv (A : Type*) {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : ptrunc k A ≃* ptrunc k (Ω (psusp A)) :=
have H' : k ≤[ℕ₋₂] n + n,
  by rewrite [mul.comm at H, -algebra.zero_add n at {1}]; exact of_nat_le_of_nat H,
ptrunc_pequiv_ptrunc_of_le H' (freudenthal.pequiv' A n)

definition freudenthal_equiv {A : Type*} {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : trunc k A ≃ trunc k (Ω (psusp A)) :=
freudenthal_pequiv A H

namespace sphere
  open ops algebra pointed function

  -- replace with definition in algebra.homotopy_group
  definition phomotopy_group_succ_in2 (A : Type*) (n : ℕ) : π*[n + 1] A = π*[n] Ω A :> Type* :=
  ap (ptrunc 0) (loop_space_succ_eq_in A n)

  definition stability_pequiv_helper (k n : ℕ) (H : k + 2 ≤ 2 * n)
    : ptrunc k (Ω(psusp (S. n))) ≃* ptrunc k (S. n) :=
  begin
    have H' : k ≤ 2 * pred n,
    begin
      rewrite [mul_pred_right], change pred (pred (k + 2)) ≤ pred (pred (2 * n)),
      apply pred_le_pred, apply pred_le_pred, exact H
    end,
    have is_conn (of_nat (pred n)) (S. n),
    begin
      cases n with n,
      { exfalso, exact not_succ_le_zero _ H},
      { esimp, apply is_conn_psphere}
    end,
    symmetry, exact freudenthal_pequiv (S. n) H'
  end

  definition stability_pequiv (k n : ℕ) (H : k + 2 ≤ 2 * n) : π*[k + 1] (S. (n+1)) ≃* π*[k] (S. n) :=
  begin
    refine pequiv_of_eq (phomotopy_group_succ_in2 (S. (n+1)) k) ⬝e* _,
    rewrite psphere_succ,
    refine !phomotopy_group_pequiv_loop_ptrunc ⬝e* _,
    refine loopn_pequiv_loopn k (stability_pequiv_helper k n H) ⬝e* _,
    exact !phomotopy_group_pequiv_loop_ptrunc⁻¹ᵉ*,
  end

  -- change some "+1"'s intro succ's to avoid this definition (or vice versa)
  definition group_homotopy_group2 [instance] (k : ℕ) (A : Type*) :
    group (carrier (ptrunctype.to_pType (π*[k + 1] A))) :=
  group_homotopy_group k A

  definition loop_pequiv_loop_con {A B : Type*} (f : A ≃* B) (p q : Ω A)
    : loop_pequiv_loop f (p ⬝ q) = loop_pequiv_loop f p ⬝ loop_pequiv_loop f q :=
  loopn_pequiv_loopn_con 0 f p q

  definition iterated_loop_ptrunc_pequiv_con {n : ℕ₋₂} {k : ℕ} {A : Type*}
    (p q : Ω[succ k] (ptrunc (n+succ k) A)) :
    iterated_loop_ptrunc_pequiv n (succ k) A (p ⬝ q) =
    trunc_concat (iterated_loop_ptrunc_pequiv n (succ k) A p)
                 (iterated_loop_ptrunc_pequiv n (succ k) A q)  :=
  begin
    refine _ ⬝ loop_ptrunc_pequiv_con _ _,
    exact ap !loop_ptrunc_pequiv !loop_pequiv_loop_con
  end

  theorem inv_respect_binary_operation {A B : Type} (f : A ≃ B) (mA : A → A → A) (mB : B → B → B)
    (p : Πa₁ a₂, f (mA a₁ a₂) = mB (f a₁) (f a₂)) (b₁ b₂ : B) :
    f⁻¹ (mB b₁ b₂) = mA (f⁻¹ b₁) (f⁻¹ b₂) :=
  begin
    refine is_equiv_rect' f⁻¹ _ _ b₁, refine is_equiv_rect' f⁻¹ _ _ b₂,
    intros a₂ a₁, apply inv_eq_of_eq, symmetry, exact p a₁ a₂
  end

  definition iterated_loop_ptrunc_pequiv_inv_con {n : ℕ₋₂} {k : ℕ} {A : Type*}
    (p q : ptrunc n (Ω[succ k] A)) :
    (iterated_loop_ptrunc_pequiv n (succ k) A)⁻¹ᵉ* (trunc_concat p q) =
    (iterated_loop_ptrunc_pequiv n (succ k) A)⁻¹ᵉ* p ⬝
    (iterated_loop_ptrunc_pequiv n (succ k) A)⁻¹ᵉ* q :=
  inv_respect_binary_operation (iterated_loop_ptrunc_pequiv n (succ k) A) concat trunc_concat
    (@iterated_loop_ptrunc_pequiv_con n k A) p q

  definition phomotopy_group_pequiv_loop_ptrunc_con {k : ℕ} {A : Type*} (p q : πg[k +1] A) :
    phomotopy_group_pequiv_loop_ptrunc (succ k) A (p * q) =
    phomotopy_group_pequiv_loop_ptrunc (succ k) A p ⬝
    phomotopy_group_pequiv_loop_ptrunc (succ k) A q :=
  begin
    refine _ ⬝ !loopn_pequiv_loopn_con,
    exact ap (loopn_pequiv_loopn _ _) !iterated_loop_ptrunc_pequiv_inv_con
  end

  definition phomotopy_group_pequiv_loop_ptrunc_inv_con {k : ℕ} {A : Type*}
    (p q : Ω[succ k] (ptrunc (succ k) A)) :
    (phomotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* (p ⬝ q) =
    (phomotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* p *
    (phomotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* q :=
  inv_respect_binary_operation (phomotopy_group_pequiv_loop_ptrunc (succ k) A) mul concat
    (@phomotopy_group_pequiv_loop_ptrunc_con k A) p q

  definition tcast [constructor] {n : ℕ₋₂} {A B : n-Type*} (p : A = B) : A →* B :=
  pcast (ap ptrunctype.to_pType p)

  definition tr_mul_tr {n : ℕ} {A : Type*} (p q : Ω[succ n] A)
    : tr p *[π[n + 1] A] tr q = tr (p ⬝ q) :=
  idp

  -- use this in proof for ghomotopy_group_succ_in
  definition phomotopy_group_succ_in2_con {A : Type*} {n : ℕ} (g h : πg[succ n +1] A) :
    pcast (phomotopy_group_succ_in2 A (succ n)) (g * h) =
    pcast (phomotopy_group_succ_in2 A (succ n)) g * pcast (phomotopy_group_succ_in2 A (succ n)) h :=
  begin
    induction g with p, induction h with q, esimp,
    rewrite [-+ tr_eq_cast_ap, ↑phomotopy_group_succ_in2, -+ tr_compose],
    refine ap (transport _ _) !tr_mul_tr ⬝ _,
    rewrite [+ trunc_transport],
    apply ap tr, apply loop_space_succ_eq_in_concat,
  end

  definition stability_eq (k n : ℕ) (H : k + 3 ≤ 2 * n) : πg[k+1 +1] (S. (n+1)) = πg[k+1] (S. n) :=
  begin
    fapply Group_eq,
    { exact equiv_of_pequiv (stability_pequiv (succ k) n H)},
    { intro g h,
      refine _ ⬝ !phomotopy_group_pequiv_loop_ptrunc_inv_con,
      apply ap !phomotopy_group_pequiv_loop_ptrunc⁻¹ᵉ*,
      refine ap (loopn_pequiv_loopn _ _) _ ⬝ !loopn_pequiv_loopn_con,
      refine ap !phomotopy_group_pequiv_loop_ptrunc _ ⬝ !phomotopy_group_pequiv_loop_ptrunc_con,
      apply phomotopy_group_succ_in2_con
      }
  end

  theorem mul_two {A : Type} [semiring A] (a : A) : a * 2 = a + a :=
  by rewrite [-one_add_one_eq_two, left_distrib, +mul_one]

  theorem two_mul {A : Type} [semiring A] (a : A) : 2 * a = a + a :=
  by rewrite [-one_add_one_eq_two, right_distrib, +one_mul]

  definition two_le_succ_succ (n : ℕ) : 2 ≤ succ (succ n) :=
  nat.succ_le_succ (nat.succ_le_succ !zero_le)

  open int circle hopf
  definition πnSn (n : ℕ) : πg[n+1] (S. (succ n)) = gℤ :=
  begin
    cases n with n IH,
    { exact fundamental_group_of_circle},
    { induction n with n IH,
      { exact π2S2},
      { refine _ ⬝ IH, apply stability_eq,
        calc
          succ n + 3 = succ (succ n) + 2 : !succ_add⁻¹
                 ... ≤ succ (succ n) + (succ (succ n)) : add_le_add_left !two_le_succ_succ
                 ... = 2 * (succ (succ n)) : !two_mul⁻¹ }}
  end


  attribute group_integers [constructor]
  theorem not_is_trunc_sphere (n : ℕ) : ¬is_trunc n (S. (succ n)) :=
  begin
    intro H,
    note H2 := trivial_homotopy_group_of_is_trunc (S. (succ n)) n n !le.refl,
    rewrite [πnSn at H2, ▸* at H2],
    have H3 : (0 : ℤ) ≠ (1 : ℤ), from dec_star,
    apply H3,
    apply is_prop.elim,
  end

  definition transport11 {A B : Type} (P : A → B → Type) {a a' : A} {b b' : B}
    (p : a = a') (q : b = b') (z : P a b) : P a' b' :=
  transport (P a') q (p ▸ z)

  section
    open sphere_index

    definition add_plus_one_minus_one (n : ℕ₋₁) : n +1+ -1 = n := idp
    definition add_plus_one_succ (n m : ℕ₋₁) : n +1+ (m.+1) = (n +1+ m).+1 := idp
    definition minus_one_add_plus_one (n : ℕ₋₁) : -1 +1+ n = n :=
    begin induction n with n IH, reflexivity, exact ap succ IH end
    definition succ_add_plus_one (n m : ℕ₋₁) : (n.+1) +1+ m = (n +1+ m).+1 :=
    begin induction m with m IH, reflexivity, exact ap succ IH end

    definition nat_of_sphere_index : ℕ₋₁ → ℕ :=
    sphere_index.rec 0 (λx, succ)

    definition trunc_index_of_nat_of_sphere_index (n : ℕ₋₁)
      : trunc_index.of_nat (nat_of_sphere_index n) = (of_sphere_index n).+1 :=
    begin
      induction n with n IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition sphere_index_of_nat_of_sphere_index (n : ℕ₋₁)
      : sphere_index.of_nat (nat_of_sphere_index n) = n.+1 :=
    begin
      induction n with n IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition of_sphere_index_succ (n : ℕ₋₁)
      : of_sphere_index (n.+1) = (of_sphere_index n).+1 :=
    begin
      induction n with n IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition sphere_index.of_nat_succ (n : ℕ)
      : sphere_index.of_nat (succ n) = (sphere_index.of_nat n).+1 :=
    begin
      induction n with n IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition nat_of_sphere_index_succ (n : ℕ₋₁)
      : nat_of_sphere_index (n.+1) = succ (nat_of_sphere_index n) :=
    begin
      induction n with n IH,
      { reflexivity},
      { exact ap succ IH}
    end

    definition not_is_trunc_sphere' (n : ℕ₋₁) : ¬is_trunc n (S (n.+1)) :=
    begin
      cases n with n,
      { esimp [sphere.ops.S, sphere], intro H,
        have H2 : is_prop bool, from @(is_trunc_equiv_closed -1 sphere_equiv_bool) H,
        have H3 : bool.tt ≠ bool.ff, from dec_star, apply H3, apply is_prop.elim},
      { intro H, apply not_is_trunc_sphere (nat_of_sphere_index n),
        rewrite [▸*, trunc_index_of_nat_of_sphere_index, -nat_of_sphere_index_succ,
                 sphere_index_of_nat_of_sphere_index],
        exact H}
    end
  end

  definition π3S2 : πg[2+1] (S. 2) = gℤ :=
  (πnS3_eq_πnS2 0)⁻¹ ⬝ πnSn 2

end sphere
