-- TODO: in wedge connectivity and is_conn.elim, unbundle P

import homotopy.wedge algebra.homotopy_group homotopy.sphere types.nat

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

  -- example : ((@add.{0} trunc_index has_add_trunc_index n
  --               (trunc_index.of_nat
  --                  (@add.{0} nat nat._trans_of_decidable_linear_ordered_semiring_17 nat.zero
  --                     (@one.{0} nat nat._trans_of_decidable_linear_ordered_semiring_21))))) = (0 : ℕ₋₂) := proof idp qed

  definition iterated_loop_ptrunc_pequiv_con (n : ℕ₋₂) (k : ℕ) (A : Type*)
    (p q : Ω[k + 1](ptrunc (n+k+1) A)) :
    iterated_loop_ptrunc_pequiv n (k+1) A (p ⬝ q) =
    trunc_concat (iterated_loop_ptrunc_pequiv n (k+1) A p)
                 (iterated_loop_ptrunc_pequiv n (k+1) A q) :=
  begin
    exact sorry
    -- induction k with k IH,
    -- { replace (nat.zero + 1) with (nat.succ nat.zero), esimp [iterated_loop_ptrunc_pequiv],
    --   exact sorry},
    -- { exact sorry}
  end

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

  parameters {A : Type*} {n : ℕ} [is_conn n A]

  --porting from Agda
  -- definition Q (x : susp A) : Type :=
  -- trunc (k) (north = x)

  definition up (a : A) : north = north :> susp A := -- up a = loop_susp_unit A a
  merid a ⬝ (merid pt)⁻¹

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

  -- can we get this?
  -- definition freudenthal_suspension  : is_conn_fun (n+n) (loop_susp_unit A) :=
  -- begin
  --   intro p, esimp at *, fapply is_contr.mk,
  --   { note c := encode (tr p), esimp at *, induction c with a, },
  --   { exact sorry}
  -- end

-- {- Used to prove stability in iterated suspensions -}
-- module FreudenthalIso
--   {i} (n : ℕ₋₂) (k : ℕ) (t : k ≠ O) (kle : ⟨ k ⟩ ≤T S (n +2+ S n))
--   (X : Ptd i) (cX : is-connected (S (S n)) (fst X)) where

--   open FreudenthalEquiv n (⟨ k ⟩) kle (fst X) (snd X) cX public

--   hom : Ω^-Group k t (⊙Trunc ⟨ k ⟩ X) Trunc-level
--      →ᴳ Ω^-Group k t (⊙Trunc ⟨ k ⟩ (⊙Ω (⊙Susp X))) Trunc-level
--   hom = record {
--     f = fst F;
--     pres-comp = ap^-conc^ k t (decodeN , decodeN-pt) }
--     where F = ap^ k (decodeN , decodeN-pt)

--   iso : Ω^-Group k t (⊙Trunc ⟨ k ⟩ X) Trunc-level
--      ≃ᴳ Ω^-Group k t (⊙Trunc ⟨ k ⟩ (⊙Ω (⊙Susp X))) Trunc-level
--   iso = (hom , is-equiv-ap^ k (decodeN , decodeN-pt) (snd eq))

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

  definition stability_pequiv (k n : ℕ) (H : k + 2 ≤ 2 * n) : π*[k + 1] (S. (n+1)) ≃* π*[k] (S. n) :=
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
    refine pequiv_of_eq (ap (ptrunc 0) (loop_space_succ_eq_in (S. (n+1)) k)) ⬝e* _,
    rewrite psphere_succ,
    refine !phomotopy_group_pequiv_loop_ptrunc ⬝e* _,
    refine loopn_pequiv_loopn k (freudenthal_pequiv _ H')⁻¹ᵉ* ⬝e* _,
    exact !phomotopy_group_pequiv_loop_ptrunc⁻¹ᵉ*,
  end

--print phomotopy_group_pequiv_loop_ptrunc
--print iterated_loop_ptrunc_pequiv
  -- definition to_fun_stability_pequiv (k n : ℕ) (H : k + 3 ≤ 2 * n) --(p : π*[k + 1] (S. (n+1)))
  --   : stability_pequiv (k+1) n H = _ ∘ _ ∘ cast (ap (ptrunc 0) (loop_space_succ_eq_in (S. (n+1)) (k+1))) :=
  -- sorry

  -- definition stability (k n : ℕ) (H : k + 3 ≤ 2 * n) : πg[k+1 +1] (S. (n+1)) = πg[k+1] (S. n) :=
  -- begin
  --   fapply Group_eq,
  --   { refine equiv_of_pequiv (stability_pequiv _ _ _), rewrite succ_add, exact H},
  --   { intro g h, esimp, }
  -- end

end sphere
