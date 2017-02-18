/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Given a sequence of LES's, we want to splice them together.
... -> G_{1,k+1} -> G_{1,k} -> ... -> G_{1,1} -> G_{1,0}
... -> G_{2,k+1} -> G_{2,k} -> ... -> G_{2,1} -> G_{2,0}
...
... -> G_{n,k+1} -> G_{n,k} -> ... -> G_{n,1} -> G_{n,0}
...

If we have equivalences:
G_{n,m) = G_{n+1,m+k}
G_{n,m+1) = G_{n+1,m+k+1}
such that the evident squares commute, we can obtain a single sequence

 ... -> G_{n,m} -> G_{n+1,m+k-1} -> ... -> G_{n+1,m} -> G_{n+2,m+k-1} -> ...

However, in this formalization, we will only do this for k = 3, because we get more definitional
equalities in this specific case than in the general case. The reason is that we need to check
whether a term `x : fin (succ k)` represents `k`. If we do this in general using
if x = k then ... else ...
we don't get definitionally that x = k and the successor of x is 0, which means that when defining
maps G_{n,m} -> G_{n+1,m+k-1} we need to transport along those paths, which is annoying.

So far, the splicing seems to be only needed for k = 3, so it seems to be sufficient.

-/

import homotopy.chain_complex

open prod prod.ops succ_str fin pointed nat algebra eq is_trunc equiv is_equiv

/- fin -/

  -- definition cyclic_pred {n : ℕ} (x : fin n) : fin n :=
  -- begin
  --   cases n with n,
  --   { exfalso, apply not_lt_zero _ (is_lt x)},
  --   { cases x with m H, cases m with m,
  --     { exact fin.mk n !self_lt_succ},
  --     { apply fin.mk m, exact lt.trans !self_lt_succ H}}
  -- end

  -- definition stratified_succ2 {N : succ_str} {n : ℕ} (x : stratified_type N n)
  --   : stratified_type N n :=
  -- (nat.cases_on (pr2 x) (S (pr1 x)) (λa, pr1 x), cyclic_pred (pr2 x))

  -- definition stratified2 [reducible] [constructor] (N : succ_str) (n : ℕ) : succ_str :=
  -- succ_str.mk (stratified_type N n) stratified_succ2


namespace chain_complex

definition stratified_succ_max {N : succ_str} {n : ℕ} (x : stratified N n) (p : val (pr2 x) = n)
  : S x = (S (pr1 x), 0) :=
begin
  unfold [stratified, succ_str.S, stratified_succ],
  apply prod_eq,
  { exact if_pos p},
  { exact dif_pos p}
end

  definition splice_type [unfold 5] {N M : succ_str} (G : N → chain_complex M) (m : M)
    (x : stratified N 2) : Set* :=
  G x.1 (m +' val x.2)

  definition splice_map {N M : succ_str} (G : N → chain_complex M) (m : M)
    (e0 : Πn, G (S n) m ≃* G n (m +' 3)) :
    Π(x : stratified N 2), splice_type G m (S x) →* splice_type G m x
  | (n, fin.mk 0 H) := proof cc_to_fn (G n) m qed
  | (n, fin.mk 1 H) := proof cc_to_fn (G n) (S m) qed
  | (n, fin.mk 2 H) := proof cc_to_fn (G n) (S (S m)) ∘* e0 n qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition is_chain_complex_splice_map {N M : succ_str} (G : N → chain_complex M) (m : M)
    (e0 : Πn, G (S n) m ≃* G n (m +' 3)) (e1 : Πn, G (S n) (S m) ≃* G n (S (m +' 3)))
    (p : Πn, e0 n ∘* cc_to_fn (G (S n)) m ~ cc_to_fn (G n) (m +' 3) ∘* e1 n) :
    Π(x : stratified N 2) (y : splice_type G m (S (S x))),
      splice_map G m e0 x (splice_map G m e0 (S x) y) = pt
  | (n, fin.mk 0 H) y := proof cc_is_chain_complex (G n) m y qed
  | (n, fin.mk 1 H) y := proof cc_is_chain_complex (G n) (S m) (e0 n y) qed
  | (n, fin.mk 2 H) y := proof ap (cc_to_fn (G n) (S (S m))) (p n y) ⬝
                               cc_is_chain_complex (G n) (S (S m)) (e1 n y) qed
  | (n, fin.mk (k+3) H) y := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition splice [constructor] {N M : succ_str} (G : N → chain_complex M) (m : M)
    (e0 : Πn, G (S n) m ≃* G n (m +' 3)) (e1 : Πn, G (S n) (S m) ≃* G n (S (m +' 3)))
    (p : Πn, e0 n ∘* cc_to_fn (G (S n)) m ~ cc_to_fn (G n) (m +' 3) ∘* e1 n) :
    chain_complex (stratified N 2) :=
  chain_complex.mk (splice_type G m) (splice_map G m e0) (is_chain_complex_splice_map G m e0 e1 p)

  definition is_exact_splice {N M : succ_str} (G : N → chain_complex M) (m : M)
    (e0 : Πn, G (S n) m ≃* G n (m +' 3)) (e1 : Πn, G (S n) (S m) ≃* G n (S (m +' 3)))
    (p : Πn, e0 n ∘* cc_to_fn (G (S n)) m ~ cc_to_fn (G n) (m +' 3) ∘* e1 n)
    (H2 : Πn, is_exact (G n)) : Π(x : stratified N 2), is_exact_at (splice G m e0 e1 p) x
  | (n, fin.mk 0 H) := proof H2 n m qed
  | (n, fin.mk 1 H) := begin intro y q, induction H2 n (S m) proof y qed proof q qed with x r,
    apply image.mk ((e0 n)⁻¹ᵉ x),
    exact ap (pmap.to_fun (cc_to_fn (G n) (S (S m)))) (to_right_inv (e0 n) x) ⬝ r end
  | (n, fin.mk 2 H) :=
  begin intro y q, induction H2 n (S (S m)) proof e0 n y qed proof q qed with x r,
    apply image.mk ((e1 n)⁻¹ᵉ x),
    refine _ ⬝ to_left_inv (e0 n) y, refine _ ⬝ ap (e0 n)⁻¹ᵉ r, apply @eq_inv_of_eq _ _ (e0 n),
    refine p n ((e1 n)⁻¹ᵉ x) ⬝ _, apply ap (cc_to_fn (G n) (m +' 3)), exact to_right_inv (e1 n) x
  end
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end


end chain_complex
