/- pointed sequential colimits -/

-- authors: Floris van Doorn, Egbert Rijke, Stefano Piceghello

import .seq_colim types.fin homotopy.chain_complex types.pointed2
open seq_colim pointed algebra eq is_trunc nat is_equiv equiv sigma sigma.ops chain_complex fiber

namespace seq_colim

  definition pseq_diagram [reducible] (A : ℕ → Type*) : Type := Πn, A n →* A (succ n)
  definition pseq_colim [constructor] {X : ℕ → Type*} (f : pseq_diagram X) : Type* :=
  pointed.MK (seq_colim f) (@sι _ _ 0 pt)

  definition inclusion_pt {X : ℕ → Type*} (f : pseq_diagram X) (n : ℕ)
    : inclusion f (Point (X n)) = Point (pseq_colim f) :=
  begin
    induction n with n p,
      reflexivity,
      exact (ap (sι f) (respect_pt _))⁻¹ᵖ ⬝ (!glue ⬝ p)
  end

  definition pinclusion [constructor] {X : ℕ → Type*} (f : pseq_diagram X) (n : ℕ)
    : X n →* pseq_colim f :=
  pmap.mk (inclusion f) (inclusion_pt f n)

  definition pshift_equiv [constructor] {A : ℕ → Type*} (f : Πn, A n →* A (succ n)) :
    pseq_colim f ≃* pseq_colim (λn, f (n+1)) :=
  begin
    fapply pequiv_of_equiv,
    { apply shift_equiv },
    { exact ap (ι _) (respect_pt (f 0)) }
  end

  definition pshift_equiv_pinclusion {A : ℕ → Type*} (f : Πn, A n →* A (succ n)) (n : ℕ) :
    psquare (pinclusion f n) (pinclusion (λn, f (n+1)) n) (f n) (pshift_equiv f)  :=
  phomotopy.mk homotopy.rfl begin
    refine !idp_con ⬝ _, esimp,
    induction n with n IH,
    { esimp[inclusion_pt], esimp[shift_diag], exact !idp_con⁻¹ },
    { esimp[inclusion_pt], refine !con_inv_cancel_left ⬝ _,
      rewrite ap_con, rewrite ap_con,
      refine _ ⬝ whisker_right _ !con.assoc,
      refine _ ⬝ (con.assoc (_ ⬝ _) _ _)⁻¹,
      xrewrite [-IH],
      esimp[shift_up], rewrite [elim_glue,  ap_inv, -ap_compose'], esimp,
      rewrite [-+con.assoc], apply whisker_right,
      rewrite con.assoc, apply !eq_inv_con_of_con_eq,
      symmetry, exact eq_of_square !natural_square
  }
  end

  definition pseq_colim_functor [constructor] {A A' : ℕ → Type*} {f : pseq_diagram A}
    {f' : pseq_diagram A'} (g : Πn, A n →* A' n)
    (p : Π⦃n⦄, g (n+1) ∘* f n ~ f' n ∘* g n) : pseq_colim f →* pseq_colim f' :=
  pmap.mk (seq_colim_functor g p) (ap (ι _) (respect_pt (g _)))

  definition pseq_colim_pequiv' [constructor] {A A' : ℕ → Type*} {f : pseq_diagram A}
    {f' : pseq_diagram A'} (g : Πn, A n ≃* A' n)
    (p : Π⦃n⦄, g (n+1) ∘* f n ~ f' n ∘* g n) : pseq_colim @f ≃* pseq_colim @f' :=
  pequiv_of_equiv (seq_colim_equiv g p) (ap (ι _) (respect_pt (g _)))

  definition pseq_colim_pequiv [constructor] {A A' : ℕ → Type*} {f : pseq_diagram A}
    {f' : pseq_diagram A'} (g : Πn, A n ≃* A' n)
    (p : Πn, g (n+1) ∘* f n ~* f' n ∘* g n) : pseq_colim @f ≃* pseq_colim @f' :=
  pseq_colim_pequiv' g (λn, @p n)

  -- definition seq_colim_equiv_constant [constructor] {A : ℕ → Type*} {f f' : pseq_diagram A}
  --   (p : Π⦃n⦄ (a : A n), f n a = f' n a) : seq_colim f ≃ seq_colim f' :=
  -- seq_colim_equiv (λn, erfl) p

  definition pseq_colim_equiv_constant' [constructor] {A : ℕ → Type*} {f f' : pseq_diagram A}
    (p : Π⦃n⦄, f n ~ f' n) : pseq_colim @f ≃* pseq_colim @f' :=
  pseq_colim_pequiv' (λn, pequiv.rfl) p

  definition pseq_colim_equiv_constant [constructor] {A : ℕ → Type*} {f f' : pseq_diagram A}
    (p : Πn, f n ~* f' n) : pseq_colim @f ≃* pseq_colim @f' :=
  pseq_colim_pequiv (λn, pequiv.rfl) (λn, !pid_pcompose ⬝* p n ⬝* !pcompose_pid⁻¹*)

  definition pseq_colim_pequiv_pinclusion {A A' : ℕ → Type*} {f : Πn, A n →* A (n+1)}
    {f' : Πn, A' n →* A' (n+1)} (g : Πn, A n ≃* A' n)
    (p : Π⦃n⦄, g (n+1) ∘* f n ~* f' n ∘* g n) (n : ℕ) :
    psquare (pinclusion f n) (pinclusion f' n) (g n) (pseq_colim_pequiv g p) :=
  phomotopy.mk homotopy.rfl begin
    esimp, refine !idp_con ⬝ _,
    induction n with n IH,
    { esimp[inclusion_pt], exact !idp_con⁻¹ },
    { esimp[inclusion_pt], rewrite [+ap_con, -+ap_inv, +con.assoc, +seq_colim_functor_glue],
      xrewrite[-IH],
      rewrite[-+ap_compose', -+con.assoc],
      apply whisker_right, esimp,
      rewrite[(eq_con_inv_of_con_eq (to_homotopy_pt (@p _)))],
      rewrite[ap_con], esimp,
      rewrite[-+con.assoc, ap_con, -ap_compose', +ap_inv],
      rewrite[-+con.assoc],
      refine _ ⬝ whisker_right _ (whisker_right _ (whisker_right _ (whisker_right _ !con.left_inv⁻¹))),
      rewrite[idp_con, +con.assoc], apply whisker_left,
      rewrite[ap_con, -ap_compose', con_inv, +con.assoc], apply whisker_left,
      refine eq_inv_con_of_con_eq _,
      symmetry, exact eq_of_square !natural_square
    }
  end

  definition seq_colim_equiv_constant_pinclusion {A : ℕ → Type*} {f f' : pseq_diagram A}
    (p : Πn, f n ~* f' n) (n : ℕ) :
    pseq_colim_equiv_constant p ∘* pinclusion f n ~* pinclusion f' n  :=
  begin
    transitivity pinclusion f' n ∘* !pid,
    refine phomotopy_of_psquare !pseq_colim_pequiv_pinclusion,
    exact !pcompose_pid
  end

  definition pseq_colim.elim' [constructor] {A : ℕ → Type*} {B : Type*} {f : pseq_diagram A}
    (g : Πn, A n →* B) (p : Πn, g (n+1) ∘* f n ~ g n) : pseq_colim f →* B :=
  begin
    fapply pmap.mk,
    { intro x, induction x with n a n a,
      { exact g n a },
      { exact p n a }},
    { esimp, apply respect_pt }
  end

  definition pseq_colim.elim [constructor] {A : ℕ → Type*} {B : Type*} {f : pseq_diagram A}
    (g : Πn, A n →* B) (p : Πn, g (n+1) ∘* f n ~* g n) : pseq_colim @f →* B :=
  pseq_colim.elim' g p

  definition pseq_colim.elim_pinclusion {A : ℕ → Type*} {B : Type*} {f : pseq_diagram A}
    (g : Πn, A n →* B) (p : Πn, g (n+1) ∘* f n ~* g n) (n : ℕ) :
  pseq_colim.elim g p ∘* pinclusion f n ~* g n :=
  begin
    refine phomotopy.mk phomotopy.rfl _,
    refine !idp_con ⬝ _,
    esimp,
    induction n with n IH,
    { esimp, esimp[inclusion_pt], exact !idp_con⁻¹ },
    { esimp, esimp[inclusion_pt],
      rewrite ap_con, rewrite ap_con,
      rewrite elim_glue,
      rewrite [-ap_inv],
      rewrite [-ap_compose'], esimp,
      rewrite [(eq_con_inv_of_con_eq (!to_homotopy_pt))],
      rewrite [IH],
      rewrite [con_inv],
      rewrite [-+con.assoc],
      refine _ ⬝ whisker_right _ !con.assoc⁻¹,
      rewrite [con.left_inv], esimp,
      refine _ ⬝ !con.assoc⁻¹,
      rewrite [con.left_inv], esimp,
      rewrite [ap_inv],
      rewrite [-con.assoc],
      refine !idp_con⁻¹ ⬝ whisker_right _ !con.left_inv⁻¹,
    }
  end

  definition prep0 [constructor] {A : ℕ → Type*} (f : pseq_diagram A) (k : ℕ) : A 0 →* A k :=
  pmap.mk (rep0 (λn x, f n x) k)
          begin induction k with k p, reflexivity, exact ap (@f k) p ⬝ !respect_pt end

  definition respect_pt_prep0_succ {A : ℕ → Type*} (f : pseq_diagram A) (k : ℕ)
    : respect_pt (prep0 f (succ k)) = ap (@f k) (respect_pt (prep0 f k)) ⬝ respect_pt (f k) :=
  by reflexivity

  theorem prep0_succ_lemma {A : ℕ → Type*} (f : pseq_diagram A) (n : ℕ)
    (p : rep0 (λn x, f n x) n pt = rep0 (λn x, f n x) n pt)
    (q : prep0 f n (Point (A 0)) = Point (A n))

    : loop_equiv_eq_closed (ap (@f n) q ⬝ respect_pt (@f n))
    (ap (@f n) p) = Ω→(@f n) (loop_equiv_eq_closed q p) :=
  by rewrite [▸*, con_inv, ↑ap1_gen, +ap_con, ap_inv, +con.assoc]

  variables {A : ℕ → Type} (f : seq_diagram A)
  definition succ_add_tr_rep {n : ℕ} (k : ℕ) (x : A n)
    : transport A (succ_add n k) (rep f k (f x)) = rep f (succ k) x :=
  begin
    induction k with k p,
      reflexivity,
      exact tr_ap A succ (succ_add n k) _ ⬝ (fn_tr_eq_tr_fn (succ_add n k) f _)⁻¹ ⬝ ap (@f _) p,
  end

  definition succ_add_tr_rep_succ {n : ℕ} (k : ℕ) (x : A n)
    : succ_add_tr_rep f (succ k) x = tr_ap A succ (succ_add n k) _ ⬝
        (fn_tr_eq_tr_fn (succ_add n k) f _)⁻¹ ⬝ ap (@f _) (succ_add_tr_rep f k x) :=
  by reflexivity

  definition code_glue_equiv [constructor] {n : ℕ} (k : ℕ) (x y : A n)
    : rep f k (f x) = rep f k (f y) ≃ rep f (succ k) x = rep f (succ k) y :=
  begin
    refine eq_equiv_fn_eq_of_equiv (equiv_ap A (succ_add n k)) _ _ ⬝e _,
    apply eq_equiv_eq_closed,
      exact succ_add_tr_rep f k x,
      exact succ_add_tr_rep f k y
  end

  theorem code_glue_equiv_ap {n : ℕ} {k : ℕ} {x y : A n} (p : rep f k (f x) = rep f k (f y))
    : code_glue_equiv f (succ k) x y (ap (@f _) p) = ap (@f _) (code_glue_equiv f k x y p) :=
  begin
    rewrite [▸*, +ap_con, ap_inv, +succ_add_tr_rep_succ, con_inv, inv_con_inv_right, +con.assoc],
    apply whisker_left,
    rewrite [- +con.assoc], apply whisker_right, rewrite [- +ap_compose'],
    note s := (eq_top_of_square (natural_square_tr
      (λx, fn_tr_eq_tr_fn (succ_add n k) f x ⬝ (tr_ap A succ (succ_add n k) (f x))⁻¹) p))⁻¹ᵖ,
    rewrite [inv_con_inv_right at s, -con.assoc at s], exact s
  end

  definition pseq_colim_loop {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) :
    Ω (pseq_colim f) ≃* pseq_colim (λn, Ω→(f n)) :=
  begin
    fapply pequiv_of_equiv,
    { refine !seq_colim_eq_equiv0 ⬝e _,
      fapply seq_colim_equiv,
      { intro n, exact loop_equiv_eq_closed (respect_pt (prep0 f n)) },
      { intro n p, apply prep0_succ_lemma }},
    { reflexivity }
  end

  definition pseq_colim_loop_pinclusion {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) (n : ℕ) :
    pseq_colim_loop f ∘* Ω→ (pinclusion f n) ~* pinclusion (λn, Ω→(f n)) n :=
  sorry

  definition pseq_diagram_pfiber {A A' : ℕ → Type*} {f : pseq_diagram A} {f' : pseq_diagram A'}
    (g : Πn, A n →* A' n) (p : Πn, g (succ n) ∘* f n ~* f' n ∘* g n) :
    pseq_diagram (λk, pfiber (g k)) :=
  λk, pfiber_functor (f k) (f' k) (p k)

/- Two issues when going to the pointed version:
  - seq_diagram_fiber τ p a for a : A n at position k lives over (A (n + k)), so for a : A 0 you get A (0 + k), but we need A k
  - in seq_diagram_fiber the fibers are taken in rep f ..., but in the pointed version over the basepoint of A n
-/
definition pfiber_pseq_colim_functor {A A' : ℕ → Type*} {f : pseq_diagram A}
  {f' : pseq_diagram A'} (τ : Πn, A n →* A' n)
  (p : Π⦃n⦄, τ (n+1) ∘* f n ~* f' n ∘* τ n) : pfiber (pseq_colim_functor τ p) ≃*
    pseq_colim (pseq_diagram_pfiber τ p) :=
begin
  fapply pequiv_of_equiv,
  { refine fiber_seq_colim_functor0 τ p pt ⬝e _, fapply seq_colim_equiv, intro n, esimp,
    repeat exact sorry }, exact sorry
end


  -- open succ_str
  -- definition pseq_colim_succ_str_change_index' {N : succ_str} {B : N → Type*} (n : N) (m : ℕ)
  --   (h : Πn, B n →* B (S n)) :
  --   pseq_colim (λk, h (n +' (m + succ k))) ≃* pseq_colim (λk, h (S n +' (m + k))) :=
  -- sorry

  -- definition pseq_colim_succ_str_change_index {N : succ_str} {B : ℕ → N → Type*} (n : N)
  --   (h : Π(k : ℕ) n, B k n →* B k (S n)) :
  --   pseq_colim (λk, h k (n +' succ k)) ≃* pseq_colim (λk, h k (S n +' k)) :=
  -- sorry

  -- definition pseq_colim_index_eq_general {N : succ_str} (B : N → Type*) (f g : ℕ → N) (p : f ~ g)
  --   (pf : Πn, S (f n) = f (n+1)) (pg : Πn, S (g n) = g (n+1)) (h : Πn, B n →* B (S n)) :
  --   @pseq_colim (λn, B (f n)) (λn, ptransport B (pf n) ∘* h (f n)) ≃*
  --   @pseq_colim (λn, B (g n)) (λn, ptransport B (pg n) ∘* h (g n)) :=
  -- sorry


end seq_colim
