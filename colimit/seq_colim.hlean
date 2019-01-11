/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/
import hit.colimit .sequence cubical.squareover types.arrow types.equiv
       cubical.pathover2

open eq nat sigma sigma.ops quotient equiv pi is_trunc is_equiv fiber function trunc

namespace seq_colim

-- note: this clashes with the abbreviation defined in namespace "colimit"
abbreviation ι  [constructor] := @inclusion
abbreviation ι' [constructor] [parsing_only] {A} (f n) := @inclusion A f n

universe variable v
variables {A A' A'' : ℕ → Type} (f : seq_diagram A) (f' : seq_diagram A') (f'' : seq_diagram A'')
          (τ τ₂ : Π⦃n⦄, A n → A' n) (p : Π⦃n⦄ (a : A n), τ (f a) = f' (τ a))
          (p₂ : Π⦃n⦄ (a : A n), τ₂ (f a) = f' (τ₂ a))
          (τ' : Π⦃n⦄, A' n → A'' n) (p' : Π⦃n⦄ (a' : A' n), τ' (f' a') = f'' (τ' a'))
          {P : Π⦃n⦄, A n → Type.{v}} (g : seq_diagram_over f P) {n : ℕ} {a : A n}

definition lrep_glue {n m : ℕ} (H : n ≤ m) (a : A n) : ι f (lrep f H a) = ι f a :=
begin
  induction H with m H p,
  { reflexivity },
  { exact glue f (lrep f H a) ⬝ p }
end

definition colim_back [unfold 4] [H : is_equiseq f] : seq_colim f → A 0 :=
begin
  intro x,
  induction x with k a k a,
  { exact lrep_back f (zero_le k) a},
  rexact ap (lrep_back f (zero_le k)) (left_inv (@f k) a),
end

section
variable {f}
local attribute is_equiv_lrep [instance] --[priority 500]
definition is_equiv_inclusion0 (H : is_equiseq f) : is_equiv (ι' f 0) :=
begin
  fapply adjointify,
  { exact colim_back f},
  { intro x, induction x with k a k a,
    { refine (lrep_glue f (zero_le k) (lrep_back f (zero_le k) a))⁻¹ ⬝ _,
      exact ap (ι f) (right_inv (lrep f (zero_le k)) a)},
    apply eq_pathover_id_right,
    refine (ap_compose (ι f) (colim_back f) _) ⬝ph _,
    refine ap02 _ _ ⬝ph _, rotate 1,
    { rexact elim_glue f _ _ a },
    refine _ ⬝pv ((natural_square (lrep_glue f (zero_le k))
                                  (ap (lrep_back f (zero_le k)) (left_inv (@f k) a)))⁻¹ʰ ⬝h _),
    { exact (glue f _)⁻¹ ⬝ ap (ι f) (right_inv (lrep f (zero_le (succ k))) (f a)) },
    { rewrite [-con.assoc, -con_inv] },
    refine !ap_compose⁻¹ ⬝ ap_compose (ι f) _ _ ⬝ph _,
    refine dconcat (aps (ι' f k) (natural_square (right_inv (lrep f (zero_le k)))
                                                 (left_inv (@f _) a))) _,
    apply move_top_of_left, apply move_left_of_bot,
    refine ap02 _ (whisker_left _ (adj (@f _) a)) ⬝pv _,
    rewrite [-+ap_con, ap_compose', ap_id],
    apply natural_square_tr },
  { intro a, reflexivity }
end

definition equiv_of_is_equiseq [constructor] (H : is_equiseq f) : seq_colim f ≃ A 0 :=
(equiv.mk _ (is_equiv_inclusion0 H))⁻¹ᵉ

variable (f)
end

section

definition rep_glue (k : ℕ) (a : A n) : ι f (rep f k a) = ι f a :=
begin
  induction k with k IH,
  { reflexivity},
  { exact glue f (rep f k a) ⬝ IH}
end

/- functorial action and equivalences -/
section functor
variables {f f' f''}
include p
definition seq_colim_functor [unfold 7] : seq_colim f → seq_colim f' :=
begin
  intro x, induction x with n a n a,
  { exact ι f' (τ a)},
  { exact ap (ι f') (p a) ⬝ glue f' (τ a)}
end
omit p

theorem seq_colim_functor_glue {n : ℕ} (a :   A n)
  : ap (seq_colim_functor τ p) (glue f a) = ap (ι f') (p a) ⬝ glue f' (τ a) :=
!elim_glue

definition seq_colim_functor_compose [constructor] (x : seq_colim f) :
  seq_colim_functor (λn x, τ' (τ x)) (λn, hvconcat (@p n) (@p' n)) x =
  seq_colim_functor τ' p' (seq_colim_functor τ p x)  :=
begin
  induction x, reflexivity,
  apply eq_pathover, apply hdeg_square,
  refine !seq_colim_functor_glue ⬝ _ ⬝ (ap_compose (seq_colim_functor _ _) _ _)⁻¹,
  refine _ ⬝ (ap02 _ proof !seq_colim_functor_glue qed ⬝ !ap_con)⁻¹,
  refine _ ⬝ (proof !ap_compose' ⬝ ap_compose (ι f'') _ _ qed ◾ proof !seq_colim_functor_glue qed)⁻¹,
  exact whisker_right _ !ap_con ⬝ !con.assoc
end

variable (f)
definition seq_colim_functor_id [constructor] (x : seq_colim f) :
  seq_colim_functor (λn, id) (λn, homotopy.rfl) x = x :=
begin
  induction x, reflexivity,
  apply eq_pathover, apply hdeg_square,
  exact !seq_colim_functor_glue ⬝ !idp_con ⬝ !ap_id⁻¹,
end
variables {f τ τ₂ p p₂}

definition seq_colim_functor_homotopy [constructor] (q : τ ~2 τ₂)
  (r : Π⦃n⦄ (a : A n), square (q (n+1) (f a)) (ap (@f' n) (q n a)) (p a) (p₂ a))
  (x : seq_colim f) :
  seq_colim_functor τ p x = seq_colim_functor τ₂ p₂ x :=
begin
  induction x,
    exact ap (ι f') (q n a),
  apply eq_pathover,
  refine !seq_colim_functor_glue ⬝ph _ ⬝hp !seq_colim_functor_glue⁻¹,
  refine aps (ι f') (r a) ⬝v !ap_compose⁻¹ ⬝pv natural_square_tr (glue f') (q n a),
end
variables (τ τ₂ p p₂)

definition is_equiv_seq_colim_functor [constructor] [H : Πn, is_equiv (@τ n)]
   : is_equiv (seq_colim_functor @τ p) :=
adjointify _ (seq_colim_functor (λn, (@τ _)⁻¹) (λn a, inv_commute' τ f f' p a))
           abstract begin
             intro x,
             refine !seq_colim_functor_compose⁻¹ ⬝ seq_colim_functor_homotopy _ _ x ⬝ !seq_colim_functor_id,
             { intro n a, exact right_inv (@τ n) a },
             { intro n a,
               refine whisker_right _ !ap_inv_commute' ⬝ !inv_con_cancel_right ⬝ whisker_left _ !ap_inv ⬝ph _,
               apply whisker_bl, apply whisker_tl, exact ids }
           end end
           abstract begin
             intro x,
             refine !seq_colim_functor_compose⁻¹ ⬝ seq_colim_functor_homotopy _ _ x ⬝ !seq_colim_functor_id,
             { intro n a, exact left_inv (@τ n) a },
             { intro n a,
               esimp [hvconcat],
               refine whisker_left _ (!inv_commute'_fn ⬝ !con.assoc) ⬝ !con_inv_cancel_left ⬝ph _,
               apply whisker_bl, apply whisker_tl, exact ids }
           end end

definition seq_colim_equiv [constructor] (τ : Π{n}, A n ≃ A' n)
  (p : Π⦃n⦄ (a : A n), τ (f a) = f' (τ a)) : seq_colim f ≃ seq_colim f' :=
equiv.mk _ (is_equiv_seq_colim_functor @τ p)

definition seq_colim_rec_unc [unfold 4] {P : seq_colim f → Type}
  (v : Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
                 Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a)
  : Π(x : seq_colim f), P x :=
by induction v with Pincl Pglue; exact seq_colim.rec f Pincl Pglue

definition is_equiv_seq_colim_rec (P : seq_colim f → Type) :
  is_equiv (seq_colim_rec_unc :
    (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
      Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a)
        → (Π (aa : seq_colim f), P aa)) :=
begin
  fapply adjointify,
  { intro s, exact ⟨λn a, s (ι f a), λn a, apd s (glue f a)⟩},
  { intro s, apply eq_of_homotopy, intro x, induction x,
    { reflexivity},
    { apply eq_pathover_dep, esimp, apply hdeg_squareover, apply rec_glue}},
  { intro v, induction v with Pincl Pglue, fapply ap (sigma.mk _),
    apply eq_of_homotopy2, intros n a, apply rec_glue},
end

/- universal property -/
definition equiv_seq_colim_rec (P : seq_colim f → Type) :
  (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
     Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a) ≃ (Π (aa : seq_colim f), P aa) :=
equiv.mk _ !is_equiv_seq_colim_rec

end functor

definition shift_up [unfold 3] (x : seq_colim f) : seq_colim (shift_diag f) :=
begin
  induction x,
  { exact ι' (shift_diag f) n (f a)},
  { exact glue (shift_diag f) (f a)}
end

definition shift_down [unfold 3] (x : seq_colim (shift_diag f)) : seq_colim f :=
begin
  induction x,
  { exact ι' f (n+1) a},
  { exact glue f a}
end

end

definition shift_equiv [constructor] : seq_colim f ≃ seq_colim (shift_diag f) :=
equiv.MK (shift_up f)
         (shift_down f)
         abstract begin
           intro x, induction x,
           { exact glue _ a },
           { apply eq_pathover,
             rewrite [▸*, ap_id, ap_compose (shift_up f) (shift_down f), ↑shift_down,
                      elim_glue],
             apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹ }
         end end
         abstract begin
           intro x, induction x,
           { exact glue _ a },
           { apply eq_pathover,
             rewrite [▸*, ap_id, ap_compose (shift_down f) (shift_up f), ↑shift_up,
                      elim_glue],
             apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹ }
         end end

/- todo: define functions back and forth explicitly -/

definition kshift'_equiv (k : ℕ) : seq_colim f ≃ seq_colim (kshift_diag' f k) :=
begin
  induction k with k IH,
  { reflexivity },
  { exact IH ⬝e shift_equiv (kshift_diag' f k) ⬝e
      seq_colim_equiv (λn, equiv_ap A (succ_add n k))
                      (λn a, proof !tr_inv_tr ⬝ !transport_lemma⁻¹ qed) }
end

definition kshift_equiv_inv (k : ℕ) : seq_colim (kshift_diag f k) ≃ seq_colim f :=
begin
  induction k with k IH,
  { exact seq_colim_equiv (λn, equiv_ap A (nat.zero_add n)) (λn a, !transport_lemma2) },
  { exact seq_colim_equiv (λn, equiv_ap A (succ_add k n))
                          (λn a, transport_lemma2 (succ_add k n) f a) ⬝e
          (shift_equiv (kshift_diag f k))⁻¹ᵉ ⬝e IH }
end

definition kshift_equiv [constructor] (k : ℕ) : seq_colim f ≃ seq_colim (kshift_diag f k) :=
(kshift_equiv_inv f k)⁻¹ᵉ

-- definition kshift_equiv2 [constructor] (k : ℕ) : seq_colim f ≃ seq_colim (kshift_diag f k) :=
-- begin
--   refine equiv_change_fun (kshift_equiv f k) _,

-- end

variable {f}
definition seq_colim_constant_seq [constructor] (X : Type) : seq_colim (constant_seq X) ≃ X :=
equiv_of_is_equiseq (λn, !is_equiv_id)

variable (f)
definition is_contr_seq_colim {A : ℕ → Type} (f : seq_diagram A)
  [Πk, is_contr (A k)] : is_contr (seq_colim f) :=
begin
  refine is_contr_is_equiv_closed (ι' f 0) _ _,
  apply is_equiv_inclusion0, intro n, exact is_equiv_of_is_contr _ _ _
end

definition seq_colim_equiv_of_is_equiv [constructor] {n : ℕ} (H : Πk, k ≥ n → is_equiv (@f k)) :
  seq_colim f ≃ A n :=
kshift_equiv f n ⬝e equiv_of_is_equiseq (λk, H (n+k) !le_add_right)

/- colimits of dependent sequences, sigma's commute with colimits -/

section over

variable {f}

definition rep_f_equiv_natural {k : ℕ} (p : P (rep f k (f a))) :
  transporto P (rep_f f (succ k) a) (g p) = g (transporto P (rep_f f k a) p) :=
(fn_tro_eq_tro_fn2 (rep_f f k a) g p)⁻¹

variable (a)
definition over_f_equiv [constructor] :
  seq_colim (seq_diagram_of_over g (f a)) ≃ seq_colim (shift_diag (seq_diagram_of_over g a)) :=
seq_colim_equiv (rep_f_equiv f P a) (λk p, rep_f_equiv_natural g p)

definition seq_colim_over_equiv :
  seq_colim (seq_diagram_of_over g (f a)) ≃ seq_colim (seq_diagram_of_over g a) :=
over_f_equiv g a ⬝e (shift_equiv (seq_diagram_of_over g a))⁻¹ᵉ

definition seq_colim_over_equiv_glue {k : ℕ} (x : P (rep f k (f a))) :
  ap (seq_colim_over_equiv g a) (glue (seq_diagram_of_over g (f a)) x) =
  ap (ι' (seq_diagram_of_over g a) (k+2)) (rep_f_equiv_natural g x) ⬝
  glue (seq_diagram_of_over g a) (rep_f f k a ▸o x) :=
begin
  refine ap_compose (shift_down (seq_diagram_of_over g a)) _ _ ⬝ _,
  exact ap02 _ !elim_glue ⬝ !ap_con ⬝ !ap_compose' ◾ !elim_glue
end

variable {a}

include g
definition seq_colim_over [unfold 5] (x : seq_colim f) : Type.{v} :=
begin
  refine seq_colim.elim_type f _ _ x,
  { intro n a, exact seq_colim (seq_diagram_of_over g a)},
  { intro n a, exact seq_colim_over_equiv g a }
end
omit g

definition ιo [constructor] (p : P a) : seq_colim_over g (ι f a) :=
ι' _ 0 p

variable {P}
theorem seq_colim_over_glue /- r -/ (x : seq_colim_over g (ι f (f a)))
  : transport (seq_colim_over g) (glue f a) x = shift_down _ (over_f_equiv g a x) :=
ap10 (elim_type_glue _ _ _ a) x

theorem seq_colim_over_glue_inv (x : seq_colim_over g (ι f a))
  : transport (seq_colim_over g) (glue f a)⁻¹ x = to_inv (over_f_equiv g a) (shift_up _ x) :=
ap10 (elim_type_glue_inv _ _ _ a) x

definition glue_over (p : P (f a)) : pathover (seq_colim_over g) (ιo g p) (glue f a) (ι' _ 1 p) :=
pathover_of_tr_eq !seq_colim_over_glue

-- we can define a function from the colimit of total spaces to the total space of the colimit.

definition glue' (p : P a) : ⟨ι f (f a), ιo g (g p)⟩ = ⟨ι f a, ιo g p⟩ :=
sigma_eq (glue f a) (glue_over g (g p) ⬝op glue (seq_diagram_of_over g a) p)

definition glue_star (k : ℕ) (x : P (rep f k (f a))) :
  ⟨ι f (f a), ι (seq_diagram_of_over g (f a)) x⟩ =
  ⟨ι f a, ι (seq_diagram_of_over g a) (to_fun (rep_f_equiv f P a k) x)⟩
  :> sigma (seq_colim_over g) :=
begin
  apply dpair_eq_dpair (glue f a),
  apply pathover_of_tr_eq,
  refine seq_colim_over_glue g (ι (seq_diagram_of_over g (f a)) x)
end

definition sigma_colim_of_colim_sigma [unfold 5] (a : seq_colim (seq_diagram_sigma g)) :
  Σ(x : seq_colim f), seq_colim_over g x :=
begin
induction a with n v n v,
{ induction v with a p, exact ⟨ι f a, ιo g p⟩},
{ induction v with a p, exact glue' g p }
end

definition colim_sigma_triangle [unfold 5] (a : seq_colim (seq_diagram_sigma g)) :
  (sigma_colim_of_colim_sigma g a).1 = seq_colim_functor (λn, sigma.pr1) (λn, homotopy.rfl) a :=
begin
induction a with n v n v,
{ induction v with a p, reflexivity },
{ induction v with a p, apply eq_pathover, apply hdeg_square,
  refine ap_compose sigma.pr1 _ _ ⬝ ap02 _ !elim_glue ⬝ _ ⬝ !elim_glue⁻¹,
  exact !sigma_eq_pr1 ⬝ !idp_con⁻¹ }
end

-- we now want to show that this function is an equivalence.

/-
  Proof of the induction principle of colim-sigma for sigma-colim.
  It's a double induction, so we have 4 cases: point-point, point-path, path-point and path-path.
  The main idea of the proof is that for the path-path case you need to fill a square, but we can
  define the point-path case as a filler for this square.
-/

open sigma

/-
  dictionary:
  Kristina | Lean
  VARIABLE NAMES (A, P, k, n, e, w are the same)
  x : A_n                     | a : A n
  a : A_n → A_{n+1}           | f : A n → A (n+1)
  y : P(n, x)                 | x : P a (maybe other variables)
  f : P(n, x) → P(n+1, a_n x) | g : P a → P (f a)
  DEFINITION NAMES
  κ   | glue
  U   | rep_f_equiv : P (n+1+k, rep f k (f x)) ≃ P (n+k+1, rep f (k+1) x)
  δ   | rep_f_equiv_natural
  F   | over_f_equiv g a ⬝e (shift_equiv (λk, P (rep f k a)) (seq_diagram_of_over g a))⁻¹ᵉ
  g_* | g_star
  g   | sigma_colim_rec_point
-/

definition glue_star_eq (k : ℕ) (x : P (rep f k (f a))) :
  glue_star g k x =
  dpair_eq_dpair (glue f a) (pathover_tr (glue f a) (ι (seq_diagram_of_over g (f a)) x)) ⬝
  ap (dpair (ι f a)) (seq_colim_over_glue g (ι (seq_diagram_of_over g (f a)) x)) :=
ap (sigma_eq _) !pathover_of_tr_eq_eq_concato ⬝ !sigma_eq_con ⬝ whisker_left _ !ap_dpair⁻¹

definition g_star_step {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Πn (a : A n) (x : P a), E ⟨ι f a, ιo g x⟩) {k : ℕ}
  (IH : Π{n} {a : A n} (x : P (rep f k a)), E ⟨ι f a, ι (seq_diagram_of_over g a) x⟩) :
  Σ(gs : Π⦃n : ℕ⦄ {a : A n} (x : P (rep f (k+1) a)), E ⟨ι f a, ι (seq_diagram_of_over g a) x⟩),
  Π⦃n : ℕ⦄ {a : A n} (x : P (rep f k (f a))),
    pathover E (IH x) (glue_star g k x) (gs (transporto P (rep_f f k a) x)) :=
begin
  fconstructor,
  { intro n a,
    refine equiv_rect (rep_f_equiv f P a k) _ _,
    intro z, refine transport E _ (IH z),
    exact glue_star g k z },
  { intro n a x, exact !pathover_tr ⬝op !equiv_rect_comp⁻¹ }
end

definition g_star /- g_* -/ {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Πn (a : A n) (x : P a), E ⟨ι f a, ιo g x⟩) {k : ℕ} :
  Π {n : ℕ} {a : A n} (x : P (rep f k a)), E ⟨ι f a, ι (seq_diagram_of_over g a) x⟩ :=
begin
  induction k with k IH: intro n a x,
  { exact e n a x },
  { apply (g_star_step g e @IH).1 }
end

definition g_star_path_left {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  {k : ℕ} {n : ℕ} {a : A n} (x : P (rep f k (f a))) :
  pathover E (g_star g e x) (glue_star g k x)
             (g_star g e (transporto P (rep_f f k a) x)) :=
by apply (g_star_step g e (@(g_star g e) k)).2

/- this is the bottom of the square we have to fill in the end -/
definition bottom_square {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k (f a))) :=
move_top_of_right (natural_square
    (λ b, dpair_eq_dpair (glue f a) (pathover_tr (glue f a) b) ⬝
      ap (dpair (ι f a)) (seq_colim_over_glue g b))
    (glue (seq_diagram_of_over g (f a)) x) ⬝hp
  ap_compose (dpair (ι f a)) (to_fun (seq_colim_over_equiv g a))
    (glue (seq_diagram_of_over g (f a)) x) ⬝hp
  (ap02 (dpair (ι f a)) (seq_colim_over_equiv_glue g a x)⁻¹)⁻¹ ⬝hp
  ap_con (dpair (ι f a))
    (ap (λx, shift_down (seq_diagram_of_over g a) (ι (shift_diag (seq_diagram_of_over g a)) x))
      (rep_f_equiv_natural g x))
    (glue (seq_diagram_of_over g a) (to_fun (rep_f_equiv f P a k) x)))

/- this is the composition + filler -/
definition g_star_path_right_step {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k (f a)))
  (IH : Π(n : ℕ) (a : A n) (x : P (rep f k a)),
  pathover E (g_star g e (seq_diagram_of_over g a x))
           (ap (dpair (ι f a)) (glue (seq_diagram_of_over g a) x))
           (g_star g e x)) :=
squareover_fill_r
  (bottom_square g e w k x)
  (change_path (glue_star_eq g (succ k) (g x)) (g_star_path_left g e w (g x)) ⬝o
    pathover_ap E (dpair (ι f a))
      (pathover_ap (λ (b : seq_colim (seq_diagram_of_over g a)), E ⟨ι f a, b⟩)
        (ι (seq_diagram_of_over g a)) (apd (g_star g e) (rep_f_equiv_natural g x))))
  (change_path (glue_star_eq g k x) (g_star_path_left g e w x))
  (IH (n+1) (f a) x)

/- this is just the composition -/
definition g_star_path_right_step1 {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k (f a)))
  (IH : Π(n : ℕ) (a : A n) (x : P (rep f k a)),
  pathover E (g_star g e (seq_diagram_of_over g a x))
           (ap (dpair (ι f a)) (glue (seq_diagram_of_over g a) x))
           (g_star g e x)) :=
(g_star_path_right_step g e w k x IH).1

definition g_star_path_right {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (k : ℕ) {n : ℕ} {a : A n} (x : P (rep f k a)) :
  pathover E (g_star g e (seq_diagram_of_over g a x))
           (ap (dpair (ι f a)) (glue (seq_diagram_of_over g a) x))
           (g_star g e x) :=
begin
  revert n a x, induction k with k IH: intro n a x,
  { exact abstract begin refine pathover_cancel_left !pathover_tr⁻¹ᵒ (change_path _ (w x)),
    apply sigma_eq_concato_eq end end },
  { revert x, refine equiv_rect (rep_f_equiv f P a k) _ _, intro x,
    exact g_star_path_right_step1 g e w k x IH }
end

definition sigma_colim_rec_point [unfold 10] /- g -/ {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  {n : ℕ} {a : A n} (x : seq_colim_over g (ι f a)) : E ⟨ι f a, x⟩ :=
begin
  induction x with k x k x,
  { exact g_star g e x },
  { apply pathover_of_pathover_ap E (dpair (ι f a)),
    exact g_star_path_right g e w k x }
end

definition sigma_colim_rec {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  (v : Σ(x : seq_colim f), seq_colim_over g x) : E v :=
begin
  induction v with x y,
  induction x with n a n a,
  { exact sigma_colim_rec_point g e w y },
  { apply pi_pathover_left, intro x,
    refine change_path (whisker_left _ !ap_inv ⬝ !con_inv_cancel_right)
      (_ ⬝o pathover_ap E (dpair _) (apd (sigma_colim_rec_point g e w) !seq_colim_over_glue⁻¹)),
    /- we can simplify the squareover we need to fill a bit if we apply this rule here -/
    -- refine change_path (ap (sigma_eq (glue f a)) !pathover_of_tr_eq_eq_concato ⬝ !sigma_eq_con ⬝ whisker_left _ !ap_dpair⁻¹) _,
    induction x with k x k x,
    { exact change_path !glue_star_eq (g_star_path_left g e w x) },
    -- { exact g_star_path_left g e w x },
    { apply pathover_pathover, esimp,
      refine _ ⬝hop (ap (pathover_ap E _) (apd_compose2 (sigma_colim_rec_point g e w) _ _) ⬝
        pathover_ap_pathover_of_pathover_ap E (dpair (ι f a)) (seq_colim_over_equiv g a) _)⁻¹,
      apply squareover_change_path_right',
      refine _ ⬝hop !pathover_ap_change_path⁻¹ ⬝ ap (pathover_ap E _)
        (apd02 _ !seq_colim_over_equiv_glue⁻¹),
      apply squareover_change_path_right,
      refine _ ⬝hop (ap (pathover_ap E _) (!apd_con ⬝ (!apd_ap ◾o idp)) ⬝ !pathover_ap_cono)⁻¹,
      apply squareover_change_path_right',
      apply move_right_of_top_over,
      refine _ ⬝hop (ap (pathover_ap E _) !rec_glue ⬝ to_right_inv !pathover_compose _)⁻¹,
      refine ap (pathover_ap E _) !rec_glue ⬝ to_right_inv !pathover_compose _ ⬝pho _,
      refine _ ⬝hop !equiv_rect_comp⁻¹,
      exact (g_star_path_right_step g e w k x @(g_star_path_right g e w k)).2 }}
end


/- We now define the map back, and show using this induction principle that the composites are the identity -/
variable {P}

definition colim_sigma_of_sigma_colim_constructor [unfold 7] (p : seq_colim_over g (ι f a))
  : seq_colim (seq_diagram_sigma g) :=
begin
  induction p with k p k p,
  { exact ι _ ⟨rep f k a, p⟩},
  { apply glue}
end

definition colim_sigma_of_sigma_colim_path1 /- μ -/ {k : ℕ} (p : P (rep f k (f a))) :
  ι (seq_diagram_sigma g) ⟨rep f k (f a), p⟩ =
  ι (seq_diagram_sigma g) ⟨rep f (succ k) a, transporto P (rep_f f k a) p⟩ :=
begin
  apply apd0111 (λn a p, ι' (seq_diagram_sigma g) n ⟨a, p⟩) (succ_add n k) (rep_f f k a),
  apply pathover_tro
end

definition colim_sigma_of_sigma_colim_path2 {k : ℕ} (p : P (rep f k (f a))) :
square (colim_sigma_of_sigma_colim_path1 g (g p)) (colim_sigma_of_sigma_colim_path1 g p)
  (ap (colim_sigma_of_sigma_colim_constructor g) (glue (seq_diagram_of_over g (f a)) p))
  (ap (λx, colim_sigma_of_sigma_colim_constructor g (shift_down (seq_diagram_of_over g a)
        (seq_colim_functor (λk, transporto P (rep_f f k a)) (λk p, rep_f_equiv_natural g p) x)))
    (glue (seq_diagram_of_over g (f a)) p)) :=
begin
  refine !elim_glue ⬝ph _,
  refine _ ⬝hp (ap_compose' (colim_sigma_of_sigma_colim_constructor g) _ _),
  refine _ ⬝hp ap02 _ !seq_colim_over_equiv_glue⁻¹,
  refine _ ⬝hp !ap_con⁻¹,
  refine _ ⬝hp !ap_compose ◾ !elim_glue⁻¹,
  refine _ ⬝pv whisker_rt _ (natural_square0111 P (pathover_tro (rep_f f k a) p) g
                                                  (λn a p, glue (seq_diagram_sigma g) ⟨a, p⟩)),
  refine _ ⬝ whisker_left _ (ap02 _ !inv_inv⁻¹ ⬝ !ap_inv),
  symmetry, apply apd0111_precompose
end

definition colim_sigma_of_sigma_colim [unfold 5] (v : Σ(x : seq_colim f), seq_colim_over g x)
  : seq_colim (seq_diagram_sigma g) :=
begin
  induction v with x p,
  induction x with n a n a,
  { exact colim_sigma_of_sigma_colim_constructor g p },
  apply arrow_pathover_constant_right, intro x, esimp at x,
  refine _ ⬝ ap (colim_sigma_of_sigma_colim_constructor g) !seq_colim_over_glue⁻¹,
  induction x with k p k p,
  { exact colim_sigma_of_sigma_colim_path1 g p },
  apply eq_pathover, apply colim_sigma_of_sigma_colim_path2
end

definition colim_sigma_of_sigma_colim_glue' [unfold 5] (p : P a)
  : ap (colim_sigma_of_sigma_colim g) (glue' g p) = glue (seq_diagram_sigma g) ⟨a, p⟩ :=
begin
  refine !ap_dpair_eq_dpair ⬝ _,
  refine !apd011_eq_apo11_apd ⬝ _,
  refine ap (λx, apo11_constant_right x _) !rec_glue ⬝ _,
  refine !apo11_arrow_pathover_constant_right ⬝ _, esimp,
  refine whisker_right _ !idp_con ⬝ _,
  rewrite [▸*, tr_eq_of_pathover_concato_eq, ap_con, ↑glue_over,
           to_right_inv !pathover_equiv_tr_eq, ap_inv, inv_con_cancel_left],
  apply elim_glue
end

theorem colim_sigma_of_sigma_colim_of_colim_sigma (a : seq_colim (seq_diagram_sigma g)) :
  colim_sigma_of_sigma_colim g (sigma_colim_of_colim_sigma g a) = a :=
begin
induction a with n v n v,
{ induction v with a p, reflexivity },
{ induction v with a p, esimp, apply eq_pathover_id_right, apply hdeg_square,
  refine ap_compose (colim_sigma_of_sigma_colim g) _ _ ⬝ _,
  refine ap02 _ !elim_glue ⬝ _, exact colim_sigma_of_sigma_colim_glue' g p }
end

theorem sigma_colim_of_colim_sigma_of_sigma_colim (v : Σ(x : seq_colim f), seq_colim_over g x)
  : sigma_colim_of_colim_sigma g (colim_sigma_of_sigma_colim g v) = v :=
begin
  revert v, refine sigma_colim_rec _ _ _,
  { intro n a x, reflexivity },
  { intro n a x, apply eq_pathover_id_right, apply hdeg_square,
    refine ap_compose (sigma_colim_of_colim_sigma g) _ _ ⬝ _,
    refine ap02 _ (colim_sigma_of_sigma_colim_glue' g x) ⬝ _,
    apply elim_glue }
end

variable (P)
definition sigma_seq_colim_over_equiv [constructor]
  : (Σ(x : seq_colim f), seq_colim_over g x) ≃ seq_colim (seq_diagram_sigma g) :=
equiv.MK (colim_sigma_of_sigma_colim g)
         (sigma_colim_of_colim_sigma g)
         (colim_sigma_of_sigma_colim_of_colim_sigma g)
         (sigma_colim_of_colim_sigma_of_sigma_colim g)

end over

definition seq_colim_id_equiv_seq_colim_id0 (a₀ a₁ : A 0) :
  seq_colim (id_seq_diagram f 0 a₀ a₁) ≃ seq_colim (id0_seq_diagram f a₀ a₁) :=
seq_colim_equiv
  (λn, !lrep_eq_lrep_irrel (nat.zero_add n))
  (λn p, !lrep_eq_lrep_irrel_natural)

definition kshift_equiv_inv_incl_kshift_diag {n k : ℕ} (x : A (n + k)) :
  kshift_equiv_inv f n (ι' (kshift_diag f n) k x) = ι f x :=
begin
  revert A f k x, induction n with n IH: intro A f k x,
  { exact apd011 (ι' f) !nat.zero_add⁻¹ !pathover_tr⁻¹ᵒ },
  { exact !IH ⬝ apd011 (ι' f) !succ_add⁻¹ !pathover_tr⁻¹ᵒ }
end

definition incl_kshift_diag {n k : ℕ} (x : A (n + k)) :
  ι' (kshift_diag f n) k x = kshift_equiv f n (ι f x) :=
eq_inv_of_eq (kshift_equiv_inv_incl_kshift_diag f x)

definition incl_kshift_diag0 {n : ℕ} (x : A n) :
  ι' (kshift_diag f n) 0 x = kshift_equiv f n (ι f x) :=
incl_kshift_diag f x

definition seq_colim_eq_equiv0' (a₀ a₁ : A 0) :
  ι f a₀ = ι f a₁ ≃ seq_colim (id_seq_diagram f 0 a₀ a₁) :=
begin
  refine total_space_method (ι f a₀) (seq_colim_over (id0_seq_diagram_over f a₀))
    _ _ (ι f a₁) ⬝e _,
  { apply @(is_trunc_equiv_closed_rev _ (sigma_seq_colim_over_equiv _ _)),
    apply is_contr_seq_colim },
  { exact ιo _ idp },
  /-
    In the next equivalence we have to show that
      seq_colim_over (id0_seq_diagram_over f a₀) (ι f a₁) ≃ seq_colim (id_seq_diagram f 0 a₀ a₁).
    This looks trivial, because both of them reduce to
      seq_colim (f^{0 ≤ 0+k}(a₀) = f^{0 ≤ 0+k}(a₁), ap_f).
    However, not all proofs of these inequalities are definitionally equal. 3 of them are proven by
      zero_le : 0 ≤ n,
    but one of them (the RHS of seq_colim_over (id0_seq_diagram_over f a₀) (ι f a₁)) uses
      le_add_right : n ≤ n+k
    Alternatively, we could redefine le_add_right so that for n=0, it reduces to `zero_le (0+k)`.
  -/
  { refine seq_colim_equiv (λn, eq_equiv_eq_closed !lrep_irrel idp) _,
    intro n p, refine whisker_right _ (!lrep_irrel2⁻² ⬝ !ap_inv⁻¹) ⬝ !ap_con⁻¹ }
end

-- definition seq_colim_eq_equiv0'_natural {a₀ a₁ : A 0} {a₀' a₁' : A' 0} (p₀ : τ a₀ = a₀')
--   (p₁ : τ a₁ = a₁') :
--   hsquare (seq_colim_eq_equiv0' f a₀ a₁) (seq_colim_eq_equiv0' f' a₀' a₁')
--     (pointed.ap1_gen (seq_colim_functor τ p) (ap (ι' f' 0) p₀) (ap (ι' f' 0) p₁))
--     (seq_colim_functor (λn, pointed.ap1_gen (@τ _)) _) :=
-- _

definition seq_colim_eq_equiv0 (a₀ a₁ : A 0) : ι f a₀ = ι f a₁ ≃ seq_colim (id0_seq_diagram f a₀ a₁) :=
seq_colim_eq_equiv0' f a₀ a₁ ⬝e seq_colim_id_equiv_seq_colim_id0 f a₀ a₁

definition seq_colim_eq_equiv {n : ℕ} (a₀ a₁ : A n) :
  ι f a₀ = ι f a₁ ≃ seq_colim (id_seq_diagram f n a₀ a₁) :=
eq_equiv_fn_eq (kshift_equiv f n) (ι f a₀) (ι f a₁) ⬝e
eq_equiv_eq_closed (incl_kshift_diag0 f a₀)⁻¹ (incl_kshift_diag0 f a₁)⁻¹ ⬝e
seq_colim_eq_equiv0' (kshift_diag f n) a₀ a₁ ⬝e
@seq_colim_equiv _ _ _ (λk, ap (@f _))
  (λm, eq_equiv_eq_closed !lrep_kshift_diag !lrep_kshift_diag)
  (λm p, whisker_right _ (whisker_right _ !ap_inv⁻¹ ⬝ !ap_con⁻¹) ⬝ !ap_con⁻¹) ⬝e
seq_colim_equiv
  (λm, !lrep_eq_lrep_irrel (ap (add n) (nat.zero_add m)))
  begin
    intro m q,
    refine _ ⬝ lrep_eq_lrep_irrel_natural f (le_add_right n m) (ap (add n) (nat.zero_add m)) q,
    exact ap (λx, lrep_eq_lrep_irrel f _ _ _ _ x _) !is_prop.elim
  end

open algebra
theorem is_trunc_seq_colim [instance] (k : ℕ₋₂) [H : Πn, is_trunc k (A n)] :
  is_trunc k (seq_colim f) :=
begin
  revert A f H, induction k with k IH: intro A f H,
  { apply is_contr_seq_colim },
  { apply is_trunc_succ_intro, intro x y,
    induction x using seq_colim.rec_prop with n a,
    induction y using seq_colim.rec_prop with m a',
    apply is_trunc_equiv_closed,
      exact eq_equiv_eq_closed (lrep_glue _ (le_max_left n m) _) (lrep_glue _ (le_max_right n m) _),
    apply is_trunc_equiv_closed_rev,
      apply seq_colim_eq_equiv,
    apply IH, intro l, apply is_trunc_eq }
end

definition seq_colim_trunc_of_trunc_seq_colim [unfold 4] (k : ℕ₋₂) (x : trunc k (seq_colim f)) :
  seq_colim (trunc_diagram k f) :=
begin induction x with x, exact seq_colim_functor (λn, tr) (λn y, idp) x end

definition trunc_seq_colim_of_seq_colim_trunc [unfold 4] (k : ℕ₋₂)
  (x : seq_colim (trunc_diagram k f)) : trunc k (seq_colim f) :=
begin
  induction x with n x n x,
  { induction x with a, exact tr (ι f a) },
  { induction x with a, exact ap tr (glue f a) }
end

definition trunc_seq_colim_equiv [constructor] (k : ℕ₋₂) :
  trunc k (seq_colim f) ≃ seq_colim (trunc_diagram k f) :=
equiv.MK (seq_colim_trunc_of_trunc_seq_colim f k) (trunc_seq_colim_of_seq_colim_trunc f k)
  abstract begin
    intro x, induction x with n x n x,
    { induction x with a, reflexivity },
    { induction x with a, apply eq_pathover_id_right, apply hdeg_square,
      refine ap_compose (seq_colim_trunc_of_trunc_seq_colim f k) _ _ ⬝ ap02 _ !elim_glue ⬝ _,
      refine !ap_compose' ⬝ !elim_glue ⬝ _, exact !idp_con }
  end end
  abstract begin
    intro x, induction x with x, induction x with n a n a,
    { reflexivity },
    { apply eq_pathover, apply hdeg_square,
      refine ap_compose (trunc_seq_colim_of_seq_colim_trunc f k) _ _ ⬝ ap02 _ !elim_glue ⬝ _,
      refine !ap_compose' ⬝ !elim_glue }
  end end

theorem is_conn_seq_colim [instance] (k : ℕ₋₂) [H : Πn, is_conn k (A n)] :
  is_conn k (seq_colim f) :=
is_trunc_equiv_closed_rev -2 (trunc_seq_colim_equiv f k) _

/- the colimit of a sequence of fibers is the fiber of the functorial action of the colimit -/
definition domain_seq_colim_functor {A A' : ℕ → Type} {f : seq_diagram A}
  {f' : seq_diagram A'} (τ : Πn, A' n → A n)
  (p : Π⦃n⦄, τ (n+1) ∘ @f' n ~ @f n ∘ @τ n) :
    (Σ(x : seq_colim f), seq_colim_over (seq_diagram_over_fiber τ p) x) ≃ seq_colim f' :=
begin
  transitivity seq_colim (seq_diagram_sigma (seq_diagram_over_fiber τ p)),
    exact sigma_seq_colim_over_equiv _ (seq_diagram_over_fiber τ p),
    exact seq_colim_equiv (λn, sigma_fiber_equiv (τ n)) (λn x, idp)
end

definition fiber_seq_colim_functor {A A' : ℕ → Type} {f : seq_diagram A}
  {f' : seq_diagram A'} (τ : Πn, A' n → A n)
  (p : Π⦃n⦄, τ (n+1) ∘ @f' n ~ @f n ∘ @τ n) {n : ℕ} (a : A n) :
    fiber (seq_colim_functor τ p) (ι f a) ≃ seq_colim (seq_diagram_fiber τ p a) :=
begin
  refine _ ⬝e fiber_pr1 (seq_colim_over (seq_diagram_over_fiber τ p)) (ι f a),
  apply fiber_equiv_of_triangle (domain_seq_colim_functor τ p)⁻¹ᵉ,
  refine _ ⬝hty λx, (colim_sigma_triangle _ _)⁻¹,
  apply homotopy_inv_of_homotopy_pre (seq_colim_equiv _ _)
          (seq_colim_functor _ _) (seq_colim_functor _ _),
  refine (λx, !seq_colim_functor_compose⁻¹) ⬝hty _,
  refine seq_colim_functor_homotopy _ _,
  intro n x, exact point_eq x.2,
  intro n x, induction x with x y, induction y with y q, induction q,
  apply square_of_eq, refine !idp_con⁻¹
end

definition fiber_seq_colim_functor0 {A A' : ℕ → Type} {f : seq_diagram A}
  {f' : seq_diagram A'} (τ : Πn, A' n → A n)
  (p : Π⦃n⦄, τ (n+1) ∘ @f' n ~ @f n ∘ @τ n) (a : A 0) :
    fiber (seq_colim_functor τ p) (ι f a) ≃ seq_colim (seq_diagram_fiber0 τ p a) :=
fiber_seq_colim_functor τ p a ⬝e
seq_colim_equiv
  (λn, equiv_apd011 (λx y, fiber (τ x) y) (rep_pathover_rep0 f a))
  (λn x, sorry)
-- maybe use fn_tro_eq_tro_fn2

variables {f f'}
definition fiber_inclusion (x : seq_colim f) :
  fiber (ι' f 0) x ≃ fiber (seq_colim_functor (rep0 f) (λn a, idp)) x :=
fiber_equiv_of_triangle (seq_colim_constant_seq (A 0))⁻¹ᵉ homotopy.rfl

theorem is_trunc_fun_seq_colim_functor (k : ℕ₋₂) (H : Πn, is_trunc_fun k (@τ n)) :
  is_trunc_fun k (seq_colim_functor τ p) :=
begin
  intro x, induction x using seq_colim.rec_prop,
  exact is_trunc_equiv_closed_rev k (fiber_seq_colim_functor τ p a) _
end

open is_conn
theorem is_conn_fun_seq_colim_functor (k : ℕ₋₂) (H : Πn, is_conn_fun k (@τ n)) :
  is_conn_fun k (seq_colim_functor τ p) :=
begin
  intro x, induction x using seq_colim.rec_prop,
  exact is_conn_equiv_closed_rev k (fiber_seq_colim_functor τ p a) _
end

variables (f f')
theorem is_trunc_fun_inclusion (k : ℕ₋₂) (H : Πn, is_trunc_fun k (@f n)) :
  is_trunc_fun k (ι' f 0) :=
begin
  intro x,
  apply is_trunc_equiv_closed_rev k (fiber_inclusion x),
  apply is_trunc_fun_seq_colim_functor,
  intro n, apply is_trunc_fun_lrep, exact H
end

theorem is_conn_fun_inclusion (k : ℕ₋₂) (H : Πn, is_conn_fun k (@f n)) :
  is_conn_fun k (ι' f 0) :=
begin
  intro x,
  apply is_conn_equiv_closed_rev k (fiber_inclusion x),
  apply is_conn_fun_seq_colim_functor,
  intro n, apply is_conn_fun_lrep, exact H
end

/- the sequential colimit of standard finite types is ℕ -/
open fin
definition nat_of_seq_colim_fin [unfold 1] (x : seq_colim seq_diagram_fin) : ℕ :=
begin
  induction x with n x n x,
  { exact x },
  { reflexivity }
end

definition seq_colim_fin_of_nat (n : ℕ) : seq_colim seq_diagram_fin :=
ι' _ (n+1) (fin.mk n (self_lt_succ n))

definition lrep_seq_diagram_fin {n : ℕ} (x : fin n) :
  lrep seq_diagram_fin (is_lt x) (fin.mk x (self_lt_succ x)) = x :=
begin
  induction x with k H, esimp, induction H with n H p,
    reflexivity,
  exact ap (@lift_succ _) p
end

definition lrep_seq_diagram_fin_lift_succ {n : ℕ} (x : fin n) :
  lrep_seq_diagram_fin (lift_succ x) = ap (@lift_succ _) (lrep_seq_diagram_fin x) :=
begin
  induction x with k H, reflexivity
end

definition seq_colim_fin_equiv [constructor] : seq_colim seq_diagram_fin ≃ ℕ :=
equiv.MK nat_of_seq_colim_fin seq_colim_fin_of_nat
  abstract begin
    intro n, reflexivity
  end end
  abstract begin
    intro x, induction x with n x n x,
    { esimp, refine (lrep_glue _ (is_lt x) _)⁻¹ ⬝ ap (ι _) (lrep_seq_diagram_fin x), },
    { apply eq_pathover_id_right,
      refine ap_compose seq_colim_fin_of_nat _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
      esimp, refine (square_of_eq !con_idp)⁻¹ʰ ⬝h _,
      refine _ ⬝pv natural_square_tr (@glue _ (seq_diagram_fin) n) (lrep_seq_diagram_fin x),
      refine ap02 _ !lrep_seq_diagram_fin_lift_succ ⬝ !ap_compose⁻¹ }
  end end

/- the sequential colimit of embeddings is an embedding -/

definition seq_colim_eq_equiv0'_inv_refl (a₀ : A 0) :
  (seq_colim_eq_equiv0' f a₀ a₀)⁻¹ᵉ (ι' (id_seq_diagram f 0 a₀ a₀) 0 proof (refl a₀) qed) = refl (ι f a₀) :=
begin
  apply inv_eq_of_eq,
  reflexivity,
end

definition is_embedding_ι (H : Πn, is_embedding (@f n)) : is_embedding (ι' f 0) :=
begin
  intro x y, fapply is_equiv_of_equiv_of_homotopy,
  { symmetry, refine seq_colim_eq_equiv0' f x y ⬝e _,
    apply equiv_of_is_equiseq, intro n, apply H },
  { intro p, induction p, apply seq_colim_eq_equiv0'_inv_refl }
end

-- print axioms sigma_seq_colim_over_equiv
-- print axioms seq_colim_eq_equiv
-- print axioms fiber_seq_colim_functor
-- print axioms is_trunc_seq_colim
-- print axioms trunc_seq_colim_equiv
-- print axioms is_conn_seq_colim
-- print axioms is_trunc_fun_seq_colim_functor
-- print axioms is_conn_fun_seq_colim_functor
-- print axioms is_trunc_fun_inclusion
-- print axioms is_conn_fun_inclusion

end seq_colim
