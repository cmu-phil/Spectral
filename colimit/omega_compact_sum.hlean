import .omega_compact ..homotopy.fwedge

open eq nat seq_colim is_trunc equiv is_equiv trunc sigma sum pi function algebra sigma.ops

variables {A A' : ℕ → Type} (f : seq_diagram A) (f' : seq_diagram A') {n : ℕ} (a : A n)
universe variable u

definition kshift_up (k : ℕ) (x : seq_colim f) : seq_colim (kshift_diag f k) :=
begin
  induction x with n a n a,
  { apply ι' (kshift_diag f k) n, exact lrep f (le_add_left n k) a },
  { exact ap (ι _) (lrep_f f _ a ⬝ lrep_irrel f _ _ a ⬝ !f_lrep⁻¹) ⬝ !glue }
end

definition kshift_down [unfold 4] (k : ℕ) (x : seq_colim (kshift_diag f k)) : seq_colim f :=
begin
  induction x with n a n a,
  { exact ι' f (k + n) a },
  { exact glue f a }
end

definition kshift_equiv_eq_kshift_up (k : ℕ) (a : A n) : kshift_equiv f k (ι f a) = kshift_up f k (ι f a) :=
begin
  induction k with k p,
  { exact ap (ι _) !lrep_eq_transport⁻¹ },
  { exact sorry }
end

definition kshift_equiv2 [constructor] (k : ℕ) : seq_colim f ≃ seq_colim (kshift_diag f k) :=
begin
  refine equiv_change_fun (kshift_equiv f k) _,
    exact kshift_up f k,
  intro x, induction x with n a n a,
  { exact kshift_equiv_eq_kshift_up f k a },
  { exact sorry }
end

definition kshift_equiv_inv_eq_kshift_down (k : ℕ) (a : A (k + n)) :
  kshift_equiv_inv f k (ι' (kshift_diag f k) n a) = kshift_down f k (ι' (kshift_diag f k) n a) :=
begin
  induction k with k p,
  { exact apd011 (ι' _) _ !pathover_tr⁻¹ᵒ },
  { exact sorry }
end

definition kshift_equiv_inv2 [constructor] (k : ℕ) : seq_colim (kshift_diag f k) ≃ seq_colim f :=
begin
  refine equiv_change_fun (equiv_change_inv (kshift_equiv_inv f k) _) _,
  { exact kshift_up f k },
  { intro x, induction x with n a n a,
    { exact kshift_equiv_eq_kshift_up f k a },
    { exact sorry }},
  { exact kshift_down f k },
  { intro x, induction x with n a n a,
    { exact !kshift_equiv_inv_eq_kshift_down },
    { exact sorry }}
end

definition seq_colim_over_weakened_sequence [unfold 5] (x : seq_colim f) :
  seq_colim_over (weakened_sequence f f') x ≃ seq_colim f' :=
begin
  induction x with n a n a,
  { exact kshift_equiv_inv2 f' n },
  { apply equiv_pathover_inv, apply arrow_pathover_constant_left, intro x,
    apply pathover_of_tr_eq, refine !seq_colim_over_glue ⬝ _, exact sorry }
end

definition seq_colim_prod' [constructor] : seq_colim (seq_diagram_prod f f') ≃ seq_colim f × seq_colim f' :=
calc
  seq_colim (seq_diagram_prod f f') ≃ seq_colim (seq_diagram_sigma (weakened_sequence f f')) :
        by exact seq_colim_equiv (λn, !sigma.equiv_prod⁻¹ᵉ) (λn a, idp)
  ... ≃ Σ(x : seq_colim f), seq_colim_over (weakened_sequence f f') x :
        by exact (sigma_seq_colim_over_equiv _ (weakened_sequence f f'))⁻¹ᵉ
  ... ≃ Σ(x : seq_colim f), seq_colim f' :
        by exact sigma_equiv_sigma_right (seq_colim_over_weakened_sequence f f')
  ... ≃ seq_colim f × seq_colim f' :
        by exact sigma.equiv_prod (seq_colim f) (seq_colim f')

open prod prod.ops
example {a' : A' n} : seq_colim_prod' f f' (ι _ (a, a')) = (ι f a, ι f' a') := idp

definition seq_colim_prod_inv {a' : A' n} : (seq_colim_prod' f f')⁻¹ᵉ (ι f a, ι f' a') = (ι _ (a, a')) :=
begin
  exact sorry
end

definition prod_seq_colim_of_seq_colim_prod (x : seq_colim (seq_diagram_prod f f')) :
  seq_colim f × seq_colim f' :=
begin
  induction x with n x n x,
  { exact (ι f x.1, ι f' x.2) },
  { exact prod_eq (glue f x.1) (glue f' x.2) }
end

definition seq_colim_prod [constructor] :
  seq_colim (seq_diagram_prod f f') ≃ seq_colim f × seq_colim f' :=
begin
  refine equiv_change_fun (seq_colim_prod' f f') _,
    exact prod_seq_colim_of_seq_colim_prod f f',
  intro x, induction x with n x n x,
  { reflexivity },
  { induction x with a a', apply eq_pathover, apply hdeg_square, esimp,
    refine _ ⬝ !elim_glue⁻¹,
    refine ap_compose ((sigma.equiv_prod (seq_colim f) (seq_colim f') ∘
                       sigma_equiv_sigma_right (seq_colim_over_weakened_sequence f f')) ∘
                       sigma_colim_of_colim_sigma (weakened_sequence f f')) _ _ ⬝ _,
    refine ap02 _ (!elim_glue ⬝ !idp_con) ⬝ _,
    refine !ap_compose ⬝ _, refine ap02 _ !elim_glue ⬝ _,
    refine !ap_compose ⬝ _, esimp, refine ap02 _ !ap_sigma_functor_id_sigma_eq ⬝ _,
    apply eq_of_fn_eq_fn (prod_eq_equiv _ _), apply pair_eq,
    { exact !ap_compose'⁻¹ ⬝ !sigma_eq_pr1 ⬝ !prod_eq_pr1⁻¹ },
    { refine !ap_compose'⁻¹ ⬝ _ ⬝ !prod_eq_pr2⁻¹, esimp,
      refine !sigma_eq_pr2_constant ⬝ _,
      refine !eq_of_pathover_apo ⬝ _, exact sorry }}
end

  local attribute equiv_of_omega_compact [constructor]

  definition omega_compact_sum [instance] [constructor] {X Y : Type} [omega_compact.{_ u} X]
    [omega_compact.{u u} Y] : omega_compact.{_ u} (X ⊎ Y) :=
  begin
    fapply omega_compact_of_equiv,
    { intro A f,
      exact calc
      seq_colim (seq_diagram_arrow_left f (X ⊎ Y))
          ≃ seq_colim (seq_diagram_prod (seq_diagram_arrow_left f X) (seq_diagram_arrow_left f Y)) :
            by exact seq_colim_equiv (λn, !imp_prod_imp_equiv_sum_imp⁻¹ᵉ) (λn f, idp)
      ... ≃ seq_colim (seq_diagram_arrow_left f X) × seq_colim (seq_diagram_arrow_left f Y) :
            by apply seq_colim_prod
      ... ≃ (X → seq_colim f) × (Y → seq_colim f) :
            by exact prod_equiv_prod (equiv_of_omega_compact X f) (equiv_of_omega_compact Y f)
      ... ≃ ((X ⊎ Y) → seq_colim f) :
            by exact !imp_prod_imp_equiv_sum_imp },
    { intros, induction x with x y: reflexivity },
    { intros, induction x with x y: apply hdeg_square,
      { refine ap_compose (((λz, arrow_colim_of_colim_arrow f z _) ∘ pr1) ∘
          seq_colim_prod _ _) _ _ ⬝ _, refine ap02 _ (!elim_glue ⬝ !idp_con) ⬝ _,
        refine !ap_compose ⬝ _, refine ap02 _ !elim_glue ⬝ _,
        refine !ap_compose ⬝ _, refine ap02 _ !prod_eq_pr1 ⬝ !elim_glue },
      { refine ap_compose (((λz, arrow_colim_of_colim_arrow f z _) ∘ pr2) ∘
          seq_colim_prod _ _) _ _ ⬝ _, refine ap02 _ (!elim_glue ⬝ !idp_con) ⬝ _,
        refine !ap_compose ⬝ _, refine ap02 _ !elim_glue ⬝ _,
        refine !ap_compose ⬝ _, refine ap02 _ !prod_eq_pr2 ⬝ !elim_glue }},
  end

open wedge pointed circle

/- needs fwedge! -/
definition seq_diagram_fwedge (X : Type*) : seq_diagram (λn, @fwedge (A n) (λa, X)) :=
sorry f

definition seq_colim_fwedge_equiv (X : Type*) [is_trunc 1 X] :
  seq_colim (seq_diagram_fwedge f X) ≃ @fwedge (seq_colim f) (λn, X) :=
sorry

definition not_omega_compact_fwedge_nat_circle : ¬(omega_compact.{0 0} (@fwedge ℕ (λn, S¹*))) :=
assume H,
sorry
