-- authors: Floris van Doorn, Egbert Rijke

import hit.colimit types.fin homotopy.chain_complex .move_to_lib
open seq_colim pointed algebra eq is_trunc nat is_equiv equiv sigma sigma.ops chain_complex

namespace seq_colim

  definition pseq_colim [constructor] {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) : Type* :=
  pointed.MK (seq_colim f) (@sι _ _ 0 pt)

  -- TODO: we need to prove this
  definition pseq_colim_loop {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) :
    Ω (pseq_colim f) ≃* pseq_colim (λn, Ω→(f n)) :=
 sorry

  definition seq_diagram [reducible] (A : ℕ → Type) : Type := Π⦃n⦄, A n → A (succ n)

  structure Seq_diagram : Type :=
    (carrier : ℕ → Type)
    (struct : seq_diagram carrier)

  definition is_equiseq [reducible] {A : ℕ → Type} (f : seq_diagram A) : Type :=
  forall (n : ℕ), is_equiv (@f n)

  structure Equi_seq : Type :=
    (carrier : ℕ → Type)
    (maps : seq_diagram carrier)
    (prop : is_equiseq maps)

  protected abbreviation Mk [constructor] := Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [coercion]

  variables {A : ℕ → Type} (f : seq_diagram A)
  include f

  definition rep0 [reducible] (k : ℕ) : A 0 → A k :=
  begin
    intro a,
    induction k with k x,
      exact a,
      exact f x
  end

  definition is_equiv_rep0 [constructor] [H : is_equiseq f] (k : ℕ) :
    is_equiv (rep0 f k) :=
  begin
    induction k with k IH,
    { apply is_equiv_id},
    { apply is_equiv_compose (@f _) (rep0 f k)},
  end

  local attribute is_equiv_rep0 [instance]
  definition rep0_back [reducible] [H : is_equiseq f] (k : ℕ) : A k → A 0 :=
  (rep0 f k)⁻¹

  section generalized_rep
  variable {n : ℕ}

  definition rep [reducible] (k : ℕ) (a : A n) : A (n + k) :=
  by induction k with k x; exact a; exact f x

  definition rep_f (k : ℕ) (a : A n) : pathover A (rep f k (f a)) (succ_add n k) (rep f (succ k) a) :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end

  definition rep_back [H : is_equiseq f] (k : ℕ) (a : A (n + k)) : A n :=
  begin
    induction k with k g,
    exact a,
    exact g ((@f (n + k))⁻¹ a),
  end

  definition is_equiv_rep [constructor] [H : is_equiseq f] (k : ℕ) :
    is_equiv (λ (a : A n), rep f k a) :=
  begin
    fapply adjointify,
    { exact rep_back f k},
    { induction k with k IH: intro b,
      { reflexivity},
      unfold rep,
      unfold rep_back,
      fold [rep f k (rep_back f k ((@f (n+k))⁻¹ b))],
      refine ap (@f (n+k)) (IH ((@f (n+k))⁻¹ b)) ⬝ _,
      apply right_inv (@f (n+k))},
    induction k with k IH: intro b,
    exact rfl,
    unfold rep_back,
    unfold rep,
    fold [rep f k b],
    refine _ ⬝ IH b,
    exact ap (rep_back f k) (left_inv (@f (n+k)) (rep f k b))
  end

  definition rep_rep (k l : ℕ) (a : A n) :
    pathover A (rep f k (rep f l a)) (nat.add_assoc n l k) (rep f (l + k) a) :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end

  definition f_rep (k : ℕ) (a : A n) : f (rep f k a) = rep f (succ k) a := idp
  end generalized_rep

  section shift

  definition shift_diag [unfold_full] : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  definition kshift_diag [unfold_full] (k : ℕ) : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  definition kshift_diag' [unfold_full] (k : ℕ) : seq_diagram (λn, A (n + k)) :=
  λn a, transport A (succ_add n k)⁻¹ (f a)
  end shift

  section constructions

    omit f

    definition constant_seq (X : Type) : seq_diagram (λ n, X) :=
    λ n x, x

    definition seq_diagram_arrow_left [unfold_full] (X : Type) : seq_diagram (λn, X → A n) :=
    λn g x, f (g x)

    -- inductive finset : ℕ → Type :=
    -- | fin : forall n, finset n → finset (succ n)
    -- | ftop : forall n, finset (succ n)

    definition seq_diagram_fin : seq_diagram fin :=
    λn, fin.lift_succ

    definition id0_seq (x y : A 0) : ℕ → Type :=
    λ k, rep0 f k x = rep0 f k y

    definition id0_seq_diagram (x y : A 0) : seq_diagram (id0_seq f x y) :=
    λ (k : ℕ) (p : rep0 f k x = rep0 f k y), ap (@f k) p

    definition id_seq (n : ℕ) (x y : A n) : ℕ → Type :=
    λ k, rep f k x = rep f k y

    definition id_seq_diagram (n : ℕ) (x y : A n) : seq_diagram (id_seq f n x y) :=
    λ (k : ℕ) (p : rep f k x = rep f k y), ap (@f (n + k)) p

  end constructions

  section over

    variable {A}
    variable (P : Π⦃n⦄, A n → Type)

    definition seq_diagram_over : Type := Π⦃n⦄ {a : A n}, P a → P (f a)

    variable (g : seq_diagram_over f P)
    variables {f P}

    definition seq_diagram_of_over [unfold_full] {n : ℕ} (a : A n) :
      seq_diagram (λk, P (rep f k a)) :=
    λk p, g p

    definition seq_diagram_sigma [unfold 6] : seq_diagram (λn, Σ(x : A n), P x) :=
    λn v, ⟨f v.1, g v.2⟩

    variables {n : ℕ} (f P)

    theorem rep_f_equiv [constructor] (a : A n) (k : ℕ) :
      P (rep f k (f a)) ≃ P (rep f (succ k) a) :=
    equiv_apd011 P (rep_f f k a)

    theorem rep_rep_equiv [constructor] (a : A n) (k l : ℕ) :
      P (rep f (l + k) a) ≃ P (rep f k (rep f l a)) :=
    (equiv_apd011 P (rep_rep f k l a))⁻¹ᵉ

  end over

  omit f
  -- do we need to generalize this to the case where the bottom sequence consists of equivalences?
  definition seq_diagram_pi {X : Type} {A : X → ℕ → Type} (g : Π⦃x n⦄, A x n → A x (succ n)) :
    seq_diagram (λn, Πx, A x n) :=
  λn f x, g (f x)

  abbreviation ι  [constructor] := @inclusion
  abbreviation ι' [constructor] [parsing_only] {A} (f n) := @inclusion A f n

  definition rep0_glue (k : ℕ) (a : A 0) : ι f (rep0 f k a) = ι f a :=
  begin
    induction k with k IH,
    { reflexivity},
    { exact glue f (rep0 f k a) ⬝ IH}
  end

  definition shift_up [unfold 3] (x : seq_colim f) : seq_colim (shift_diag f) :=
  begin
    induction x,
    { exact ι _ (f a)},
    { exact glue _ (f a)}
  end

  definition shift_down [unfold 3] (x : seq_colim (shift_diag f)) : seq_colim f :=
  begin
    induction x,
    { exact ι f a},
    { exact glue f a}
  end

  definition shift_equiv [constructor] : seq_colim f ≃ seq_colim (shift_diag f) :=
  equiv.MK (shift_up f)
           (shift_down f)
           abstract begin
             intro x, induction x,
             { esimp, exact glue _ a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_up f) (shift_down f), ↑shift_down,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end
           abstract begin
             intro x, induction x,
             { exact glue _ a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_down f) (shift_up f), ↑shift_up,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end

  definition pshift_equiv [constructor] {A : ℕ → Type*} (f : Πn, A n →* A (succ n)) :
    pseq_colim f ≃* pseq_colim (λn, f (n+1)) :=
  begin
    fapply pequiv_of_equiv,
    { apply shift_equiv },
    { exact ap (ι _) !respect_pt }
  end

  section functor
  variable {f}
  variables {A' : ℕ → Type} {f' : seq_diagram A'}
  variables (g : Π⦃n⦄, A n → A' n) (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a))
  include p

  definition seq_colim_functor [unfold 7] : seq_colim f → seq_colim f' :=
  begin
    intro x, induction x with n a n a,
    { exact ι f' (g a)},
    { exact ap (ι f') (p a) ⬝ glue f' (g a)}
  end

  theorem seq_colim_functor_glue {n : ℕ} (a : A n)
    : ap (seq_colim_functor g p) (glue f a) = ap (ι f') (p a) ⬝ glue f' (g a) :=
  !elim_glue

  omit p

  definition is_equiv_seq_colim_functor [constructor] [H : Πn, is_equiv (@g n)]
     : is_equiv (seq_colim_functor @g p) :=
  adjointify _ (seq_colim_functor (λn, (@g _)⁻¹) (λn a, inv_commute' g f f' p a))
             abstract begin
               intro x, induction x,
               { esimp, exact ap (ι _) (right_inv (@g _) a)},
               { apply eq_pathover,
                 rewrite [ap_id, ap_compose (seq_colim_functor g p) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a, ap_con, ▸*,
                   seq_colim_functor_glue _ _ ((@g _)⁻¹ a), -ap_compose, ↑[function.compose],
                   ap_compose (ι _) (@g _),ap_inv_commute',+ap_con, con.assoc,
                   +ap_inv, inv_con_cancel_left, con.assoc, -ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apd}
             end end
             abstract begin
               intro x, induction x,
               { esimp, exact ap (ι _) (left_inv (@g _) a)},
               { apply eq_pathover,
                 rewrite [ap_id, ap_compose (seq_colim_functor _ _) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a, ap_con,▸*, seq_colim_functor_glue _ _ (g a),
                   -ap_compose, ↑[function.compose], ap_compose (ι f) (@g _)⁻¹, inv_commute'_fn,
                   +ap_con, con.assoc, con.assoc, +ap_inv, con_inv_cancel_left, -ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apd}
             end end

  definition seq_colim_equiv [constructor] (g : Π{n}, A n ≃ A' n)
    (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a)) : seq_colim f ≃ seq_colim f' :=
  equiv.mk _ (is_equiv_seq_colim_functor @g p)

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

  definition pseq_colim_pequiv [constructor] {A A' : ℕ → Type*} {f : Π{n}, A n →* A (n+1)}
    {f' : Π{n}, A' n →* A' (n+1)} (g : Π{n}, A n ≃* A' n)
    (p : Π⦃n⦄, g ∘* f ~ f' ∘* g) : pseq_colim @f ≃* pseq_colim @f' :=
  pequiv_of_equiv (seq_colim_equiv @g p) (ap (ι _) (respect_pt g))

  definition seq_colim_equiv_constant [constructor] {A : ℕ → Type*} {f f' : Π⦃n⦄, A n → A (n+1)}
    (p : Π⦃n⦄ (a : A n), f a = f' a) : seq_colim f ≃ seq_colim f' :=
  seq_colim_equiv (λn, erfl) p

  definition pseq_colim_equiv_constant [constructor] {A : ℕ → Type*} {f f' : Π{n}, A n →* A (n+1)}
    (p : Π⦃n⦄, f ~ f') : pseq_colim @f ≃* pseq_colim @f' :=
  pseq_colim_pequiv (λn, pequiv.rfl) p

  definition pseq_colim.elim [constructor] {A : ℕ → Type*} {B : Type*} {f : Π{n}, A n →* A (n+1)}
    (g : Πn, A n →* B) (p : Πn, g (n+1) ∘* f ~ g n) : pseq_colim @f →* B :=
  begin
    fapply pmap.mk,
    { intro x, induction x with n a n a,
      { exact g n a },
      { exact p n a }},
    { esimp, apply respect_pt }
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
