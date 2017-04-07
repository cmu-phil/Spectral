-- authors: Floris van Doorn, Egbert Rijke

import hit.colimit types.fin homotopy.chain_complex .move_to_lib
open seq_colim pointed algebra eq is_trunc nat is_equiv equiv sigma sigma.ops chain_complex

namespace seq_colim

  definition pseq_colim [constructor] {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) : Type* :=
  pointed.MK (seq_colim f) (@sι _ _ 0 pt)

  definition inclusion_pt [constructor] {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) (n : ℕ)
    : inclusion f (Point (X n)) = Point (pseq_colim f) :=
  begin
    induction n with n p,
      reflexivity,
      exact (ap (sι f) (respect_pt _))⁻¹ᵖ ⬝ !glue ⬝ p
  end

  definition pinclusion [constructor] {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) (n : ℕ)
    : X n →* pseq_colim f :=
  pmap.mk (inclusion f) (inclusion_pt f n)

  definition seq_diagram [reducible] (A : ℕ → Type) : Type := Π⦃n⦄, A n → A (succ n)
  definition pseq_diagram [reducible] (A : ℕ → Type*) : Type := Π⦃n⦄, A n →* A (succ n)

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

  namespace ops
  abbreviation ι  [constructor] := @inclusion
  abbreviation pι  [constructor] {A} (f) {n} := @pinclusion A f n
  abbreviation pι'  [constructor] [parsing_only] := @pinclusion
  abbreviation ι' [constructor] [parsing_only] {A} (f n) := @inclusion A f n
  end ops
  open seq_colim.ops

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

  definition prep0 [constructor] {A : ℕ → Type*} (f : pseq_diagram A) (k : ℕ) : A 0 →* A k :=
  pmap.mk (rep0 (λn x, f x) k)
          begin induction k with k p, reflexivity, exact ap (@f k) p ⬝ !respect_pt end

  definition respect_pt_prep0_succ {A : ℕ → Type*} (f : pseq_diagram A) (k : ℕ)
    : respect_pt (prep0 f (succ k)) = ap (@f k) (respect_pt (prep0 f k)) ⬝ respect_pt (@f k) :=
  by reflexivity

  theorem prep0_succ_lemma {A : ℕ → Type*} (f : pseq_diagram A) (n : ℕ)
    (p : rep0 (λn x, f x) n pt = rep0 (λn x, f x) n pt)
    (q : prep0 f n (Point (A 0)) = Point (A n))
    : loop_equiv_eq_closed (ap (@f n) q ⬝ respect_pt (@f n))
    (ap (@f n) p) = Ω→(@f n) (loop_equiv_eq_closed q p) :=
  by rewrite [▸*, con_inv, ↑ap1_gen, +ap_con, ap_inv, +con.assoc]

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

  section
  parameters {X : ℕ → Type} (g : seq_diagram X) (x : X 0)

  definition rep_eq_diag ⦃n : ℕ⦄ (y : X n) : seq_diagram (λk, rep g k (rep0 g n x) = rep g k y) :=
  proof λk, ap (@g (n + k)) qed

  definition code_incl ⦃n : ℕ⦄ (y : X n) : Type :=
  seq_colim (rep_eq_diag y)

  definition code [unfold 4] : seq_colim g → Type :=
  seq_colim.elim_type g code_incl
  begin
    intro n y,
    refine _ ⬝e !shift_equiv⁻¹ᵉ,
    fapply seq_colim_equiv,
    { intro k, exact code_glue_equiv g k (rep0 g n x) y },
    { intro k p, exact code_glue_equiv_ap g p }
  end

  definition encode [unfold 5] (y : seq_colim g) (p : ι g x = y) : code y :=
  transport code p (ι' _ 0 idp)

  definition decode [unfold 4] (y : seq_colim g) (c : code y) : ι g x = y :=
  begin
    induction y,
    { esimp at c, exact sorry },
    { exact sorry }
  end

  definition decode_encode (y : seq_colim g) (p : ι g x = y) : decode y (encode y p) = p :=
  sorry

  definition encode_decode (y : seq_colim g) (c : code y) : encode y (decode y c) = c :=
  sorry

  definition seq_colim_eq_equiv_code [constructor] (y : seq_colim g) : (ι g x = y) ≃ code y :=
  equiv.MK (encode y) (decode y) (encode_decode y) (decode_encode y)

  definition seq_colim_eq {n : ℕ} (y : X n) : (ι g x = ι g y) ≃ seq_colim (rep_eq_diag y) :=
  proof seq_colim_eq_equiv_code (ι g y) qed

  end

  definition rep0_eq_diag {X : ℕ → Type} (f : seq_diagram X) (x y : X 0)
    : seq_diagram (λk, rep0 f k x = rep0 f k y) :=
  proof λk, ap (@f (k)) qed

  definition seq_colim_eq0 {X : ℕ → Type} (f : seq_diagram X) (x y : X 0) :
    (ι f x = ι f y) ≃ seq_colim (rep0_eq_diag f x y)  :=
  begin
    refine !seq_colim_eq ⬝e _,
    fapply seq_colim_equiv,
    { intro n, exact sorry},
    { intro n p, exact sorry }
  end


  definition pseq_colim_loop {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) :
    Ω (pseq_colim f) ≃* pseq_colim (λn, Ω→(f n)) :=
  begin
    fapply pequiv_of_equiv,
    { refine !seq_colim_eq0 ⬝e _,
      fapply seq_colim_equiv,
      { intro n, exact loop_equiv_eq_closed (respect_pt (prep0 f n)) },
      { intro n p, apply prep0_succ_lemma }},
    { exact sorry }
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
