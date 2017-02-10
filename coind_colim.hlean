-- author: Floris van Doorn

import .colim

open nat seq_colim seq_colim.ops eq equiv is_equiv is_trunc function

namespace seq_colim

  variables {A : ℕ → Type} {f : seq_diagram A}

  definition ι0  [reducible] : A 0 → seq_colim f :=
  ι f

  variable (f)
  definition ι0' [reducible] : A 0 → seq_colim f :=
  ι f

  definition glue0 (a : A 0) : shift_down f (ι0 (f a)) = ι f a :=
  glue f a

  definition rec_coind_point {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), seq_colim f → Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f (ι0 a))
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)),
      P (shift_diag f) x → P f (shift_down f x))
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0),
      pathover (P f) (Ps f (ι0 (f a)) !P0) (proof glue f a qed) (P0 f a))
     (n : ℕ) : Π{A : ℕ → Type} {f : seq_diagram A} (a : A n), P f (ι f a) :=
  begin
    induction n with n IH: intro A f a,
    { exact P0 f a },
    { exact Ps f (ι _ a) (IH a) }
  end

  definition rec_coind_point_succ {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), seq_colim f → Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f (ι0 a))
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)),
      P (shift_diag f) x → P f (shift_down f x))
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0),
      pathover (P f) (Ps f (ι0 (f a)) !P0) _ (P0 f a))
     (n : ℕ) {A : ℕ → Type} {f : seq_diagram A} (a : A (succ n)) :
    rec_coind_point P0 Ps Pe (succ n) a = Ps f (ι _ a) (rec_coind_point P0 Ps Pe n a) :=
  by reflexivity

  definition rec_coind {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), seq_colim f → Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f (ι0 a))
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)),
      P (shift_diag f) x → P f (shift_down f x))
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0),
      pathover (P f) (Ps f (ι0 (f a)) !P0) (proof glue f a qed) (P0 f a))
    {A : ℕ → Type} {f : seq_diagram A} (x : seq_colim f) : P f x :=
  begin
    induction x,
    { exact rec_coind_point P0 Ps Pe n a },
    { revert A f a, induction n with n IH: intro A f a,
      { exact Pe f a },
      { rewrite [rec_coind_point_succ _ _ _ n, rec_coind_point_succ],
        note p := IH _ (shift_diag f) a,
        refine change_path _ (pathover_ap _ _ (apo (Ps f) p)),
        exact !elim_glue
        }},
  end

  definition rec_coind_pt2 {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), seq_colim f → Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f (ι0 a))
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)),
      P (shift_diag f) x → P f (shift_down f x))
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0),
      pathover (P f) (Ps f (ι0 (f a)) !P0) _ (P0 f a))
    {A : ℕ → Type} {f : seq_diagram A} (x : seq_colim (shift_diag f))
    : rec_coind P0 Ps Pe (shift_down f x) = Ps f x (rec_coind P0 Ps Pe x) :=
  begin
    induction x,
    { reflexivity },
    { apply eq_pathover_dep,
      apply hdeg_squareover, esimp,
      refine apd_compose2 (rec_coind P0 Ps Pe) _ _ ⬝ _ ⬝ (apd_compose1 (Ps f) _ _)⁻¹,
      exact sorry
      --refine ap (λx, pathover_of_pathover_ap _ _ (x)) _ ⬝ _ ,
      }
  end

  definition elim_coind_point {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f)
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) → P f)
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
    (n : ℕ) : Π{A : ℕ → Type} (f : seq_diagram A) (a : A n), P f :=
  begin
    induction n with n IH: intro A f a,
    { exact P0 f a },
    { exact Ps f (ι _ a) (IH _ a) }
  end

  definition elim_coind_point_succ {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f)
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) → P f)
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
    (n : ℕ) {A : ℕ → Type} {f : seq_diagram A} (a : A (succ n)) :
      elim_coind_point P0 Ps Pe (succ n) f a =
      Ps f (ι _ a) (elim_coind_point P0 Ps Pe n (shift_diag f) a) :=
  by reflexivity

  definition elim_coind_path {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f)
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) → P f)
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
    (n : ℕ) : Π{A : ℕ → Type} (f : seq_diagram A) (a : A n),
    elim_coind_point P0 Ps Pe (succ n) f (f a) = elim_coind_point P0 Ps Pe n f a :=
  begin
    induction n with n IH: intro A f a,
    { exact Pe f a },
    { rewrite [elim_coind_point_succ _ _ _ n, elim_coind_point_succ],
      note p := IH (shift_diag f) a,
      refine ap011 (Ps f) !glue p }
  end

  definition elim_coind {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f)
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) → P f)
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
    {A : ℕ → Type} {f : seq_diagram A} (x : seq_colim f) : P f :=
  begin
    induction x,
    { exact elim_coind_point P0 Ps Pe n f a },
    { exact elim_coind_path P0 Ps Pe n f a },
  end

  definition elim_coind_pt2 {P : Π⦃A : ℕ → Type⦄ (f : seq_diagram A), Type}
    (P0 : Π⦃A⦄ (f : seq_diagram A) (a : A 0), P f)
    (Ps : Π⦃A⦄ (f : seq_diagram A) (x : seq_colim (shift_diag f)), P (shift_diag f) → P f)
    (Pe : Π⦃A⦄ (f : seq_diagram A) (a : A 0), Ps f (ι0 (f a)) (P0 _ (f a)) = P0 f a)
    {A : ℕ → Type} {f : seq_diagram A} (x : seq_colim (shift_diag f))
    : elim_coind P0 Ps Pe (shift_down f x) = Ps f x (elim_coind P0 Ps Pe x) :=
  begin
    induction x,
    { reflexivity },
    { apply eq_pathover, apply hdeg_square,
      refine ap_compose (elim_coind P0 Ps Pe) _ _ ⬝ _ ⬝ (ap_eq_ap011 (Ps f) _ _ _)⁻¹,
      refine ap02 _ !elim_glue ⬝ !elim_glue ⬝ ap011 (ap011 _) !ap_id⁻¹ !elim_glue⁻¹ }
  end

end seq_colim
