import homotopy.torus

open eq circle prod prod.ops function

namespace torus

  definition S1xS1_of_torus [unfold 1] (x : T²) : S¹ × S¹ :=
  begin
    induction x,
    { exact (circle.base, circle.base) },
    { exact prod_eq loop idp },
    { exact prod_eq idp loop },
    { apply square_of_eq,
      exact !prod_eq_concat ⬝ ap011 prod_eq !idp_con⁻¹ !idp_con ⬝ !prod_eq_concat⁻¹ }
  end

  definition torus_of_S1xS1 [unfold 1] (x : S¹ × S¹) : T² :=
  begin
    induction x with x y, induction x,
    { induction y,
      { exact base },
      { exact loop2 }},
    { induction y,
      { exact loop1 },
      { apply eq_pathover, refine !elim_loop ⬝ph surf ⬝hp !elim_loop⁻¹ }}
  end

  definition to_from_base_left [unfold 1] (y : S¹) :
    S1xS1_of_torus (torus_of_S1xS1 (circle.base, y)) = (circle.base, y) :=
  begin
    induction y,
    { reflexivity },
    { apply eq_pathover, apply hdeg_square,
      refine ap_compose S1xS1_of_torus _ _ ⬝ ap02 _ !elim_loop ⬝ _ ⬝ !ap_prod_mk_right⁻¹,
      apply elim_loop2 }
  end

  definition from_to_loop1
    : pathover (λa, torus_of_S1xS1 (S1xS1_of_torus a) = a) proof idp qed loop1 proof idp qed :=
  begin
    apply eq_pathover, apply hdeg_square,
    refine ap_compose torus_of_S1xS1 _ _ ⬝ ap02 _ !elim_loop1 ⬝ _ ⬝ !ap_id⁻¹,
    refine !ap_prod_elim ⬝ !idp_con ⬝ !elim_loop
  end

  definition from_to_loop2
    : pathover (λa, torus_of_S1xS1 (S1xS1_of_torus a) = a) proof idp qed loop2 proof idp qed :=
  begin
    apply eq_pathover, apply hdeg_square,
    refine ap_compose torus_of_S1xS1 _ _ ⬝ ap02 _ !elim_loop2 ⬝ _ ⬝ !ap_id⁻¹,
    refine !ap_prod_elim ⬝ !elim_loop
  end

  definition torus_equiv_S1xS1 : T² ≃ S¹ × S¹ :=
  begin
    fapply equiv.MK,
    { exact S1xS1_of_torus },
    { exact torus_of_S1xS1 },
    { intro x, induction x with x y, induction x,
      { exact to_from_base_left y },
      { apply eq_pathover,
        refine ap_compose (S1xS1_of_torus ∘ torus_of_S1xS1) _ _ ⬝ph _,
        refine ap02 _ !ap_prod_mk_left ⬝ph _ ⬝hp !ap_prod_mk_left⁻¹,
        refine !ap_compose ⬝ ap02 _ (!ap_prod_elim ⬝ !idp_con) ⬝ph _,
        refine ap02 _ !elim_loop ⬝ph _,
        induction y,
        { apply hdeg_square, apply elim_loop1 },
        { apply square_pathover, exact sorry }
        -- apply square_of_eq, induction y,
        -- { refine !idp_con ⬝ !elim_loop1⁻¹ },
        -- { apply eq_pathover_dep, }
        }},
    { intro x, induction x,
      { reflexivity },
      { exact from_to_loop1 },
      { exact from_to_loop2 },
      { exact sorry }}
  end

end torus
