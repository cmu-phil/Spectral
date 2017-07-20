import algebra.group_theory ..pointed ..homotopy.smash

open eq pointed algebra group eq equiv is_trunc is_conn prod prod.ops
     smash susp unit pushout trunc prod

section
  variables {A B C : Type*}

  definition prod.pair_pmap (f : C →* A) (g : C →* B)
    : C →* A ×* B :=
  pmap.mk (λ c, (f c, g c)) (pair_eq (respect_pt f) (respect_pt g))

  -- ×* is the product in Type*
  definition pmap_prod_equiv : (C →* A ×* B) ≃ (C →* A) × (C →* B) :=
  begin
    apply equiv.MK (λ f, (ppr1 ∘* f, ppr2 ∘* f))
                   (λ w, prod.elim w prod.pair_pmap),
    { intro p, induction p with f g, apply pair_eq,
      { fapply pmap_eq,
        { intro x, reflexivity },
        { apply trans (prod_eq_pr1 (respect_pt f) (respect_pt g)),
          apply inverse, apply idp_con } },
      { fapply pmap_eq,
        { intro x, reflexivity },
        { apply trans (prod_eq_pr2 (respect_pt f) (respect_pt g)),
          apply inverse, apply idp_con } } },
    { intro f, fapply pmap_eq,
      { intro x, apply prod.eta },
      { exact prod.pair_eq_eta (respect_pt f) } }
  end

  -- since ~* is the identity type of pointed maps,
  -- the following follows by univalence, but we give a direct proof
  -- if we really have to, we could prove the uncurried version
  -- is an equivalence, but it's a pain without eta for products
  definition pair_phomotopy {f g : C →* A ×* B}
    (h : ppr1 ∘* f ~* ppr1 ∘* g) (k : ppr2 ∘* f ~* ppr2 ∘* g)
    : f ~* g :=
  phomotopy.mk (λ x, prod_eq (h x) (k x))
  begin
    apply prod.prod_eq_assemble,
    { esimp, rewrite [prod.eq_pr1_concat,prod_eq_pr1],
      exact to_homotopy_pt h },
    { esimp, rewrite [prod.eq_pr2_concat,prod_eq_pr2],
      exact to_homotopy_pt k }
  end

end

-- should be in wedge
definition or_of_wedge {A B : Type*} (w : wedge A B)
  : trunc.or (Σ a, w = inl a) (Σ b, w = inr b) :=
begin
  induction w with a b,
  { exact trunc.tr (sum.inl (sigma.mk a idp)) },
  { exact trunc.tr (sum.inr (sigma.mk b idp)) },
  { apply is_prop.elimo }
end

namespace group -- is this the correct namespace?

-- TODO: modify h_space to match

-- TODO: move these to appropriate places
definition pdiag (A : Type*) : A →* (A ×* A) :=
pmap.mk (λ a, (a, a)) idp

section prod
  variables (A B : Type*)

  definition wpr1 (A B : Type*) : (A ∨ B) →* A :=
  pmap.mk (wedge.elim (pid A) (pconst B A) idp) idp

  definition wpr2 (A B : Type*) : (A ∨ B) →* B :=
  pmap.mk (wedge.elim (pconst A B) (pid B) idp) idp

  definition ppr1_pprod_of_wedge (A B : Type*)
    : ppr1 ∘* pprod_of_wedge A B ~* wpr1 A B :=
  begin
    fconstructor,
    { intro w, induction w with a b,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        apply trans (ap_compose ppr1 (pprod_of_wedge A B) (pushout.glue star)),
        krewrite pushout.elim_glue, krewrite pushout.elim_glue } },
    { reflexivity }
  end

  definition ppr2_pprod_of_wedge (A B : Type*)
    : ppr2 ∘* pprod_of_wedge A B ~* wpr2 A B :=
  begin
    fconstructor,
    { intro w, induction w with a b,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        apply trans (ap_compose ppr2 (pprod_of_wedge A B) (pushout.glue star)),
        krewrite pushout.elim_glue, krewrite pushout.elim_glue } },
    { reflexivity }
  end

end prod
structure co_h_space [class] (A : Type*) :=
(comul : A →* (A ∨ A))
(colaw : pprod_of_wedge A A ∘* comul ~* pdiag A)

open co_h_space

definition co_h_space_of_counit_laws {A : Type*}
  (c : A →* (A ∨ A))
  (l : wpr1 A A ∘* c ~* pid A) (r : wpr2 A A ∘* c ~* pid A)
  : co_h_space A :=
co_h_space.mk c (pair_phomotopy
  (calc
    ppr1 ∘* pprod_of_wedge A A ∘* c
        ~* (ppr1 ∘* pprod_of_wedge A A) ∘* c
        : (passoc ppr1 (pprod_of_wedge A A) c)⁻¹*
    ... ~* wpr1 A A ∘* c
        : pwhisker_right c (ppr1_pprod_of_wedge A A)
    ... ~* pid A : l)
  (calc
    ppr2 ∘* pprod_of_wedge A A ∘* c
        ~* (ppr2 ∘* pprod_of_wedge A A) ∘* c
        : (passoc ppr2 (pprod_of_wedge A A) c)⁻¹*
    ... ~* wpr2 A A ∘* c
        : pwhisker_right c (ppr2_pprod_of_wedge A A)
    ... ~* pid A : r))

section
  variables (A : Type*) [H : co_h_space A]
  include H

  definition counit_left : wpr1 A A ∘* comul A ~* pid A :=
  calc
    wpr1 A A ∘* comul A
        ~* (ppr1 ∘* (pprod_of_wedge A A)) ∘* comul A
        : (pwhisker_right (comul A) (ppr1_pprod_of_wedge A A))⁻¹*
    ... ~* ppr1 ∘* ((pprod_of_wedge A A) ∘* comul A)
        : passoc ppr1 (pprod_of_wedge A A) (comul A)
    ... ~* pid A
        : pwhisker_left ppr1 (colaw A)

  definition counit_right : wpr2 A A ∘* comul A ~* pid A :=
  calc
    wpr2 A A ∘* comul A
        ~* (ppr2 ∘* (pprod_of_wedge A A)) ∘* comul A
        : (pwhisker_right (comul A) (ppr2_pprod_of_wedge A A))⁻¹*
    ... ~* ppr2 ∘* ((pprod_of_wedge A A) ∘* comul A)
        : passoc ppr2 (pprod_of_wedge A A) (comul A)
    ... ~* pid A
        : pwhisker_left ppr2 (colaw A)

  definition is_conn_co_h_space : is_conn 0 A :=
  begin
    apply is_contr.mk (trunc.tr pt), intro ta,
    induction ta with a,
    have t : trunc -1 ((Σ b, comul A a = inl b) ⊎ (Σ c, comul A a = inr c)),
    from (or_of_wedge (comul A a)),
    induction t with s, induction s with bp cp,
    { induction bp with b p, apply ap trunc.tr,
      exact (ap (wpr2 A A) p)⁻¹ ⬝ (counit_right A a) },
    { induction cp with c p, apply ap trunc.tr,
      exact (ap (wpr1 A A) p)⁻¹ ⬝ (counit_left A a) }
  end

end

section
  variable (A : Type*)

  definition pinch : ⅀ A →* wedge (⅀ A) (⅀ A) :=
  begin
    fapply pmap.mk,
    { intro sa, induction sa with a,
      { exact inl north }, { exact inr south },
      { exact ap inl (glue a ⬝ (glue pt)⁻¹) ⬝ glue star ⬝ ap inr (glue a) } },
    { reflexivity }
  end

  definition co_h_space_susp : co_h_space (⅀ A) :=
  co_h_space_of_counit_laws (pinch A)
  begin
    fapply phomotopy.mk,
    { intro sa, induction sa with a,
      { reflexivity },
      { exact glue pt },
      { apply eq_pathover,
        krewrite [ap_id,ap_compose' (wpr1 (⅀ A) (⅀ A)) (pinch A)],
        krewrite elim_merid, rewrite ap_con,
        krewrite [pushout.elim_inr,ap_constant],
        rewrite ap_con, krewrite [pushout.elim_inl,pushout.elim_glue,ap_id],
        apply square_of_eq, apply trans !idp_con, apply inverse,
        apply trans (con.assoc (merid a) (glue pt)⁻¹ (glue pt)),
        exact whisker_left (merid a) (con.left_inv (glue pt)) } },
    { reflexivity }
  end
  begin
    fapply phomotopy.mk,
    { intro sa, induction sa with a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover,
        krewrite [ap_id,ap_compose' (wpr2 (⅀ A) (⅀ A)) (pinch A)],
        krewrite elim_merid, rewrite ap_con,
        krewrite [pushout.elim_inr,ap_id],
        rewrite ap_con, krewrite [pushout.elim_inl,pushout.elim_glue,ap_constant],
        apply square_of_eq, apply trans !idp_con, apply inverse,
        exact idp_con (merid a) } },
    { reflexivity }
  end

end
/-
  terminology: magma, comagma? co_h_space/co_h_space?
  pre_inf_group? pre_inf_cogroup? ghs (for group-like H-space?)
  cgcohs (cogroup-like co-H-space?) cogroup_like_co_h_space?
-/

end group
