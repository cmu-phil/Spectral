
import algebra.group_theory ..move_to_lib eq2
open pi pointed algebra group eq equiv is_trunc trunc

namespace group

  -- definition pmap_mul [constructor] {A B : Type*} [inf_pgroup B] (f g : A →* B) : A →* B :=
  -- pmap.mk (λa, f a * g a) (ap011 mul (respect_pt f) (respect_pt g) ⬝ !one_mul)

  -- definition pmap_inv [constructor] {A B : Type*} [inf_pgroup B] (f : A →* B) : A →* B :=
  -- pmap.mk (λa, (f a)⁻¹) (ap inv (respect_pt f) ⬝ !one_inv)

  definition pmap_mul [constructor] {A B : Type*} (f g : A →* Ω B) : A →* Ω B :=
  pmap.mk (λa, f a ⬝ g a) (respect_pt f ◾ respect_pt g ⬝ !idp_con)

  definition pmap_inv [constructor] {A B : Type*} (f : A →* Ω B) : A →* Ω B :=
  pmap.mk (λa, (f a)⁻¹ᵖ) (respect_pt f)⁻²

  definition inf_group_pmap [constructor] [instance] (A B : Type*) : inf_group (A →* Ω B) :=
  begin
    fapply inf_group.mk,
    { exact pmap_mul },
    { intro f g h, fapply pmap_eq,
      { intro a, exact con.assoc (f a) (g a) (h a) },
      { rexact eq_of_square (con2_assoc (respect_pt f) (respect_pt g) (respect_pt h)) }},
    { apply pconst },
    { intros f, fapply pmap_eq,
      { intro a, exact one_mul (f a) },
      { esimp, apply eq_of_square, refine _ ⬝vp !ap_id, apply natural_square_tr }},
    { intros f, fapply pmap_eq,
      { intro a, exact mul_one (f a) },
      { reflexivity }},
    { exact pmap_inv },
    { intro f, fapply pmap_eq,
      { intro a, exact con.left_inv (f a) },
      { exact !con_left_inv_idp⁻¹ }},
  end

  definition group_trunc_pmap [constructor] [instance] (A B : Type*) : group (trunc 0 (A →* Ω B)) :=
  !trunc_group

  definition Group_trunc_pmap [reducible] [constructor] (A B : Type*) : Group :=
  Group.mk (trunc 0 (A →* Ω (Ω B))) _

  definition Group_trunc_pmap_homomorphism [constructor] {A A' B : Type*} (f : A' →* A) :
    Group_trunc_pmap A B →g Group_trunc_pmap A' B :=
  begin
    fapply homomorphism.mk,
    { apply trunc_functor, intro g, exact g ∘* f},
    { intro g h, induction g with g, induction h with h, apply ap tr,
      fapply pmap_eq,
      { intro a, reflexivity },
      { refine _ ⬝ !idp_con⁻¹,
        refine whisker_right _ !ap_con_fn ⬝ _, apply con2_con_con2 }}
  end

  definition Group_trunc_pmap_pid [constructor] {A B : Type*} (f : Group_trunc_pmap A B) :
    Group_trunc_pmap_homomorphism (pid A) f = f :=
  begin
    induction f with f, apply ap tr, apply eq_of_phomotopy, apply pcompose_pid
  end

  definition Group_trunc_pmap_pconst [constructor] {A A' B : Type*} (f : Group_trunc_pmap A B) :
    Group_trunc_pmap_homomorphism (pconst A' A) f = 1 :=
  begin
    induction f with f, apply ap tr, apply eq_of_phomotopy, apply pcompose_pconst
  end

  definition Group_trunc_pmap_pcompose [constructor] {A A' A'' B : Type*} (f : A' →* A) (f' : A'' →* A')
    (g : Group_trunc_pmap A B) : Group_trunc_pmap_homomorphism (f ∘* f') g =
    Group_trunc_pmap_homomorphism f' (Group_trunc_pmap_homomorphism f g) :=
  begin
    induction g with g, apply ap tr, apply eq_of_phomotopy, exact !passoc⁻¹*
  end

  definition Group_trunc_pmap_phomotopy [constructor] {A A' B : Type*} {f f' : A' →* A} (p : f ~* f') :
    @Group_trunc_pmap_homomorphism _ _ B f ~ Group_trunc_pmap_homomorphism f' :=
  begin
    intro f, induction f, exact ap tr (eq_of_phomotopy (pwhisker_left a p))
  end

  definition ab_inf_group_pmap [constructor] [instance] (A B : Type*) : ab_inf_group (A →* Ω (Ω B)) :=
  ⦃ab_inf_group, inf_group_pmap A (Ω B), mul_comm :=
    begin
      intro f g, fapply pmap_eq,
      { intro a, exact eckmann_hilton (f a) (g a) },
      { rexact eq_of_square (eckmann_hilton_con2 (respect_pt f) (respect_pt g)) }
    end⦄

  definition ab_group_trunc_pmap [constructor] [instance] (A B : Type*) :
    ab_group (trunc 0 (A →* Ω (Ω B))) :=
  !trunc_ab_group

  definition AbGroup_trunc_pmap [reducible] [constructor] (A B : Type*) : AbGroup :=
  AbGroup.mk (trunc 0 (A →* Ω (Ω B))) _

  /- Group of functions whose codomain is a group -/
  definition group_pi [instance] [constructor] {A : Type} (P : A → Type) [Πa, group (P a)] : group (Πa, P a) :=
  begin
    fapply group.mk,
    { apply is_trunc_pi },
    { intro f g a, exact f a * g a },
    { intros, apply eq_of_homotopy, intro a, apply mul.assoc },
    { intro a, exact 1 },
    { intros, apply eq_of_homotopy, intro a, apply one_mul },
    { intros, apply eq_of_homotopy, intro a, apply mul_one },
    { intro f a, exact (f a)⁻¹ },
    { intros, apply eq_of_homotopy, intro a, apply mul.left_inv }
  end

  definition Group_pi [constructor] {A : Type} (P : A → Group) : Group :=
  Group.mk (Πa, P a) _

  /- we use superscript in the following notation, because otherwise we can never write something
     like `Πg h : G, _` anymore -/

  notation `Πᵍ` binders `, ` r:(scoped P, Group_pi P) := r

  definition Group_pi_intro [constructor] {A : Type} {G : Group} {P : A → Group} (f : Πa, G →g P a)
    : G →g Πᵍ a, P a :=
  begin
    fconstructor,
    { intro g a, exact f a g },
    { intro g h, apply eq_of_homotopy, intro a, exact respect_mul (f a) g h }
  end

  -- definition AbGroup_trunc_pmap_homomorphism [constructor] {A A' B : Type*} (f : A' →* A) :
  --   AbGroup_trunc_pmap A B →g AbGroup_trunc_pmap A' B :=
  -- Group_trunc_pmap_homomorphism f


  /- Group of functions whose codomain is a group -/
  -- definition group_arrow [instance] (A B : Type) [group B] : group (A → B) :=
  -- begin
  --   fapply group.mk,
  --   { apply is_trunc_arrow },
  --   { intro f g a, exact f a * g a },
  --   { intros, apply eq_of_homotopy, intro a, apply mul.assoc },
  --   { intro a, exact 1 },
  --   { intros, apply eq_of_homotopy, intro a, apply one_mul },
  --   { intros, apply eq_of_homotopy, intro a, apply mul_one },
  --   { intro f a, exact (f a)⁻¹ },
  --   { intros, apply eq_of_homotopy, intro a, apply mul.left_inv }
  -- end

  -- definition Group_arrow (A : Type) (G : Group) : Group :=
  -- Group.mk (A → G) _

  -- definition ab_group_arrow [instance] (A B : Type) [ab_group B] : ab_group (A → B) :=
  -- ⦃ab_group, group_arrow A B,
  --    mul_comm := by intros; apply eq_of_homotopy; intro a; apply mul.comm⦄

  -- definition AbGroup_arrow (A : Type) (G : AbGroup) : AbGroup :=
  -- AbGroup.mk (A → G) _

  -- definition pgroup_ppmap [instance] (A B : Type*) [pgroup B] : pgroup (ppmap A B) :=
  -- begin
  --   fapply pgroup.mk,
  --   { apply is_trunc_pmap },
  --   { intro f g, apply pmap.mk (λa, f a * g a),
  --     exact ap011 mul (respect_pt f) (respect_pt g) ⬝ !one_mul },
  --   { intros, apply pmap_eq_of_homotopy, intro a, apply mul.assoc },
  --   { intro f, apply pmap.mk (λa, (f a)⁻¹), apply inv_eq_one, apply respect_pt },
  --   { intros, apply pmap_eq_of_homotopy, intro a, apply one_mul },
  --   { intros, apply pmap_eq_of_homotopy, intro a, apply mul_one },
  --   { intros, apply pmap_eq_of_homotopy, intro a, apply mul.left_inv }
  -- end

  -- definition Group_pmap (A : Type*) (G : Group) : Group :=
  -- Group_of_pgroup (ppmap A (pType_of_Group G))

  -- definition AbGroup_pmap (A : Type*) (G : AbGroup) : AbGroup :=
  -- AbGroup.mk (A →* pType_of_Group G)
  -- ⦃ ab_group, Group.struct (Group_pmap A G),
  --   mul_comm := by intro f g; apply pmap_eq_of_homotopy; intro a; apply mul.comm ⦄

  -- definition Group_pmap_homomorphism [constructor] {A A' : Type*} (f : A' →* A) (G : AbGroup) :
  --   Group_pmap A G →g Group_pmap A' G :=
  -- begin
  --   fapply homomorphism.mk,
  --   { intro g, exact g ∘* f},
  --   { intro g h, apply pmap_eq_of_homotopy, intro a, reflexivity }
  -- end

end group
