/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import hit.set_quotient .subgroup ..move_to_lib types.equiv

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod trunc function equiv is_equiv

namespace group

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {N' : normal_subgroup_rel G'}
  variables {A B : AbGroup}

  /- Quotient Group -/

  definition homotopy_of_homomorphism_eq {f g : G →g G'}(p : f = g) : f ~ g :=
  λx : G , ap010 group_fun p x

  definition quotient_rel [constructor] (g h : G) : Prop := N (g * h⁻¹)

  variable {N}

    -- We prove that quotient_rel is an equivalence relation
  theorem quotient_rel_refl (g : G) : quotient_rel N g g :=
  transport (λx, N x) !mul.right_inv⁻¹ (subgroup_has_one N)

  theorem quotient_rel_symm (r : quotient_rel N g h) : quotient_rel N h g :=
  transport (λx, N x) (!mul_inv ⬝ ap (λx, x * _) !inv_inv) (subgroup_respect_inv N r)

  theorem quotient_rel_trans (r : quotient_rel N g h) (s : quotient_rel N h k)
    : quotient_rel N g k :=
  have H1 : N ((g * h⁻¹) * (h * k⁻¹)), from subgroup_respect_mul N r s,
  have H2 : (g * h⁻¹) * (h * k⁻¹) = g * k⁻¹, from calc
    (g * h⁻¹) * (h * k⁻¹) = ((g * h⁻¹) * h) * k⁻¹ : by rewrite [mul.assoc (g * h⁻¹)]
                      ... = g * k⁻¹               : by rewrite inv_mul_cancel_right,
  show N (g * k⁻¹), by rewrite [-H2]; exact H1

  theorem is_equivalence_quotient_rel : is_equivalence (quotient_rel N) :=
  is_equivalence.mk quotient_rel_refl
                    (λg h, quotient_rel_symm)
                    (λg h k, quotient_rel_trans)

    -- We prove that quotient_rel respects inverses and multiplication, so
    -- it is a congruence relation
  theorem quotient_rel_resp_inv (r : quotient_rel N g h) : quotient_rel N g⁻¹ h⁻¹ :=
  have H1 : N (g⁻¹ * (h * g⁻¹) * g), from
    is_normal_subgroup' N g (quotient_rel_symm r),
  have H2 : g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h⁻¹⁻¹, from calc
    g⁻¹ * (h * g⁻¹) * g = g⁻¹ * h * g⁻¹ * g : by rewrite -mul.assoc
                    ... = g⁻¹ * h           : inv_mul_cancel_right
                    ... = g⁻¹ * h⁻¹⁻¹       : by rewrite algebra.inv_inv,
  show N (g⁻¹ * h⁻¹⁻¹), by rewrite [-H2]; exact H1

  theorem quotient_rel_resp_mul (r : quotient_rel N g h) (r' : quotient_rel N g' h')
    : quotient_rel N (g * g') (h * h') :=
  have H1 : N (g * ((g' * h'⁻¹) * h⁻¹)), from
    normal_subgroup_insert N r' r,
  have H2 : g * ((g' * h'⁻¹) * h⁻¹) = (g * g') * (h * h')⁻¹, from calc
    g * ((g' * h'⁻¹) * h⁻¹) = g * (g' * (h'⁻¹ * h⁻¹)) : by rewrite [mul.assoc]
                        ... = (g * g') * (h'⁻¹ * h⁻¹) : mul.assoc
                        ... = (g * g') * (h * h')⁻¹ : by rewrite [mul_inv],
  show N ((g * g') * (h * h')⁻¹), from transport (λx, N x) H2 H1

  local attribute is_equivalence_quotient_rel [instance]

  variable (N)

  definition qg : Type := set_quotient (quotient_rel N)

  variable {N}

  local attribute qg [reducible]

  definition quotient_one [constructor] : qg N := class_of one
  definition quotient_inv [unfold 3] : qg N → qg N :=
  quotient_unary_map has_inv.inv (λg g' r, quotient_rel_resp_inv r)
  definition quotient_mul [unfold 3 4] : qg N → qg N → qg N :=
  quotient_binary_map has_mul.mul (λg g' r h h' r', quotient_rel_resp_mul r r')

  section
  local notation 1 := quotient_one
  local postfix ⁻¹ := quotient_inv
  local infix * := quotient_mul

  theorem quotient_mul_assoc (g₁ g₂ g₃ : qg N) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    refine set_quotient.rec_prop _ g₁,
    refine set_quotient.rec_prop _ g₂,
    refine set_quotient.rec_prop _ g₃,
    clear g₁ g₂ g₃, intro g₁ g₂ g₃,
    exact ap class_of !mul.assoc
  end

  theorem quotient_one_mul (g : qg N) : 1 * g = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !one_mul
  end

  theorem quotient_mul_one (g : qg N) : g * 1 = g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !mul_one
  end

  theorem quotient_mul_left_inv (g : qg N) : g⁻¹ * g = 1 :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    exact ap class_of !mul.left_inv
  end

  theorem quotient_mul_comm {G : AbGroup} {N : normal_subgroup_rel G} (g h : qg N)
    : g * h = h * g :=
  begin
    refine set_quotient.rec_prop _ g, clear g, intro g,
    refine set_quotient.rec_prop _ h, clear h, intro h,
    apply ap class_of, esimp, apply mul.comm
  end

  end

  variable (N)
  definition group_qg [constructor] : group (qg N) :=
  group.mk _ quotient_mul quotient_mul_assoc quotient_one quotient_one_mul quotient_mul_one
           quotient_inv quotient_mul_left_inv

  definition quotient_group [constructor] : Group :=
  Group.mk _ (group_qg N)

  definition ab_group_qg [constructor] {G : AbGroup} (N : normal_subgroup_rel G)
    : ab_group (qg N) :=
  ⦃ab_group, group_qg N, mul_comm := quotient_mul_comm⦄

  definition quotient_ab_group [constructor] {G : AbGroup} (N : subgroup_rel G)
    : AbGroup :=
  AbGroup.mk _ (ab_group_qg (normal_subgroup_rel_ab N))

  definition qg_map [constructor] : G →g quotient_group N :=
  homomorphism.mk class_of (λ g h, idp)

  definition ab_qg_map {G : AbGroup} (N : subgroup_rel G) : G →g quotient_ab_group N :=
  begin
    fapply homomorphism.mk,
    exact class_of,
    exact λ g h, idp
  end

 definition is_surjective_ab_qg_map {A : AbGroup} (N : subgroup_rel A) : is_surjective (ab_qg_map N) :=
  begin
    intro x, induction x,
    fapply image.mk,
    exact a, reflexivity,
    apply is_prop.elimo
  end

  namespace quotient
    notation `⟦`:max a `⟧`:0 := qg_map _ a
  end quotient

  open quotient
  variable {N}

  definition qg_map_eq_one (g : G) (H : N g) : qg_map N g = 1 :=
  begin
    apply eq_of_rel,
      have e : (g * 1⁻¹ = g),
      from calc
      g * 1⁻¹ = g * 1 : one_inv
        ...   = g : mul_one,
    unfold quotient_rel, rewrite e, exact H
  end

  definition ab_qg_map_eq_one {K : subgroup_rel A} (g :A) (H : K g) : ab_qg_map K g = 1 :=
  begin
    apply eq_of_rel,
      have e : (g * 1⁻¹ = g),
      from calc
      g * 1⁻¹ = g * 1 : one_inv
        ...   = g : mul_one,
    unfold quotient_rel, xrewrite e, exact H
  end

   --- there should be a smarter way to do this!! Please have a look, Floris.
  definition rel_of_qg_map_eq_one (g : G) (H : qg_map N g = 1) : N g :=
  begin
    have e : (g * 1⁻¹ = g),
    from calc
      g * 1⁻¹ = g * 1 : one_inv
        ...   = g : mul_one,
    rewrite (inverse e),
    apply rel_of_eq _ H
  end

  definition rel_of_ab_qg_map_eq_one {K : subgroup_rel A} (a :A) (H : ab_qg_map K a = 1) : K a :=
  begin
    have e : (a * 1⁻¹ = a),
    from calc
      a * 1⁻¹ = a * 1 : one_inv
        ...   = a : mul_one,
    rewrite (inverse e),
    apply rel_of_eq _ H
  end

  definition quotient_group_elim_fun [unfold 6] (f : G →g G') (H : Π⦃g⦄, N g → f g = 1)
    (g : quotient_group N) : G' :=
  begin
    refine set_quotient.elim f _ g,
    intro g h K,
    apply eq_of_mul_inv_eq_one,
    have e : f (g * h⁻¹) = f g * (f h)⁻¹,
    from calc
      f (g * h⁻¹) = f g * (f h⁻¹) : to_respect_mul
             ...  = f g * (f h)⁻¹ : to_respect_inv,
    rewrite (inverse e),
    apply H, exact K
  end

  definition quotient_group_elim [constructor] (f : G →g G') (H : Π⦃g⦄, N g → f g = 1) : quotient_group N →g G' :=
  begin
    fapply homomorphism.mk,
      -- define function
    { exact quotient_group_elim_fun f H },
    { intro g h, induction g using set_quotient.rec_prop with g,
      induction h using set_quotient.rec_prop with h,
      krewrite (inverse (to_respect_mul (qg_map N) g h)),
      unfold qg_map, esimp, exact to_respect_mul f g h }
  end

  definition quotient_group_compute (f : G →g G') (H : Π⦃g⦄, N g → f g = 1) :
    quotient_group_elim f H ∘g qg_map N ~ f :=
  begin
    intro g, reflexivity
  end

  definition gelim_unique (f : G →g G') (H : Π⦃g⦄, N g → f g = 1) (k : quotient_group N →g G')
    : ( k ∘g qg_map N ~ f ) → k ~ quotient_group_elim f H :=
  begin
    intro K cg, induction cg using set_quotient.rec_prop with g,
    exact K g
  end

  definition ab_gelim_unique {K : subgroup_rel A} (f : A →g B) (H : Π (a :A), K a → f a = 1) (k : quotient_ab_group K →g B)
    : ( k ∘g ab_qg_map K ~ f) → k ~ quotient_group_elim f H :=
  begin
    fapply gelim_unique,
  end

  definition qg_universal_property (f : G →g G') (H : Π⦃g⦄, N g → f g = 1)  :
    is_contr (Σ(g : quotient_group N →g G'), g ∘g qg_map N ~ f) :=
  begin
    fapply is_contr.mk,
      -- give center of contraction
    { fapply sigma.mk, exact quotient_group_elim f H, exact quotient_group_compute f H },
      -- give contraction
    { intro pair, induction pair with g p, fapply sigma_eq,
      {esimp, apply homomorphism_eq, symmetry, exact gelim_unique f H g p},
      {fapply is_prop.elimo} }
  end

  definition ab_qg_universal_property {K : subgroup_rel A} (f : A →g B) (H : Π (a :A), K a → f a = 1) :
  is_contr ((Σ(g : quotient_ab_group K →g B), g ∘g ab_qg_map K ~ f) ) :=
  begin
    fapply qg_universal_property,
    exact H
  end

  definition quotient_group_functor_contr {K L : subgroup_rel A} (H : Π (a : A), K a → L a) :
  is_contr ((Σ(g : quotient_ab_group K →g quotient_ab_group L), g ∘g ab_qg_map K ~ ab_qg_map L) ) :=
  begin
    fapply ab_qg_universal_property,
    intro a p,
    fapply qg_map_eq_one,
    exact H a p,
  end

  definition quotient_group_functor_id {K : subgroup_rel A} (H : Π (a : A), K a → K a) : 
    center' (@quotient_group_functor_contr _ K K H) = ⟨gid (quotient_ab_group K), λ x, rfl⟩ :=
    begin
      note p := @quotient_group_functor_contr _ K K H,
      fapply eq_of_is_contr,
    end 

  section quotient_group_iso_ua

  set_option pp.universes true

  definition subgroup_rel_eq' {K L : subgroup_rel A} (htpy : Π (a : A), K a ≃ L a) : K = L :=
  begin
    induction K with K', induction L with L', esimp at *,
    assert q : K' = L',
    begin
      fapply eq_of_homotopy,
      intro a,
      fapply tua,
      exact htpy a,
    end,
    induction q,
    assert q : Rone = Rone_1,
    begin
      fapply is_prop.elim,
    end,
    induction q,
    assert q2 : @Rmul = @Rmul_1,
    begin
      fapply is_prop.elim,
    end,
    induction q2,
    assert q : @Rinv = @Rinv_1,
    begin
      fapply is_prop.elim,
    end,
    induction q,
    reflexivity    
  end

  definition subgroup_rel_eq {K L : subgroup_rel A} (forth : Π (a : A), K a → L a) (opforth : Π (a : A), L a → K a) : K = L :=
  begin
    have htpy : Π (a : A), K a ≃ L a,
    begin
      intro a,
      fapply equiv_of_is_prop,
      fapply forth a,
      fapply opforth a,
    end,
    exact subgroup_rel_eq' htpy,
  end

  definition  eq_of_ab_qg_group' {K L : subgroup_rel A} (p : K = L) : quotient_ab_group K = quotient_ab_group L :=
  begin
    induction p, reflexivity
  end

  definition eq_of_ab_qg_group {K L : subgroup_rel A} (forth : Π (a : A), K a → L a) (opforth : Π (a : A), L a → K a) : quotient_ab_group K = quotient_ab_group L :=
  eq_of_ab_qg_group' (subgroup_rel_eq forth opforth) 

  end quotient_group_iso_ua
  
  section quotient_group_iso
  variables {K L : subgroup_rel A} (H1 : Π (a : A), K a → L a) (H2 : Π (a : A), L a → K a)
  include H1
  include H2
  
  definition quotient_group_iso_contr_KL_map :
    quotient_ab_group K →g quotient_ab_group L :=
    pr1 (center' (quotient_group_functor_contr H1))

  definition quotient_group_iso_contr_KL_triangle :
    quotient_group_iso_contr_KL_map H1 H2 ∘g ab_qg_map K ~ ab_qg_map L :=
    pr2 (center' (quotient_group_functor_contr H1))

  definition quotient_group_iso_contr_KK :
    is_contr (Σ (g : quotient_ab_group K →g quotient_ab_group K), g ∘g ab_qg_map K ~ ab_qg_map K) :=
    @quotient_group_functor_contr A K K (λ a, H2 a ∘ H1 a)

  definition quotient_group_iso_contr_LK :
    quotient_ab_group L →g quotient_ab_group K :=
    pr1 (center' (@quotient_group_functor_contr A L K H2))

  definition quotient_group_iso_contr_LL : 
    quotient_ab_group L →g quotient_ab_group L :=
    pr1 (center' (@quotient_group_functor_contr A L L (λ a, H1 a ∘ H2 a)))

/-
  definition quotient_group_iso : quotient_ab_group K ≃g quotient_ab_group L :=
    begin
      fapply isomorphism.mk,
      exact pr1 (center' (quotient_group_iso_contr_KL H1 H2)),
      fapply adjointify,
      exact quotient_group_iso_contr_LK H1 H2,
      intro x,
      induction x, reflexivity,
    end
-/

  definition quotient_group_iso_contr_aux  : 
    is_contr (Σ(gh : Σ (g : quotient_ab_group K →g quotient_ab_group L), g ∘g ab_qg_map K ~ ab_qg_map L), is_equiv (group_fun (pr1 gh))) :=
  begin
    fapply is_trunc_sigma,
    exact quotient_group_functor_contr H1,
    intro a, induction a with g h,
    fapply is_contr_of_inhabited_prop,
    fapply adjointify,
    rexact group_fun (pr1 (center' (@quotient_group_functor_contr A L K H2))),
    note htpy := homotopy_of_eq (ap group_fun (ap sigma.pr1 (@quotient_group_functor_id _ L (λ a, (H1 a) ∘ (H2 a))))),  
    have KK : is_contr ((Σ(g' : quotient_ab_group K →g quotient_ab_group K), g' ∘g ab_qg_map K ~ ab_qg_map K) ), from
      quotient_group_functor_contr (λ a, (H2 a) ∘ (H1 a)),
    -- have KK_path : ⟨g, h⟩ = ⟨id, λ a, refl (ab_qg_map K a)⟩, from eq_of_is_contr ⟨g, h⟩ ⟨id, λ a, refl (ab_qg_map K a)⟩, 
    repeat exact sorry
  end
/-
  definition quotient_group_iso_contr {K L : subgroup_rel A} (H1 : Π (a : A), K a → L a) (H2 : Π (a : A), L a → K a) : 
    is_contr (Σ (g : quotient_ab_group K ≃g quotient_ab_group L), g ∘g ab_qg_map K ~ ab_qg_map L) :=
  begin
    refine @is_trunc_equiv_closed (Σ(gh : Σ (g : quotient_ab_group K →g quotient_ab_group L), g ∘g ab_qg_map K ~ ab_qg_map L), is_equiv (group_fun (pr1 gh))) (Σ (g : quotient_ab_group K ≃g quotient_ab_group L), g ∘g ab_qg_map K ~ ab_qg_map L) -2 _ (quotient_group_iso_contr_aux H1 H2), 
  exact calc
    (Σ gh, is_equiv (group_fun gh.1)) ≃ Σ (g : quotient_ab_group K →g quotient_ab_group L) (h : g ∘g ab_qg_map K ~ ab_qg_map L), is_equiv (group_fun g) : by exact (sigma_assoc_equiv (λ gh, is_equiv (group_fun gh.1)))⁻¹
    ... ≃ (Σ (g : quotient_ab_group K ≃g quotient_ab_group L), g ∘g ab_qg_map K ~ ab_qg_map L) : _
  end
-/

  end quotient_group_iso

 
  definition quotient_group_functor [constructor] (φ : G →g G') (h : Πg, N g → N' (φ g)) :
    quotient_group N →g quotient_group N' :=
  begin
    apply quotient_group_elim (qg_map N' ∘g φ),
    intro g Ng, esimp,
    refine qg_map_eq_one (φ g) (h g Ng)
  end

------------------------------------------------
  -- FIRST ISOMORPHISM THEOREM
------------------------------------------------


definition kernel_quotient_extension {A B : AbGroup} (f : A →g B) : quotient_ab_group (kernel_subgroup f) →g B :=
  begin
    fapply quotient_group_elim f, intro a, intro p, exact p
  end

definition kernel_quotient_extension_triangle {A B : AbGroup} (f : A →g B) :
  kernel_quotient_extension f ∘g ab_qg_map (kernel_subgroup f) ~ f :=
  begin
    intro a,
    apply quotient_group_compute
  end

definition is_embedding_kernel_quotient_extension {A B : AbGroup} (f : A →g B) :
  is_embedding (kernel_quotient_extension f) :=
  begin
    fapply is_embedding_of_is_mul_hom,
    intro x,
    note H := is_surjective_ab_qg_map (kernel_subgroup f) x,
    induction H, induction p,
    intro q,
    apply qg_map_eq_one,
    refine _ ⬝ q,
    symmetry,
    rexact kernel_quotient_extension_triangle f a
  end

definition ab_group_quotient_homomorphism (A B : AbGroup)(K : subgroup_rel A)(L : subgroup_rel B) (f : A →g B)
     (p : Π(a:A), K(a) → L(f a)) : quotient_ab_group K →g quotient_ab_group L :=
    begin
    fapply quotient_group_elim,
    exact (ab_qg_map L) ∘g f,
    intro a,
    intro k,
    exact @ab_qg_map_eq_one B L (f a) (p a k),
    end

definition ab_group_kernel_factor {A B C: AbGroup} (f : A →g B)(g : A →g C){i : C →g B}(H : f = i ∘g g )
           : Π a:A , kernel_subgroup(g)(a) → kernel_subgroup(f)(a) :=
  begin
   intro a,
   intro p,
   exact calc
     f a = i (g a)            : homotopy_of_eq (ap group_fun H) a
     ... = i 1                : ap i p
     ... = 1                  : respect_one i
  end

definition  ab_group_triv_kernel_factor {A B C: AbGroup} (f : A →g B)(g : A →g C){i : C →g B}(H : f = i ∘g g ) :
 is_trivial_subgroup _ (kernel_subgroup(f)) → is_trivial_subgroup _ (kernel_subgroup(g)) :=
 begin
   intro p,
   intro a,
   intro q,
   fapply p,
   exact ab_group_kernel_factor f g H a q
 end

definition triv_kern_is_embedding {A B : AbGroup} (f : A →g B):
is_trivial_subgroup _ (kernel_subgroup(f)) → is_embedding(f) :=
  begin
  intro p,
  fapply is_embedding_of_is_mul_hom,
  intro a q,
  apply p,
  exact q
  end

definition ab_group_kernel_equivalent {A B : AbGroup} (C : AbGroup) (f : A →g B)(g : A →g C)(i : C →g B)(H : f = i ∘g g )(K : is_embedding i)
           : Π a:A , kernel_subgroup(g)(a) ↔ kernel_subgroup(f)(a) :=
begin
  intro a,
  fapply iff.intro,
  exact ab_group_kernel_factor f g H a,
  intro p,
  apply @is_injective_of_is_embedding _ _ i _ (g a) 1,
  exact calc
    i (g a) = f a       : (homotopy_of_eq (ap group_fun H) a)⁻¹
        ... = 1         : p
        ... = i 1       : (respect_one i)⁻¹
end

definition ab_group_kernel_image_lift (A B : AbGroup) (f : A →g B)
           : Π a : A, kernel_subgroup(image_lift(f))(a) ↔ kernel_subgroup(f)(a) :=
  begin
    fapply ab_group_kernel_equivalent (ab_image f) (f) (image_lift(f)) (image_incl(f)),
    exact image_factor f,
    exact is_embedding_of_is_injective (image_incl_injective(f)),
  end

definition ab_group_kernel_quotient_to_image {A B : AbGroup} (f : A →g B)
           : quotient_ab_group (kernel_subgroup f) →g ab_image (f) :=
  begin
           fapply quotient_group_elim (image_lift f), intro a, intro p,
           apply iff.mpr (ab_group_kernel_image_lift _ _ f a) p
  end

definition ab_group_kernel_quotient_to_image_domain_triangle {A B : AbGroup} (f : A →g B)
           :  ab_group_kernel_quotient_to_image (f) ∘g ab_qg_map (kernel_subgroup (f)) ~ image_lift(f) :=
  begin
    intros a,
    esimp,
  end

definition ab_group_kernel_quotient_to_image_codomain_triangle {A B : AbGroup} (f : A →g B)
           : image_incl f ∘g ab_group_kernel_quotient_to_image f ~ kernel_quotient_extension f :=
  begin
    intro x,
    induction x,
    reflexivity,
    fapply is_prop.elimo
  end

definition is_surjective_kernel_quotient_to_image {A B : AbGroup} (f : A →g B)
           : is_surjective (ab_group_kernel_quotient_to_image f) :=
  begin
    fapply @is_surjective_factor A _ (image f) _ _ _ (group_fun (ab_qg_map (kernel_subgroup f))),
exact image_lift f,
apply quotient_group_compute,
exact is_surjective_image_lift f
  end

definition is_embedding_kernel_quotient_to_image {A B : AbGroup} (f : A →g B)
           : is_embedding (ab_group_kernel_quotient_to_image f) :=
  begin
    fapply @is_embedding_factor _ (image f) B _ _ _ (ab_group_kernel_quotient_to_image f) (image_incl f) (kernel_quotient_extension f),
    exact ab_group_kernel_quotient_to_image_codomain_triangle f,
    exact is_embedding_kernel_quotient_extension f
  end

definition ab_group_first_iso_thm {A B : AbGroup} (f : A →g B)
           : quotient_ab_group (kernel_subgroup f) ≃g ab_image f :=
  begin
    fapply isomorphism.mk,
    exact ab_group_kernel_quotient_to_image f,
    fapply is_equiv_of_is_surjective_of_is_embedding,
    exact is_embedding_kernel_quotient_to_image f,
    exact is_surjective_kernel_quotient_to_image f
  end

definition codomain_surjection_is_quotient {A B : AbGroup} (f : A →g B)( H : is_surjective f)
           : quotient_ab_group (kernel_subgroup f) ≃g B :=
    begin
     exact (ab_group_first_iso_thm f) ⬝g (iso_surjection_ab_image_incl f H)
   end

definition codomain_surjection_is_quotient_triangle {A B : AbGroup} (f : A →g B)( H : is_surjective f)
           : codomain_surjection_is_quotient (f)(H) ∘g ab_qg_map (kernel_subgroup f) ~ f :=
     begin
    intro a,
    esimp
     end

-- print iff.mpr
    /- set generating normal subgroup -/

  section

    parameters {A₁ : AbGroup} (S : A₁ → Prop)
    variable {A₂ : AbGroup}

    inductive generating_relation' : A₁ → Type :=
    | rincl : Π{g}, S g → generating_relation' g
    | rmul  : Π{g h}, generating_relation' g → generating_relation' h → generating_relation' (g * h)
    | rinv  : Π{g}, generating_relation' g → generating_relation' g⁻¹
    | rone  : generating_relation' 1
    open generating_relation'
    definition generating_relation (g : A₁) : Prop := ∥ generating_relation' g ∥
    local abbreviation R := generating_relation
    definition gr_one : R 1 := tr (rone S)
    definition gr_inv (g : A₁) : R g → R g⁻¹ :=
    trunc_functor -1 rinv
    definition gr_mul (g h : A₁) : R g → R h → R (g * h) :=
    trunc_functor2 rmul

    definition normal_generating_relation : subgroup_rel A₁ :=
    ⦃ subgroup_rel,
      R := R,
      Rone := gr_one,
      Rinv := gr_inv,
      Rmul := gr_mul⦄

    parameter (A₁)
    definition quotient_ab_group_gen : AbGroup := quotient_ab_group normal_generating_relation

    definition gqg_map [constructor] : A₁ →g quotient_ab_group_gen :=
    qg_map _

    parameter {A₁}
    definition gqg_eq_of_rel {g h : A₁} (H : S (g * h⁻¹)) : gqg_map g = gqg_map h :=
    eq_of_rel (tr (rincl H))

    -- this one might work if the previous one doesn't (maybe make this the default one?)
    definition gqg_eq_of_rel' {g h : A₁} (H : S (g * h⁻¹)) : class_of g = class_of h :> quotient_ab_group_gen :=
    gqg_eq_of_rel H

    definition gqg_elim [constructor] (f : A₁ →g A₂) (H : Π⦃g⦄, S g → f g = 1)
      : quotient_ab_group_gen →g A₂ :=
    begin
      apply quotient_group_elim f,
      intro g r, induction r with r,
      induction r with g s g h r r' IH1 IH2 g r IH,
      { exact H s },
      { exact !respect_mul ⬝ ap011 mul IH1 IH2 ⬝ !one_mul },
      { exact !respect_inv ⬝ ap inv IH ⬝ !one_inv },
      { apply respect_one }
    end

    definition gqg_elim_compute (f : A₁ →g A₂) (H : Π⦃g⦄, S g → f g = 1)
      : gqg_elim f H ∘g gqg_map ~ f :=
    begin
      intro g, reflexivity
    end

    definition gqg_elim_unique (f : A₁ →g A₂) (H : Π⦃g⦄, S g → f g = 1)
      (k : quotient_ab_group_gen →g A₂) : ( k ∘g gqg_map ~ f ) → k ~ gqg_elim f H :=
    !gelim_unique

  end

end group

namespace group

  variables {G H K : Group} {R : normal_subgroup_rel G} {S : normal_subgroup_rel H}
    {T : normal_subgroup_rel K}

  definition quotient_ab_group_functor [constructor] {G H : AbGroup} {R : subgroup_rel G}
    {S : subgroup_rel H} (φ : G →g H)
    (h : Πg, R g → S (φ g)) : quotient_ab_group R →g quotient_ab_group S :=
  quotient_group_functor φ h

  theorem quotient_group_functor_compose (ψ : H →g K) (φ : G →g H)
    (hψ : Πg, S g → T (ψ g)) (hφ : Πg, R g → S (φ g)) :
    quotient_group_functor ψ hψ ∘g quotient_group_functor φ hφ ~
    quotient_group_functor (ψ ∘g φ) (λg, proof hψ (φ g) qed ∘ hφ g) :=
  begin
    intro g, induction g using set_quotient.rec_prop with g hg, reflexivity
  end

  definition quotient_group_functor_gid :
    quotient_group_functor (gid G) (λg, id) ~ gid (quotient_group R) :=
  begin
    intro g, induction g using set_quotient.rec_prop with g hg, reflexivity
  end

  definition quotient_group_functor_mul.{u₁ v₁ u₂ v₂}
    {G H : AbGroup} {R : subgroup_rel.{u₁ v₁} G} {S : subgroup_rel.{u₂ v₂} H}
    (ψ φ : G →g H) (hψ : Πg, R g → S (ψ g)) (hφ : Πg, R g → S (φ g)) :
    homomorphism_mul (quotient_ab_group_functor ψ hψ) (quotient_ab_group_functor φ hφ) ~
    quotient_ab_group_functor (homomorphism_mul ψ φ)
                        (λg hg, subgroup_respect_mul S (hψ g hg) (hφ g hg)) :=
  begin
    intro g, induction g using set_quotient.rec_prop with g hg, reflexivity
  end

  definition quotient_group_functor_homotopy {ψ φ : G →g H} (hψ : Πg, R g → S (ψ g))
    (hφ : Πg, R g → S (φ g)) (p : φ ~ ψ) :
    quotient_group_functor φ hφ ~ quotient_group_functor ψ hψ :=
  begin
    intro g, induction g using set_quotient.rec_prop with g hg,
    exact ap set_quotient.class_of (p g)
  end

end group
