
import .left_module .quotient_group

open algebra eq group sigma is_trunc function trunc

/- move to subgroup -/

namespace group

  variables {G H K : Group} {R : subgroup_rel G} {S : subgroup_rel H} {T : subgroup_rel K}

  definition subgroup_functor_fun [unfold 7] (φ : G →g H) (h : Πg, R g → S (φ g)) (x : subgroup R) :
    subgroup S :=
  begin
    induction x with g hg,
    exact ⟨φ g, h g hg⟩
  end

  definition subgroup_functor [constructor] (φ : G →g H)
    (h : Πg, R g → S (φ g)) : subgroup R →g subgroup S :=
  begin
    fapply homomorphism.mk,
    { exact subgroup_functor_fun φ h },
    { intro x₁ x₂, induction x₁ with g₁ hg₁, induction x₂ with g₂ hg₂,
      exact sigma_eq !to_respect_mul !is_prop.elimo }
  end

  definition ab_subgroup_functor [constructor] {G H : AbGroup} {R : subgroup_rel G}
    {S : subgroup_rel H} (φ : G →g H)
    (h : Πg, R g → S (φ g)) : ab_subgroup R →g ab_subgroup S :=
  subgroup_functor φ h

  theorem subgroup_functor_compose (ψ : H →g K) (φ : G →g H)
    (hψ : Πg, S g → T (ψ g)) (hφ : Πg, R g → S (φ g)) :
    subgroup_functor ψ hψ ∘g subgroup_functor φ hφ ~
    subgroup_functor (ψ ∘g φ) (λg, proof hψ (φ g) qed ∘ hφ g) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_gid : subgroup_functor (gid G) (λg, id) ~ gid (subgroup R) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_mul {G H : AbGroup} {R : subgroup_rel G} {S : subgroup_rel H}
    (ψ φ : G →g H) (hψ : Πg, R g → S (ψ g)) (hφ : Πg, R g → S (φ g)) :
    homomorphism_mul (ab_subgroup_functor ψ hψ) (ab_subgroup_functor φ hφ) ~
    ab_subgroup_functor (homomorphism_mul ψ φ)
                        (λg hg, subgroup_respect_mul S (hψ g hg) (hφ g hg)) :=
  begin
    intro g, induction g with g hg, reflexivity
  end

  definition subgroup_functor_homotopy {ψ φ : G →g H} (hψ : Πg, R g → S (ψ g))
    (hφ : Πg, R g → S (φ g)) (p : φ ~ ψ) :
    subgroup_functor φ hφ ~ subgroup_functor ψ hψ :=
  begin
    intro g, induction g with g hg,
    exact subtype_eq (p g)
  end


end group open group

namespace left_module
/- submodules -/
variables {R : Ring} {M : LeftModule R} {m m₁ m₂ : M}

structure submodule_rel (M : LeftModule R) : Type :=
  (S : M → Prop)
  (Szero : S 0)
  (Sadd : Π⦃g h⦄, S g → S h → S (g + h))
  (Ssmul : Π⦃g⦄ (r : R), S g → S (r • g))

definition contains_zero := @submodule_rel.Szero
definition contains_add  := @submodule_rel.Sadd
definition contains_smul := @submodule_rel.Ssmul
attribute submodule_rel.S [coercion]

theorem contains_neg (S : submodule_rel M) ⦃m⦄ (H : S m) : S (-m) :=
transport (λx, S x) (neg_one_smul m) (contains_smul S (- 1) H)

theorem is_normal_submodule (S : submodule_rel M) ⦃m₁ m₂⦄ (H : S m₁) : S (m₂ + m₁ + (-m₂)) :=
transport (λx, S x) (by rewrite [add.comm, neg_add_cancel_left]) H

open submodule_rel

variables {S : submodule_rel M}

definition subgroup_rel_of_submodule_rel [constructor] (S : submodule_rel M) :
  subgroup_rel (AddGroup_of_AddAbGroup M) :=
subgroup_rel.mk S (contains_zero S) (contains_add S) (contains_neg S)

definition submodule_rel_of_subgroup_rel [constructor] (S : subgroup_rel (AddGroup_of_AddAbGroup M))
  (h : Π⦃g⦄ (r : R), S g → S (r • g)) : submodule_rel M :=
submodule_rel.mk S (subgroup_has_one S) @(subgroup_respect_mul S) h

definition submodule' (S : submodule_rel M) : AddAbGroup :=
ab_subgroup (subgroup_rel_of_submodule_rel S)

definition submodule_smul [constructor] (S : submodule_rel M) (r : R) :
  submodule' S →a submodule' S :=
ab_subgroup_functor (smul_homomorphism M r) (λg, contains_smul S r)

definition submodule_smul_right_distrib (r s : R) (n : submodule' S) :
  submodule_smul S (r + s) n = submodule_smul S r n + submodule_smul S s n :=
begin
  refine subgroup_functor_homotopy _ _ _ n ⬝ !subgroup_functor_mul⁻¹,
  intro m, exact to_smul_right_distrib r s m
end

definition submodule_mul_smul' (r s : R) (n : submodule' S) :
  submodule_smul S (r * s) n = (submodule_smul S r ∘g submodule_smul S s) n :=
begin
  refine subgroup_functor_homotopy _ _ _ n ⬝ (subgroup_functor_compose _ _ _ _ n)⁻¹ᵖ,
  intro m, exact to_mul_smul r s m
end

definition submodule_mul_smul (r s : R) (n : submodule' S) :
  submodule_smul S (r * s) n = submodule_smul S r (submodule_smul S s n) :=
by rexact submodule_mul_smul' r s n

definition submodule_one_smul (n : submodule' S) : submodule_smul S 1 n = n :=
begin
  refine subgroup_functor_homotopy _ _ _ n ⬝ !subgroup_functor_gid,
  intro m, exact to_one_smul m
end

definition submodule (S : submodule_rel M) : LeftModule R :=
LeftModule_of_AddAbGroup (submodule' S) (submodule_smul S)
  (λr, homomorphism.addstruct (submodule_smul S r))
  submodule_smul_right_distrib
  submodule_mul_smul
  submodule_one_smul

definition submodule_incl [constructor] (S : submodule_rel M) : submodule S →lm M :=
lm_homomorphism_of_group_homomorphism (incl_of_subgroup _)
  begin
    intro r m, induction m with m hm, reflexivity
  end

definition incl_smul (S : submodule_rel M) (r : R) (m : M) (h : S m) :
  r • ⟨m, h⟩ = ⟨_, contains_smul S r h⟩ :> submodule S :=
by reflexivity

definition submodule_rel_of_submodule [constructor] (S₂ S₁ : submodule_rel M) :
  submodule_rel (submodule S₂) :=
submodule_rel.mk (λm, S₁ (submodule_incl S₂ m))
  (contains_zero S₁)
  (λm n p q, contains_add S₁ p q)
  begin
    intro m r p, induction m with m hm, exact contains_smul S₁ r p
  end

end left_module

/- move to quotient_group -/

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

set_option pp.universes true
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

end group open group

namespace left_module

/- quotient modules -/
variables {R : Ring} {M M₁ M₂ M₃ : LeftModule R} {m m₁ m₂ : M} {S : submodule_rel M}

definition quotient_module' (S : submodule_rel M) : AddAbGroup :=
quotient_ab_group (subgroup_rel_of_submodule_rel S)

definition quotient_module_smul [constructor] (S : submodule_rel M) (r : R) :
  quotient_module' S →a quotient_module' S :=
quotient_ab_group_functor (smul_homomorphism M r) (λg, contains_smul S r)

set_option formatter.hide_full_terms false

definition quotient_module_smul_right_distrib (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r + s) n = quotient_module_smul S r n + quotient_module_smul S s n :=
begin
  refine quotient_group_functor_homotopy _ _ _ n ⬝ !quotient_group_functor_mul⁻¹,
  intro m, exact to_smul_right_distrib r s m
end

definition quotient_module_mul_smul' (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r * s) n = (quotient_module_smul S r ∘g quotient_module_smul S s) n :=
begin
  refine quotient_group_functor_homotopy _ _ _ n ⬝ (quotient_group_functor_compose _ _ _ _ n)⁻¹ᵖ,
  intro m, exact to_mul_smul r s m
end

definition quotient_module_mul_smul (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r * s) n = quotient_module_smul S r (quotient_module_smul S s n) :=
by rexact quotient_module_mul_smul' r s n

definition quotient_module_one_smul (n : quotient_module' S) : quotient_module_smul S 1 n = n :=
begin
  refine quotient_group_functor_homotopy _ _ _ n ⬝ !quotient_group_functor_gid,
  intro m, exact to_one_smul m
end

definition quotient_module (S : submodule_rel M) : LeftModule R :=
LeftModule_of_AddAbGroup (quotient_module' S) (quotient_module_smul S)
  (λr, homomorphism.addstruct (quotient_module_smul S r))
  quotient_module_smul_right_distrib
  quotient_module_mul_smul
  quotient_module_one_smul

definition quotient_map (S : submodule_rel M) : M →lm quotient_module S :=
lm_homomorphism_of_group_homomorphism (ab_qg_map _) (λr g, idp)

/- specific submodules -/
definition has_scalar_image (φ : M₁ →lm M₂) ⦃m : M₂⦄ (r : R)
  (h : image φ m) : image φ (r • m) :=
begin
  induction h with m' p,
  apply image.mk (r • m'),
  refine to_respect_smul φ r m' ⬝ ap (λx, r • x) p,
end

definition image_rel (φ : M₁ →lm M₂) : submodule_rel M₂ :=
submodule_rel_of_subgroup_rel
  (image_subgroup (group_homomorphism_of_lm_homomorphism φ))
  (has_scalar_image φ)

definition has_scalar_kernel (φ : M₁ →lm M₂) ⦃m : M₁⦄ (r : R)
  (p : φ m = 0) : φ (r • m) = 0 :=
begin
  refine to_respect_smul φ r m ⬝ ap (λx, r • x) p ⬝ smul_zero r,
end

definition kernel_rel (φ : M₁ →lm M₂) : submodule_rel M₁ :=
submodule_rel_of_subgroup_rel
  (kernel_subgroup (group_homomorphism_of_lm_homomorphism φ))
  (has_scalar_kernel φ)

definition homology (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) : LeftModule R :=
@quotient_module R (submodule (kernel_rel ψ)) (submodule_rel_of_submodule _ (image_rel φ))

variables {ψ : M₂ →lm M₃} {φ : M₁ →lm M₂} (h : Πm, ψ (φ m) = 0)
definition homology.mk (m : M₂) (h : ψ m = 0) : homology ψ φ :=
quotient_map _ ⟨m, h⟩

definition homology_eq0 {m : M₂} {hm : ψ m = 0} (h : image φ m) :
  homology.mk m hm = 0 :> homology ψ φ :=
ab_qg_map_eq_one _ h

definition homology_eq0' {m : M₂} {hm : ψ m = 0} (h : image φ m):
  homology.mk m hm = homology.mk 0 (to_respect_zero ψ) :> homology ψ φ :=
ab_qg_map_eq_one _ h

definition homology_eq {m n : M₂} {hm : ψ m = 0} {hn : ψ n = 0} (h : image φ (m - n)) :
  homology.mk m hm = homology.mk n hn :> homology ψ φ :=
eq_of_sub_eq_zero (homology_eq0 h)

-- definition homology.rec (P : homology ψ φ → Type)
--   [H : Πx, is_set (P x)] (h₀ : Π(m : M₂) (h : ψ m = 0), P (homology.mk m h))
--   (h₁ : Π(m : M₂) (h : ψ m = 0) (k : image φ m), h₀ m h =[homology_eq0' k] h₀ 0 (to_respect_zero ψ))
--   : Πx, P x :=
-- begin
--   refine @set_quotient.rec _ _ _ H _ _,
--   { intro v, induction v with m h, exact h₀ m h },
--   { intro v v', induction v with m hm, induction v' with n hn,
--     esimp, intro h,
--     exact change_path _ _, }
-- end



end left_module
