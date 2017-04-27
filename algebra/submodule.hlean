
import .left_module .quotient_group

open algebra eq group sigma is_trunc function trunc equiv is_equiv

-- move to subgroup
attribute normal_subgroup_rel._trans_of_to_subgroup_rel [unfold 2]
attribute normal_subgroup_rel.to_subgroup_rel [constructor]

  definition is_equiv_incl_of_subgroup {G : Group} (H : subgroup_rel G) (h : Πg, H g) :
    is_equiv (incl_of_subgroup H) :=
  have is_surjective (incl_of_subgroup H),
  begin intro g, exact image.mk ⟨g, h g⟩ idp end,
  have is_embedding (incl_of_subgroup H), from is_embedding_incl_of_subgroup H,
  function.is_equiv_of_is_surjective_of_is_embedding (incl_of_subgroup H)

definition subgroup_isomorphism [constructor] {G : Group} (H : subgroup_rel G) (h : Πg, H g) :
  subgroup H ≃g G :=
isomorphism.mk _ (is_equiv_incl_of_subgroup H h)

definition is_equiv_qg_map {G : Group} (H : normal_subgroup_rel G) (H₂ : Π⦃g⦄, H g → g = 1) :
  is_equiv (qg_map H) :=
set_quotient.is_equiv_class_of _ (λg h r, eq_of_mul_inv_eq_one (H₂ r))

definition quotient_group_isomorphism [constructor] {G : Group} (H : normal_subgroup_rel G)
  (h : Πg, H g → g = 1) : quotient_group H ≃g G :=
(isomorphism.mk _ (is_equiv_qg_map H h))⁻¹ᵍ

definition is_equiv_ab_qg_map {G : AbGroup} (H : subgroup_rel G) (h : Π⦃g⦄, H g → g = 1) :
  is_equiv (ab_qg_map H) :=
proof is_equiv_qg_map _ h qed

definition ab_quotient_group_isomorphism [constructor] {G : AbGroup} (H : subgroup_rel G)
  (h : Πg, H g → g = 1) : quotient_ab_group H ≃g G :=
(isomorphism.mk _ (is_equiv_ab_qg_map H h))⁻¹ᵍ

namespace left_module
/- submodules -/
variables {R : Ring} {M M₁ M₂ M₃ : LeftModule R} {m m₁ m₂ : M}

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

definition hom_lift [constructor] {K : submodule_rel M₂} (φ : M₁ →lm M₂)
  (h : Π (m : M₁), K (φ m)) : M₁ →lm submodule K :=
lm_homomorphism_of_group_homomorphism (hom_lift (group_homomorphism_of_lm_homomorphism φ) _ h)
  begin
    intro r g, exact subtype_eq (to_respect_smul φ r g)
  end

definition hom_lift_compose {K : submodule_rel M₃}
  (φ : M₂ →lm M₃) (h : Π (m : M₂), K (φ m)) (ψ : M₁ →lm M₂) :
  hom_lift φ h ∘lm ψ ~ hom_lift (φ ∘lm ψ) proof (λm, h (ψ m)) qed :=
by reflexivity

definition hom_lift_homotopy {K : submodule_rel M₂} {φ : M₁ →lm M₂}
  {h : Π (m : M₁), K (φ m)} {φ' : M₁ →lm M₂}
  {h' : Π (m : M₁), K (φ' m)} (p : φ ~ φ') : hom_lift φ h ~ hom_lift φ' h' :=
λg, subtype_eq (p g)

definition incl_smul (S : submodule_rel M) (r : R) (m : M) (h : S m) :
  r • ⟨m, h⟩ = ⟨_, contains_smul S r h⟩ :> submodule S :=
by reflexivity

definition submodule_rel_submodule [constructor] (S₂ S₁ : submodule_rel M) :
  submodule_rel (submodule S₂) :=
submodule_rel.mk (λm, S₁ (submodule_incl S₂ m))
  (contains_zero S₁)
  (λm n p q, contains_add S₁ p q)
  begin
    intro m r p, induction m with m hm, exact contains_smul S₁ r p
  end

definition submodule_rel_submodule_trivial [constructor] {S₂ S₁ : submodule_rel M}
  (h : Π⦃m⦄, S₁ m → m = 0) ⦃m : submodule S₂⦄ (Sm : submodule_rel_submodule S₂ S₁ m) : m = 0 :=
begin
  fapply subtype_eq,
  apply h Sm
end

definition is_prop_submodule (S : submodule_rel M) [H : is_prop M] : is_prop (submodule S) :=
begin apply @is_trunc_sigma, exact H end
local attribute is_prop_submodule [instance]
definition is_contr_submodule [instance] (S : submodule_rel M) [is_contr M] : is_contr (submodule S) :=
is_contr_of_inhabited_prop 0

definition submodule_isomorphism [constructor] (S : submodule_rel M) (h : Πg, S g) :
  submodule S ≃lm M :=
isomorphism.mk (submodule_incl S) (is_equiv_incl_of_subgroup (subgroup_rel_of_submodule_rel S) h)

/- quotient modules -/

definition quotient_module' (S : submodule_rel M) : AddAbGroup :=
quotient_ab_group (subgroup_rel_of_submodule_rel S)

definition quotient_module_smul [constructor] (S : submodule_rel M) (r : R) :
  quotient_module' S →a quotient_module' S :=
quotient_ab_group_functor (smul_homomorphism M r) (λg, contains_smul S r)



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

definition quotient_map [constructor] (S : submodule_rel M) : M →lm quotient_module S :=
lm_homomorphism_of_group_homomorphism (ab_qg_map _) (λr g, idp)

definition quotient_map_eq_zero (m : M) (H : S m) : quotient_map S m = 0 :=
qg_map_eq_one _ H

definition quotient_elim [constructor] (φ : M →lm M₂) (H : Π⦃m⦄, S m → φ m = 0) :
  quotient_module S →lm M₂ :=
lm_homomorphism_of_group_homomorphism
  (quotient_group_elim (group_homomorphism_of_lm_homomorphism φ) H)
  begin
    intro r m, esimp,
    induction m using set_quotient.rec_prop with m,
    exact to_respect_smul φ r m
  end

definition is_prop_quotient_module (S : submodule_rel M) [H : is_prop M] : is_prop (quotient_module S) :=
begin apply @set_quotient.is_trunc_set_quotient, exact H end
local attribute is_prop_quotient_module [instance]

definition is_contr_quotient_module [instance] (S : submodule_rel M) [is_contr M] :
  is_contr (quotient_module S) :=
is_contr_of_inhabited_prop 0

definition quotient_module_isomorphism [constructor] (S : submodule_rel M) (h : Π⦃m⦄, S m → m = 0) :
  quotient_module S ≃lm M :=
(isomorphism.mk (quotient_map S) (is_equiv_ab_qg_map (subgroup_rel_of_submodule_rel S) h))⁻¹ˡᵐ

/- specific submodules -/
definition has_scalar_image (φ : M₁ →lm M₂) ⦃m : M₂⦄ (r : R)
  (h : image φ m) : image φ (r • m) :=
begin
  induction h with m' p,
  apply image.mk (r • m'),
  refine to_respect_smul φ r m' ⬝ ap (λx, r • x) p,
end

definition image_rel [constructor] (φ : M₁ →lm M₂) : submodule_rel M₂ :=
submodule_rel_of_subgroup_rel
  (image_subgroup (group_homomorphism_of_lm_homomorphism φ))
  (has_scalar_image φ)

definition image_rel_trivial (φ : M₁ →lm M₂) [H : is_contr M₁] ⦃m : M₂⦄ (h : image_rel φ m) : m = 0 :=
begin
  refine image.rec _ h,
  intro x p,
  refine p⁻¹ ⬝ ap φ _ ⬝ to_respect_zero φ,
  apply @is_prop.elim, apply is_trunc_succ, exact H
end

definition image_module [constructor] (φ : M₁ →lm M₂) : LeftModule R := submodule (image_rel φ)

-- unfortunately this is note definitionally equal:
-- definition foo (φ : M₁ →lm M₂) :
--   (image_module φ : AddAbGroup) = image (group_homomorphism_of_lm_homomorphism φ) :=
-- by reflexivity

definition image_lift [constructor] (φ : M₁ →lm M₂) : M₁ →lm image_module φ :=
hom_lift φ (λm, image.mk m idp)

variables {ψ : M₂ →lm M₃} {φ : M₁ →lm M₂} {θ : M₁ →lm M₃}
definition image_elim [constructor] (θ : M₁ →lm M₃) (h : Π⦃g⦄, φ g = 0 → θ g = 0) :
  image_module φ →lm M₃ :=
begin
  refine homomorphism.mk (image_elim (group_homomorphism_of_lm_homomorphism θ) h) _,
  split,
  { apply homomorphism.addstruct },
  { intro r, refine @total_image.rec _ _ _ _ (λx, !is_trunc_eq) _, intro g,
    apply to_respect_smul }
end

definition image_elim_compute (h : Π⦃g⦄, φ g = 0 → θ g = 0) :
  image_elim θ h ∘lm image_lift φ ~ θ :=
begin
  reflexivity
end

definition is_contr_image_module [instance] (φ : M₁ →lm M₂) [is_contr M₂] :
  is_contr (image_module φ) :=
!is_contr_submodule

definition is_contr_image_module_of_is_contr_dom (φ : M₁ →lm M₂) [is_contr M₁] :
  is_contr (image_module φ) :=
is_contr.mk 0
  begin
    have Π(x : image_module φ), is_prop (0 = x), from _,
    apply @total_image.rec,
    exact this,
    intro m,
    induction (is_prop.elim 0 m), apply subtype_eq,
    exact (to_respect_zero φ)⁻¹
  end

definition image_module_isomorphism [constructor] (φ : M₁ ≃lm M₂) : image_module φ ≃lm M₂ :=
submodule_isomorphism _ (λm, image.mk (φ⁻¹ˡᵐ m) proof to_right_inv (equiv_of_isomorphism φ) m qed)

definition has_scalar_kernel (φ : M₁ →lm M₂) ⦃m : M₁⦄ (r : R)
  (p : φ m = 0) : φ (r • m) = 0 :=
begin
  refine to_respect_smul φ r m ⬝ ap (λx, r • x) p ⬝ smul_zero r,
end

definition kernel_rel [constructor] (φ : M₁ →lm M₂) : submodule_rel M₁ :=
submodule_rel_of_subgroup_rel
  (kernel_subgroup (group_homomorphism_of_lm_homomorphism φ))
  (has_scalar_kernel φ)

definition kernel_rel_full (φ : M₁ →lm M₂) [is_contr M₂] (m : M₁) : kernel_rel φ m :=
!is_prop.elim

definition kernel_module [constructor] (φ : M₁ →lm M₂) : LeftModule R := submodule (kernel_rel φ)

definition is_contr_kernel_module [instance] (φ : M₁ →lm M₂) [is_contr M₁] :
  is_contr (kernel_module φ) :=
!is_contr_submodule

definition kernel_module_isomorphism [constructor] (φ : M₁ →lm M₂) [is_contr M₂] : kernel_module φ ≃lm M₁ :=
submodule_isomorphism _ (kernel_rel_full φ)

definition homology (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) : LeftModule R :=
@quotient_module R (submodule (kernel_rel ψ)) (submodule_rel_submodule _ (image_rel φ))

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

definition homology_elim [constructor] (θ : M₂ →lm M) (H : Πm, θ (φ m) = 0) :
  homology ψ φ →lm M :=
quotient_elim (θ ∘lm submodule_incl _)
  begin
    intro m x,
    induction m with m h,
    esimp at *,
    induction x with v, induction v with m' p,
    exact ap θ p⁻¹ ⬝ H m'
  end

definition is_contr_homology [instance] (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) [is_contr M₂] :
  is_contr (homology ψ φ) :=
begin apply @is_contr_quotient_module end

definition homology_isomorphism [constructor] (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) [is_contr M₁] [is_contr M₃] :
  homology ψ φ ≃lm M₂ :=
quotient_module_isomorphism _ (submodule_rel_submodule_trivial (image_rel_trivial φ)) ⬝lm
!kernel_module_isomorphism

-- remove:

-- definition homology.rec (P : homology ψ φ → Type)
--   [H : Πx, is_set (P x)] (h₀ : Π(m : M₂) (h : ψ m = 0), P (homology.mk m h))
--   (h₁ : Π(m : M₂) (h : ψ m = 0) (k : image φ m), h₀ m h =[homology_eq0' k] h₀ 0 (to_respect_zero ψ))
--   : Πx, P x :=
-- begin
--   refine @set_quotient.rec _ _ _ H _ _,
--   { intro v, induction v with m h, exact h₀ m h },
--   { intro v v', induction v with m hm, induction v' with n hn,
--     intro h,
--     note x := h₁ (m - n) _ h,
--     esimp,
--     exact change_path _ _,
-- }
-- end

  -- definition quotient.rec (P : quotient_group N → Type)
  --   [H : Πx, is_set (P x)] (h₀ : Π(g : G), P (qg_map N g))
  --   -- (h₀_mul : Π(g h : G), h₀ (g * h))
  --   (h₁ : Π(g : G) (h : N g), h₀ g =[qg_map_eq_one g h] h₀ 1)
  --   : Πx, P x :=
  -- begin
  --   refine @set_quotient.rec _ _ _ H _ _,
  --   { intro g, exact h₀ g },
  --   { intro g g' h,
  --     note x := h₁ (g * g'⁻¹) h,
  --     }
  -- --   { intro v, induction  },
  -- --   { intro v v', induction v with m hm, induction v' with n hn,
  -- --     intro h,
  -- --     note x := h₁ (m - n) _ h,
  -- --     esimp,
  -- --     exact change_path _ _,
  -- -- }
  -- end



end left_module
