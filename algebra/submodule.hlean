/- submodules and quotient modules -/

-- Authors: Floris van Doorn, Jeremy Avigad
import .left_module .quotient_group

open algebra eq group sigma sigma.ops is_trunc function trunc equiv is_equiv property

namespace left_module
/- submodules -/
variables {R : Ring} {M M₁ M₁' M₂ M₂' M₃ M₃' : LeftModule R} {m m₁ m₂ : M}

structure is_submodule [class] (M : LeftModule R) (S : property M) : Type :=
  (zero_mem : 0 ∈ S)
  (add_mem : Π⦃g h⦄, g ∈ S → h ∈ S → g + h ∈ S)
  (smul_mem : Π⦃g⦄ (r : R), g ∈ S → r • g ∈ S)

definition zero_mem {R : Ring} {M : LeftModule R} (S : property M) [is_submodule M S] := is_submodule.zero_mem S
definition add_mem {R : Ring} {M : LeftModule R} (S : property M) [is_submodule M S] := @is_submodule.add_mem R M S
definition smul_mem {R : Ring} {M : LeftModule R} (S : property M) [is_submodule M S] := @is_submodule.smul_mem R M S

theorem neg_mem (S : property M) [is_submodule M S] ⦃m⦄ (H : m ∈ S) : -m ∈ S :=
transport (λx, x ∈ S) (neg_one_smul m) (smul_mem S (- 1) H)

theorem is_normal_submodule (S : property M) [is_submodule M S] ⦃m₁ m₂⦄ (H : S m₁) : S (m₂ + m₁ + (-m₂)) :=
transport (λx, S x) (by rewrite [add.comm, neg_add_cancel_left]) H

-- open is_submodule

variables {S : property M} [is_submodule M S] {S₂ : property M₂} [is_submodule M₂ S₂]

definition is_subgroup_of_is_submodule [instance] (S : property M) [is_submodule M S] :
  is_subgroup (AddGroup_of_AddAbGroup M) S :=
is_subgroup.mk (zero_mem S) (add_mem S) (neg_mem S)

definition is_subgroup_of_is_submodule' [instance] (S : property M) [is_submodule M S] : is_subgroup (Group_of_AbGroup (AddAbGroup_of_LeftModule M)) S :=
is_subgroup.mk (zero_mem S) (add_mem S) (neg_mem S)

definition submodule' (S : property M) [is_submodule M S] : AddAbGroup :=
ab_subgroup S -- (subgroup_rel_of_submodule_rel S)

definition submodule_smul [constructor] (S : property M) [is_submodule M S] (r : R) :
  submodule' S →a submodule' S :=
ab_subgroup_functor (smul_homomorphism M r) (λg, smul_mem S r)

definition submodule_smul_right_distrib (r s : R) (n : submodule' S) :
  submodule_smul S (r + s) n = submodule_smul S r n + submodule_smul S s n :=
begin
  refine subgroup_functor_homotopy _ _ _ n ⬝ !subgroup_functor_mul⁻¹ᵖ,
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

definition submodule_one_smul (n : submodule' S) : submodule_smul S (1 : R) n = n :=
begin
  refine subgroup_functor_homotopy _ _ _ n ⬝ !subgroup_functor_gid,
  intro m, exact to_one_smul m
end

definition submodule (S : property M) [is_submodule M S] : LeftModule R :=
LeftModule_of_AddAbGroup (submodule' S) (submodule_smul S)
  (λr, homomorphism.addstruct (submodule_smul S r))
  submodule_smul_right_distrib
  submodule_mul_smul
  submodule_one_smul

definition submodule_incl [constructor] (S : property M) [is_submodule M S] : submodule S →lm M :=
lm_homomorphism_of_group_homomorphism (incl_of_subgroup _)
  begin
    intro r m, induction m with m hm, reflexivity
  end

definition hom_lift [constructor] {K : property M₂} [is_submodule M₂ K] (φ : M₁ →lm M₂)
  (h : Π (m : M₁), φ m ∈ K) : M₁ →lm submodule K :=
lm_homomorphism_of_group_homomorphism (hom_lift (group_homomorphism_of_lm_homomorphism φ) _ h)
  begin
    intro r g, exact subtype_eq (to_respect_smul φ r g)
  end

definition submodule_functor [constructor] {S : property M₁} [is_submodule M₁ S]
  {K : property M₂} [is_submodule M₂ K]
  (φ : M₁ →lm M₂) (h : Π (m : M₁), m ∈ S → φ m ∈ K) : submodule S →lm submodule K :=
hom_lift (φ ∘lm submodule_incl S) (by intro m; exact h m.1 m.2)

definition hom_lift_compose {K : property M₃} [is_submodule M₃ K]
  (φ : M₂ →lm M₃) (h : Π (m : M₂), φ m ∈ K) (ψ : M₁ →lm M₂) :
  hom_lift φ h ∘lm ψ ~ hom_lift (φ ∘lm ψ) proof (λm, h (ψ m)) qed :=
by reflexivity

definition hom_lift_homotopy {K : property M₂} [is_submodule M₂ K] {φ : M₁ →lm M₂}
  {h : Π (m : M₁), φ m ∈ K} {φ' : M₁ →lm M₂}
  {h' : Π (m : M₁), φ' m ∈ K} (p : φ ~ φ') : hom_lift φ h ~ hom_lift φ' h' :=
λg, subtype_eq (p g)

definition incl_smul (S : property M) [is_submodule M S] (r : R) (m : M) (h : S m) :
  r • ⟨m, h⟩ = ⟨_, smul_mem S r h⟩ :> submodule S :=
by reflexivity

definition property_submodule (S₁ S₂ : property M) [is_submodule M S₁] [is_submodule M S₂] :
  property (submodule S₁) := {m | submodule_incl S₁ m ∈ S₂}

definition is_submodule_property_submodule [instance] (S₁ S₂ : property M) [is_submodule M S₁] [is_submodule M S₂] :
  is_submodule (submodule S₁) (property_submodule S₁ S₂) :=
is_submodule.mk
  (mem_property_of (zero_mem S₂))
  (λm n p q, mem_property_of (add_mem S₂ (of_mem_property_of p) (of_mem_property_of q)))
  begin
    intro m r p, induction m with m hm, apply mem_property_of,
    apply smul_mem S₂, exact (of_mem_property_of p)
  end

definition eq_zero_of_mem_property_submodule_trivial [constructor] {S₁ S₂ : property M} [is_submodule M S₁] [is_submodule M S₂]
  (h : Π⦃m⦄, m ∈ S₂ → m = 0) ⦃m : submodule S₁⦄ (Sm : m ∈ property_submodule S₁ S₂) : m = 0 :=
begin
  fapply subtype_eq,
  apply h (of_mem_property_of Sm)
end

definition is_contr_submodule (S : property M) [is_submodule M S] (H : is_contr M) :
  is_contr (submodule S) :=
have is_prop M, from _,
have is_prop (submodule S), from @is_trunc_sigma _ _ _ this _,
is_contr_of_inhabited_prop 0 this

definition submodule_isomorphism [constructor] (S : property M) [is_submodule M S] (h : Πg, g ∈ S) :
  submodule S ≃lm M :=
isomorphism.mk (submodule_incl S) (is_equiv_incl_of_subgroup S h)

definition submodule_isomorphism_submodule [constructor] {S : property M₁} [is_submodule M₁ S]
  {K : property M₂} [is_submodule M₂ K]
  (φ : M₁ ≃lm M₂) (h : Π (m : M₁), m ∈ S ↔ φ m ∈ K) : submodule S ≃lm submodule K :=
lm_isomorphism_of_group_isomorphism
  (subgroup_isomorphism_subgroup (group_isomorphism_of_lm_isomorphism φ) h)
  (by rexact to_respect_smul (submodule_functor φ (λg, iff.mp (h g))))

/- quotient modules -/

definition quotient_module' (S : property M) [is_submodule M S] : AddAbGroup :=
quotient_ab_group S -- (subgroup_rel_of_submodule_rel S)

definition quotient_module_smul [constructor] (S : property M) [is_submodule M S] (r : R) :
  quotient_module' S →a quotient_module' S :=
quotient_ab_group_functor (smul_homomorphism M r) (λg, smul_mem S r)

definition quotient_module_smul_right_distrib (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r + s) n = quotient_module_smul S r n + quotient_module_smul S s n :=
begin
  refine quotient_ab_group_functor_homotopy _ _ _ n ⬝ !quotient_ab_group_functor_mul⁻¹,
  intro m, exact to_smul_right_distrib r s m
end

definition quotient_module_mul_smul' (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r * s) n = (quotient_module_smul S r ∘g quotient_module_smul S s) n :=
begin
  apply eq.symm,
  apply eq.trans (quotient_ab_group_functor_compose _ _ _ _ n),
  apply quotient_ab_group_functor_homotopy,
  intro m, exact eq.symm (to_mul_smul r s m)
end
-- previous proof:
--  refine quotient_ab_group_functor_homotopy _ _ _ n ⬝
--    (quotient_ab_group_functor_compose (quotient_module_smul S r) (quotient_module_smul S s) _ _ n)⁻¹ᵖ,
--  intro m, to_mul_smul r s m

definition quotient_module_mul_smul (r s : R) (n : quotient_module' S) :
  quotient_module_smul S (r * s) n = quotient_module_smul S r (quotient_module_smul S s n) :=
by rexact quotient_module_mul_smul' r s n

definition quotient_module_one_smul (n : quotient_module' S) : quotient_module_smul S (1 : R) n = n :=
begin
  refine quotient_ab_group_functor_homotopy _ _ _ n ⬝ !quotient_ab_group_functor_gid,
  intro m, exact to_one_smul m
end

variable (S)
definition quotient_module (S : property M) [is_submodule M S] : LeftModule R :=
LeftModule_of_AddAbGroup (quotient_module' S) (quotient_module_smul S)
  (λr, homomorphism.addstruct (quotient_module_smul S r))
  quotient_module_smul_right_distrib
  quotient_module_mul_smul
  quotient_module_one_smul

definition quotient_map [constructor] : M →lm quotient_module S :=
lm_homomorphism_of_group_homomorphism (ab_qg_map _) (λr g, idp)

definition quotient_map_eq_zero (m : M) (H : S m) : quotient_map S m = 0 :=
@ab_qg_map_eq_one _ _ _ _ H

definition rel_of_quotient_map_eq_zero (m : M) (H : quotient_map S m = 0) : S m :=
@rel_of_qg_map_eq_one _ _ _ m H

variable {S}
definition respect_smul_quotient_elim [constructor] (φ : M →lm M₂) (H : Π⦃m⦄, m ∈ S → φ m = 0)
  (r : R) (m : quotient_module S) :
  quotient_ab_group_elim (group_homomorphism_of_lm_homomorphism φ) H
    (@has_scalar.smul _ (quotient_module S) _ r m) =
  r • quotient_ab_group_elim (group_homomorphism_of_lm_homomorphism φ) H m :=
begin
  revert m,
  refine @set_quotient.rec_prop _ _ _ (λ x, !is_trunc_eq) _,
  intro m,
  exact to_respect_smul φ r m
end

definition quotient_elim [constructor] (φ : M →lm M₂) (H : Π⦃m⦄, m ∈ S → φ m = 0) :
  quotient_module S →lm M₂ :=
lm_homomorphism_of_group_homomorphism
  (quotient_ab_group_elim (group_homomorphism_of_lm_homomorphism φ) H)
  (respect_smul_quotient_elim φ H)

definition is_prop_quotient_module (S : property M) [is_submodule M S] [H : is_prop M] : is_prop (quotient_module S) :=
begin apply @set_quotient.is_trunc_set_quotient, exact H end

definition is_contr_quotient_module [instance] (S : property M) [is_submodule M S]
  (H : is_contr M) : is_contr (quotient_module S) :=
have is_prop M, from _,
have is_prop (quotient_module S), from @set_quotient.is_trunc_set_quotient _ _ _ this,
is_contr_of_inhabited_prop 0 this

definition rel_of_is_contr_quotient_module (S : property M) [is_submodule M S]
  (H : is_contr (quotient_module S)) (m : M) : S m :=
rel_of_quotient_map_eq_zero S m (@eq_of_is_contr _ H _ _)

definition quotient_module_isomorphism [constructor] (S : property M) [is_submodule M S] (h : Π⦃m⦄, S m → m = 0) :
  quotient_module S ≃lm M :=
(isomorphism.mk (quotient_map S) (is_equiv_ab_qg_map S h))⁻¹ˡᵐ

definition quotient_module_functor [constructor] (φ : M →lm M₂) (h : Πg, g ∈ S → φ g ∈ S₂) :
  quotient_module S →lm quotient_module S₂ :=
quotient_elim (quotient_map S₂ ∘lm φ)
  begin intros m Hm, rexact quotient_map_eq_zero S₂ (φ m) (h m Hm) end

definition quotient_module_isomorphism_quotient_module [constructor] (φ : M ≃lm M₂)
    (h : Πm, m ∈ S ↔ φ m ∈ S₂) : quotient_module S ≃lm quotient_module S₂ :=
lm_isomorphism_of_group_isomorphism
  (quotient_ab_group_isomorphism_quotient_ab_group (group_isomorphism_of_lm_isomorphism φ) h)
  (to_respect_smul (quotient_module_functor φ (λg, iff.mp (h g))))

/- specific submodules -/
definition has_scalar_image (φ : M₁ →lm M₂) ⦃m : M₂⦄ (r : R)
  (h : image φ m) : image φ (r • m) :=
begin
  induction h with m' p,
  apply image.mk (r • m'),
  refine to_respect_smul φ r m' ⬝ ap (λx, r • x) p,
end

definition is_submodule_image [instance] (φ : M₁ →lm M₂) : is_submodule M₂ (image φ) :=
is_submodule.mk
  (show 0 ∈ image (group_homomorphism_of_lm_homomorphism φ),
    begin apply is_subgroup.one_mem, apply is_subgroup_image end)
  (λ g₁ g₂ hg₁ hg₂,
     show g₁ + g₂ ∈ image (group_homomorphism_of_lm_homomorphism φ),
     begin
       apply @is_subgroup.mul_mem,
       apply is_subgroup_image, exact hg₁, exact hg₂
     end)
  (has_scalar_image φ)

/-
definition image_rel [constructor] (φ : M₁ →lm M₂) : submodule_rel M₂ :=
submodule_rel_of_subgroup_rel
  (image_subgroup (group_homomorphism_of_lm_homomorphism φ))
  (has_scalar_image φ)
-/

definition image_trivial (φ : M₁ →lm M₂) [H : is_contr M₁] ⦃m : M₂⦄ (h : m ∈ image φ) : m = 0 :=
begin
  refine image.rec _ h,
  intro x p,
  refine p⁻¹ ⬝ ap φ _ ⬝ to_respect_zero φ,
  apply @is_prop.elim, apply is_trunc_succ, exact H
end

definition image_module [constructor] (φ : M₁ →lm M₂) : LeftModule R := submodule (image φ)

-- unfortunately this is note definitionally equal:
-- definition foo (φ : M₁ →lm M₂) :
--   (image_module φ : AddAbGroup) = image (group_homomorphism_of_lm_homomorphism φ) :=
-- by reflexivity

definition image_lift [constructor] (φ : M₁ →lm M₂) : M₁ →lm image_module φ :=
hom_lift φ (λm, image.mk m idp)

definition is_surjective_image_lift (φ : M₁ →lm M₂) : is_surjective (image_lift φ) :=
begin
  refine total_image.rec _, intro m, exact image.mk m (subtype_eq idp)
end

variables {ψ : M₂ →lm M₃} {φ : M₁ →lm M₂} {θ : M₁ →lm M₃} {ψ' : M₂' →lm M₃'} {φ' : M₁' →lm M₂'}

definition image_elim [constructor] (θ : M₁ →lm M₃) (h : Π⦃g⦄, φ g = 0 → θ g = 0) :
  image_module φ →lm M₃ :=
begin
  fapply homomorphism.mk,
  change Image (group_homomorphism_of_lm_homomorphism φ) → M₃,
  exact image_elim (group_homomorphism_of_lm_homomorphism θ) h,
  split,
  { exact homomorphism.struct (image_elim (group_homomorphism_of_lm_homomorphism θ) _) },
  { intro r, refine @total_image.rec _ _ _ _ (λx, !is_trunc_eq) _, intro g,
    apply to_respect_smul }
end

definition image_elim_compute (h : Π⦃g⦄, φ g = 0 → θ g = 0) :
  image_elim θ h ∘lm image_lift φ ~ θ :=
begin
  reflexivity
end

-- definition image_elim_hom_lift (ψ : M →lm M₂) (h : Π⦃g⦄, φ g = 0 → θ g = 0) :
--   image_elim θ h ∘lm hom_lift ψ _ ~ _ :=
-- begin
--   reflexivity
-- end

definition is_contr_image_module [instance] (φ : M₁ →lm M₂) (H : is_contr M₂) :
  is_contr (image_module φ) :=
is_contr_submodule _ _

definition is_contr_image_module_of_is_contr_dom (φ : M₁ →lm M₂) (H : is_contr M₁) :
  is_contr (image_module φ) :=
is_contr.mk 0
  begin
    have Π(x : image_module φ), is_prop (0 = x), from _,
    apply @total_image.rec,
    exact this,
    intro m,
    have h : is_contr (LeftModule.carrier M₁), from H,
    induction (eq_of_is_contr 0 m), apply subtype_eq,
    exact (to_respect_zero φ)⁻¹
  end

definition image_module_isomorphism [constructor] (φ : M₁ →lm M₂)
  (H : is_surjective φ) : image_module φ ≃lm M₂ :=
submodule_isomorphism _ H

definition has_scalar_kernel (φ : M₁ →lm M₂) ⦃m : M₁⦄ (r : R)
  (p : φ m = 0) : φ (r • m) = 0 :=
begin
  refine to_respect_smul φ r m ⬝ ap (λx, r • x) p ⬝ smul_zero r,
end

definition lm_kernel [reducible] (φ : M₁ →lm M₂) : property M₁ := kernel (group_homomorphism_of_lm_homomorphism φ)

definition is_submodule_kernel [instance] (φ : M₁ →lm M₂) : is_submodule M₁ (lm_kernel φ) :=
is_submodule.mk
  (show 0 ∈ kernel (group_homomorphism_of_lm_homomorphism φ),
    begin apply is_subgroup.one_mem, apply is_subgroup_kernel end)
  (λ g₁ g₂ hg₁ hg₂,
     show g₁ + g₂ ∈ kernel (group_homomorphism_of_lm_homomorphism φ),
       begin apply @is_subgroup.mul_mem, apply is_subgroup_kernel, exact hg₁, exact hg₂ end)
  (has_scalar_kernel φ)

definition kernel_full (φ : M₁ →lm M₂) (H : is_contr M₂) (m : M₁) : m ∈ lm_kernel φ :=
!is_prop.elim

definition kernel_module [reducible] (φ : M₁ →lm M₂) : LeftModule R := submodule (lm_kernel φ)

definition is_contr_kernel_module [instance] (φ : M₁ →lm M₂) (H : is_contr M₁) :
  is_contr (kernel_module φ) :=
is_contr_submodule _ _

definition kernel_module_isomorphism [constructor] (φ : M₁ →lm M₂) (H : is_contr M₂) :
  kernel_module φ ≃lm M₁ :=
submodule_isomorphism _ (kernel_full φ _)

definition homology_quotient_property (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) :
  property (kernel_module ψ) :=
property_submodule (lm_kernel ψ) (image (homomorphism_fn φ))

definition is_submodule_homology_property [instance] (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) :
  is_submodule (kernel_module ψ) (homology_quotient_property ψ φ) :=
(is_submodule_property_submodule _ (image φ))

definition homology (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) : LeftModule R :=
quotient_module (homology_quotient_property ψ φ)

definition homology.mk (φ : M₁ →lm M₂) (m : M₂) (h : ψ m = 0) : homology ψ φ :=
quotient_map (homology_quotient_property ψ φ) ⟨m, h⟩

definition homology_eq0 {m : M₂} {hm : ψ m = 0} (h : image φ m) :
  homology.mk φ m hm = 0 :=
ab_qg_map_eq_one _ h

definition homology_eq0' {m : M₂} {hm : ψ m = 0} (h : image φ m):
  homology.mk φ m hm = homology.mk φ 0 (to_respect_zero ψ) :=
ab_qg_map_eq_one _ h

definition homology_eq {m n : M₂} {hm : ψ m = 0} {hn : ψ n = 0} (h : image φ (m - n)) :
  homology.mk φ m hm = homology.mk φ n hn :=
eq_of_sub_eq_zero (homology_eq0 h)

definition homology_elim [constructor] (θ : M₂ →lm M) (H : Πm, θ (φ m) = 0) :
  homology ψ φ →lm M :=
quotient_elim (θ ∘lm submodule_incl _)
  begin
    intro m x,
    induction m with m h,
    esimp at *,
    induction x with v,
    exact ap θ p⁻¹ ⬝ H v -- m'
  end

definition is_contr_homology [instance] (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) (H : is_contr M₂) :
  is_contr (homology ψ φ) :=
is_contr_quotient_module _ (is_contr_kernel_module _ _)

definition homology_isomorphism [constructor] (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂)
  (H₁ : is_contr M₁) (H₃ : is_contr M₃) : homology ψ φ ≃lm M₂ :=
(quotient_module_isomorphism (homology_quotient_property ψ φ)
  (eq_zero_of_mem_property_submodule_trivial (image_trivial _))) ⬝lm (kernel_module_isomorphism ψ _)

definition homology_functor [constructor] (α₁ : M₁ →lm M₁') (α₂ : M₂ →lm M₂') (α₃ : M₃ →lm M₃')
  (p : hsquare ψ ψ' α₂ α₃) (q : hsquare φ φ' α₁ α₂) : homology ψ φ →lm homology ψ' φ' :=
begin
  fapply quotient_module_functor,
  { apply submodule_functor α₂, intro m pm, refine (p m)⁻¹ ⬝ ap α₃ pm ⬝ to_respect_zero α₃ },
  { intro m pm, induction pm with m' pm',
    refine image.mk (α₁ m') ((q m')⁻¹ ⬝ _), exact ap α₂ pm' }
end

definition homology_isomorphism_homology [constructor] (α₁ : M₁ ≃lm M₁') (α₂ : M₂ ≃lm M₂') (α₃ : M₃ ≃lm M₃')
  (p : hsquare ψ ψ' α₂ α₃) (q : hsquare φ φ' α₁ α₂) : homology ψ φ ≃lm homology ψ' φ' :=
begin
  fapply quotient_module_isomorphism_quotient_module,
  { fapply submodule_isomorphism_submodule α₂, intro m,
    exact iff.intro (λpm, (p m)⁻¹ ⬝ ap α₃ pm ⬝ to_respect_zero α₃)
            (λpm, inj (equiv_of_isomorphism α₃) (p m ⬝ pm ⬝ (to_respect_zero α₃)⁻¹)) },
  { intro m, apply iff.intro,
    { intro pm, induction pm with m' pm', refine image.mk (α₁ m') ((q m')⁻¹ ⬝ _), exact ap α₂ pm' },
    { intro pm, induction pm with m' pm', refine image.mk (α₁⁻¹ˡᵐ m') _,
      refine (hvinverse' (equiv_of_isomorphism α₁) (equiv_of_isomorphism α₂) q m')⁻¹ ⬝ _,
      exact ap α₂⁻¹ˡᵐ pm' ⬝ to_left_inv (equiv_of_isomorphism α₂) m.1 }}
end

definition ker_in_im_of_is_contr_homology (ψ : M₂ →lm M₃) {φ : M₁ →lm M₂}
  (H₁ : is_contr (homology ψ φ)) {m : M₂} (p : ψ m = 0) : image φ m :=
rel_of_is_contr_quotient_module _ H₁ ⟨m, p⟩

definition is_embedding_of_is_contr_homology_of_constant {ψ : M₂ →lm M₃} (φ : M₁ →lm M₂)
  (H₁ : is_contr (homology ψ φ)) (H₂ : Πm, φ m = 0) : is_embedding ψ :=
begin
  apply to_is_embedding_homomorphism (group_homomorphism_of_lm_homomorphism ψ),
  intro m p, note H := rel_of_is_contr_quotient_module _ H₁ ⟨m, p⟩,
  induction H with n q,
  exact q⁻¹ ⬝ H₂ n
end

definition is_embedding_of_is_contr_homology_of_is_contr {ψ : M₂ →lm M₃} (φ : M₁ →lm M₂)
  (H₁ : is_contr (homology ψ φ)) (H₂ : is_contr M₁) : is_embedding ψ :=
is_embedding_of_is_contr_homology_of_constant φ H₁
  (λm, ap φ (@eq_of_is_contr _ H₂ _ _) ⬝ respect_zero φ)

definition is_surjective_of_is_contr_homology_of_constant (ψ : M₂ →lm M₃) {φ : M₁ →lm M₂}
  (H₁ : is_contr (homology ψ φ)) (H₂ : Πm, ψ m = 0) : is_surjective φ :=
λm, ker_in_im_of_is_contr_homology ψ H₁ (H₂ m)

definition is_surjective_of_is_contr_homology_of_is_contr (ψ : M₂ →lm M₃) {φ : M₁ →lm M₂}
  (H₁ : is_contr (homology ψ φ)) (H₂ : is_contr M₃) : is_surjective φ :=
is_surjective_of_is_contr_homology_of_constant ψ H₁ (λm, @eq_of_is_contr _ H₂ _ _)

definition homology_isomorphism_kernel_module (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂)
  (H : Πm, image φ m → m = 0) : homology ψ φ ≃lm kernel_module ψ :=
begin
  apply quotient_module_isomorphism, intro m h, apply subtype_eq, apply H, exact h
end

definition cokernel_module (φ : M₁ →lm M₂) : LeftModule R :=
quotient_module (image φ)

definition homology_isomorphism_cokernel_module (ψ : M₂ →lm M₃) (φ : M₁ →lm M₂) (H : Πm, ψ m = 0) :
  homology ψ φ ≃lm cokernel_module φ :=
quotient_module_isomorphism_quotient_module
  (submodule_isomorphism _ H)
  begin intro m, reflexivity end

open chain_complex fin nat
definition LES_of_SESs.{u} {N : succ_str} (A B C : N → LeftModule.{_ u} R) (φ : Πn, A n →lm B n)
  (ses : Πn : N, short_exact_mod (cokernel_module (φ (succ_str.S n))) (C n) (kernel_module (φ n))) :
  chain_complex.{_ u} (stratified N 2) :=
begin
  fapply chain_complex.mk,
  { intro x, apply @pSet_of_LeftModule R,
    induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
    { /-k≥3-/ exfalso, apply lt_le_antisymm H, apply le_add_left},
    { /-k=0-/ exact B n },
    { /-k=1-/ exact A n },
    { /-k=2-/ exact C n }},
  { intro x, apply @pmap_of_homomorphism R,
    induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
    { /-k≥3-/ exfalso, apply lt_le_antisymm H, apply le_add_left},
    { /-k=0-/ exact φ n },
    { /-k=1-/ exact submodule_incl _ ∘lm short_exact_mod.g (ses n) },
    { /-k=2-/ change B (succ_str.S n) →lm C n, exact short_exact_mod.f (ses n) ∘lm !quotient_map }},
  { intros x m, induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
    { exfalso, apply lt_le_antisymm H, apply le_add_left},
    { exact (short_exact_mod.g (ses n) m).2 },
    { exact ap pr1 (is_short_exact.im_in_ker (short_exact_mod.h (ses n)) (quotient_map _ m)) },
    { exact ap (short_exact_mod.f (ses n)) (quotient_map_eq_zero _ _ (image.mk m idp)) ⬝
            to_respect_zero (short_exact_mod.f (ses n)) }}
end

definition is_exact_LES_of_SESs.{u} {N : succ_str} (A B C : N → LeftModule.{_ u} R) (φ : Πn, A n →lm B n)
  (ses : Πn : N, short_exact_mod (cokernel_module (φ (succ_str.S n))) (C n) (kernel_module (φ n))) :
  is_exact (LES_of_SESs A B C φ ses) :=
begin
  intros x m p, induction x with n k, induction k with k H, do 3 (cases k with k; rotate 1),
  { exfalso, apply lt_le_antisymm H, apply le_add_left},
  { induction is_short_exact.is_surj (short_exact_mod.h (ses n)) ⟨m, p⟩ with m' q,
    exact image.mk m' (ap pr1 q) },
  { induction is_short_exact.ker_in_im (short_exact_mod.h (ses n)) m (subtype_eq p) with m' q,
    induction m' using set_quotient.rec_prop with m',
    exact image.mk m' q },
  { apply rel_of_quotient_map_eq_zero (image (φ (succ_str.S n))) m,
    apply @is_injective_of_is_embedding _ _ _ (is_short_exact.is_emb (short_exact_mod.h (ses n))),
    exact p ⬝ (to_respect_zero (short_exact_mod.f (ses n)))⁻¹ }
end

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
