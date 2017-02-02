
import algebra.group_theory ..move_to_lib
open pi pointed algebra group eq equiv is_trunc

namespace group

  /- Group of functions whose codomain is a group -/
  definition group_arrow [instance] (A B : Type) [group B] : group (A → B) :=
  begin
    fapply group.mk,
    { apply is_trunc_arrow },
    { intro f g a, exact f a * g a },
    { intros, apply eq_of_homotopy, intro a, apply mul.assoc },
    { intro a, exact 1 },
    { intros, apply eq_of_homotopy, intro a, apply one_mul },
    { intros, apply eq_of_homotopy, intro a, apply mul_one },
    { intro f a, exact (f a)⁻¹ },
    { intros, apply eq_of_homotopy, intro a, apply mul.left_inv }
  end

  definition Group_arrow (A : Type) (G : Group) : Group :=
  Group.mk (A → G) _

  definition ab_group_arrow [instance] (A B : Type) [ab_group B] : ab_group (A → B) :=
  ⦃ab_group, group_arrow A B,
     mul_comm := by intros; apply eq_of_homotopy; intro a; apply mul.comm⦄

  definition AbGroup_arrow (A : Type) (G : AbGroup) : AbGroup :=
  AbGroup.mk (A → G) _

  definition pgroup_ppmap [instance] (A B : Type*) [pgroup B] : pgroup (ppmap A B) :=
  begin
    fapply pgroup.mk,
    { apply is_trunc_pmap },
    { intro f g, apply pmap.mk (λa, f a * g a),
      exact ap011 mul (respect_pt f) (respect_pt g) ⬝ !one_mul },
    { intros, apply pmap_eq_of_homotopy, intro a, apply mul.assoc },
    { intro f, apply pmap.mk (λa, (f a)⁻¹), apply inv_eq_one, apply respect_pt },
    { intros, apply pmap_eq_of_homotopy, intro a, apply one_mul },
    { intros, apply pmap_eq_of_homotopy, intro a, apply mul_one },
    { intros, apply pmap_eq_of_homotopy, intro a, apply mul.left_inv }
  end

  definition Group_pmap (A : Type*) (G : Group) : Group :=
  Group_of_pgroup (ppmap A (pType_of_Group G))

  definition AbGroup_pmap (A : Type*) (G : AbGroup) : AbGroup :=
  AbGroup.mk (A →* pType_of_Group G)
  ⦃ ab_group, Group.struct (Group_pmap A G),
    mul_comm := by intro f g; apply pmap_eq_of_homotopy; intro a; apply mul.comm ⦄

  definition Group_pmap_homomorphism [constructor] {A A' : Type*} (f : A' →* A) (G : AbGroup) :
    Group_pmap A G →g Group_pmap A' G :=
  begin
    fapply homomorphism.mk,
    { intro g, exact g ∘* f},
    { intro g h, apply pmap_eq_of_homotopy, intro a, reflexivity }
  end

end group
