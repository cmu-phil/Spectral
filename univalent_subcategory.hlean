import homotopy.sphere2 algebra.category.functor.attributes

open eq pointed sigma is_equiv equiv fiber algebra group is_trunc function prod prod.ops iso functor

namespace category

section univ_subcat
  parameters {C : Precategory} {D : Category} (F : functor C D) (p : is_embedding  F) (q : fully_faithful F)
  variables  {a b : carrier C}
  include p q

  definition eq_equiv_iso_of_fully_faithful : a = b ≃ a ≅ b :=
    equiv.mk !ap !p                          -- a = b ≃ F a = F b
    ⬝e equiv.mk iso_of_eq !iso_of_path_equiv -- F a = F b ≃ F a ≅ F b
    ⬝e equiv.symm !iso_equiv_F_iso_F         -- F a ≅ F b ≃ a ≅ b

  definition eq_equiv_iso_of_fully_faithful_homot : @eq_equiv_iso_of_fully_faithful a b ~ iso_of_eq :=
  begin
    intro r,
    esimp [eq_equiv_iso_of_fully_faithful],
    refine _ ⬝ left_inv (iso_equiv_F_iso_F F _ _) _,
    apply ap (inv (to_fun !iso_equiv_F_iso_F)),
    apply symm,
    induction r,
    apply respect_refl
  end

  definition is_univalent_domain_of_fully_faithful_embedding : is_univalent C :=
  begin
    intros,
    exact homotopy_closed eq_equiv_iso_of_fully_faithful eq_equiv_iso_of_fully_faithful_homot _
  end
end univ_subcat

  definition precategory_Group.{u} [instance] [constructor] : precategory.{u+1 u} Group :=
  begin
    fapply precategory.mk,
    { exact λG H, G →g H },
    { exact _ },
    { exact λG H K ψ φ, ψ ∘g φ },
    { exact λG, gid G },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp }
  end

  definition precategory_AbGroup.{u} [instance] [constructor] : precategory.{u+1 u} AbGroup :=
  begin
    fapply precategory.mk,
    { exact λG H, G →g H },
    { exact _ },
    { exact λG H K ψ φ, ψ ∘g φ },
    { exact λG, gid G },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp },
    { intros, apply homomorphism_eq, esimp }
  end

  definition Group_is_iso_of_is_equiv {G H : Group} (φ : G →g H) (H : is_equiv (group_fun φ)) :
    is_iso φ :=
  begin
    fconstructor,
    { exact (isomorphism.mk φ H)⁻¹ᵍ },
    { apply homomorphism_eq, rexact left_inv φ },
    { apply homomorphism_eq, rexact right_inv φ }
  end

  definition Group_is_equiv_of_is_iso {G H : Group} (φ : G ⟶ H) (Hφ : is_iso φ) :
    is_equiv (group_fun φ) :=
  begin
    fapply adjointify,
    { exact group_fun φ⁻¹ʰ },
    { note p := right_inverse φ, exact ap010 group_fun p },
    { note p := left_inverse φ,  exact ap010 group_fun p }
  end

  definition Group_iso_equiv (G H : Group) : (G ≅ H) ≃ (G ≃g H) :=
  begin
    fapply equiv.MK,
    { intro φ, induction φ with φ φi, constructor, exact Group_is_equiv_of_is_iso φ _ },
    { intro v, induction v with φ φe, constructor, exact Group_is_iso_of_is_equiv φ _ },
    { intro v, induction v with φ φe, apply isomorphism_eq, reflexivity },
    { intro φ, induction φ with φ φi, apply iso_eq, reflexivity }
  end

  definition Group_props.{u} {A : Type.{u}} (v : (A → A → A) × (A → A) × A) : Prop.{u} :=
  begin
    induction v with m v, induction v with i o,
    fapply trunctype.mk,
    { exact is_set A × (Πa, m a o = a) × (Πa, m o a = a) × (Πa b c, m (m a b) c = m a (m b c)) ×
      (Πa, m (i a) a = o) },
    { apply is_trunc_of_imp_is_trunc, intro v, induction v with H v,
      have is_prop (Πa, m a o = a), from _,
      have is_prop (Πa, m o a = a), from _,
      have is_prop (Πa b c, m (m a b) c = m a (m b c)), from _,
      have is_prop (Πa, m (i a) a = o), from _,
      apply is_trunc_prod }
  end

  definition AbGroup_props.{u} {A : Type.{u}} (v : (A → A → A) × (A → A) × A) : Prop.{u} :=
  begin
    induction v with m v, induction v with i o,
    fapply trunctype.mk,
    { exact is_set A × (Πa, m a o = a) × (Πa, m o a = a) × (Πa b c, m (m a b) c = m a (m b c)) ×
      (Πa, m (i a) a = o) × (Πa b, m a b = m b a)},
    { apply is_trunc_of_imp_is_trunc, intro v, induction v with H v,
      have is_prop (Πa, m a o = a), from _,
      have is_prop (Πa, m o a = a), from _,
      have is_prop (Πa b c, m (m a b) c = m a (m b c)), from _,
      have is_prop (Πa, m (i a) a = o), from _,
      have is_prop (Πa b, m a b = m b a), from _,
      apply is_trunc_prod }
  end

definition AbGroup_sigma.{u} : AbGroup.{u} ≃ Σ A : Type.{u}, ab_group A :=
begin repeat (assumption | induction a with a b | intro a | fconstructor) end

definition Group_sigma.{u} : Group.{u} ≃ Σ A : Type.{u}, group A :=
begin
fconstructor, exact λ a, dpair (Group.carrier a) (Group.struct' a),
repeat (assumption | induction a with a b | intro a | fconstructor)
end

  definition group.sigma_char.{u} (A : Type) :
    group.{u} A ≃ Σ (v : (A → A → A) × (A → A) × A), Group_props v :=
  begin
    fapply equiv.MK,
    {intro g, induction g with m s ma o om mo i mi,
      repeat (fconstructor; do 2 try assumption), },
    {intro v, induction v with x v, repeat induction x with y x,
      repeat induction v with x v, constructor, repeat assumption },
    { intro, repeat induction b with b x, induction x,
      repeat induction x_1 with v x_1, reflexivity },
    { intro v, repeat induction v with x v, reflexivity },
  end

definition Group.sigma_char2.{u} :
           Group.{u} ≃ Σ(A : Type.{u}) (v : (A → A → A) × (A → A) × A), Group_props v :=
Group_sigma ⬝e sigma_equiv_sigma_right group.sigma_char

  definition ab_group.sigma_char.{u} (A : Type) :
    ab_group.{u} A ≃ Σ (v : (A → A → A) × (A → A) × A), AbGroup_props v :=
  begin
    fapply equiv.MK,
    {intro g, induction g with m s ma o om mo i mi,
      repeat (fconstructor; do 2 try assumption), },
    {intro v, induction v with x v, repeat induction x with y x,
      repeat induction v with x v, constructor, repeat assumption },
    { intro, repeat induction b with b x, induction x,
      repeat induction x_1 with v x_1, reflexivity },
    { intro v, repeat induction v with x v, reflexivity },
  end

  definition AbGroup_Group_props {A : Type} (v : (A → A → A) × (A → A) × A) :
    AbGroup_props v ≃ Group_props v × ∀ a b, v.1 a b = v.1 b a :=
  begin
    fapply equiv.MK, induction v with m v, induction v with i e,
    intro,  fconstructor, repeat induction a with b a, repeat (fconstructor; assumption), assumption,
    exact a.2.2.2.2.2, intro, induction a, repeat induction v with b v, repeat induction a with b a,
repeat (fconstructor; assumption), assumption, intro b,
    assert H : is_prop (Group_props v × ∀ a b, v.1 a b = v.1 b a),
    apply is_trunc_prod, assert K : is_set A, induction b, induction v, induction a_1, induction a_2_1, assumption,
    exact _, apply is_prop.elim, intro, apply is_prop.elim,
  end

open sigma.ops

definition sigma_prod_equiv_sigma_sigma {A} {B C : A→Type} : (Σa, B a × C a) ≃ Σ p : (Σa, B a), C p.1 :=
sigma_equiv_sigma_right (λa, !sigma.equiv_prod⁻¹ᵉ) ⬝e !sigma_assoc_equiv

definition ab_group_equiv_group_comm (A : Type) : ab_group A ≃ Σ (g : group A), ∀ a b : A, a * b = b * a :=
begin
refine !ab_group.sigma_char ⬝e _,
refine sigma_equiv_sigma_right AbGroup_Group_props ⬝e _,
refine sigma_prod_equiv_sigma_sigma ⬝e _,
apply equiv.symm, apply sigma_equiv_sigma !group.sigma_char, intros,
induction a, reflexivity
end

  section
  local attribute group.to_has_mul group.to_has_inv [coercion]

  theorem inv_eq_of_mul_eq {A : Type} (G H : group A) (p : @mul A G ~2 @mul A H) :
    @inv A G ~ @inv A H :=
  begin
    have foo : Π(g : A), @inv A G g = (@inv A G g * g) * @inv A H g,
      from λg, !mul_inv_cancel_right⁻¹,
    cases G with Gs Gm Gh1 G1 Gh2 Gh3 Gi Gh4,
    cases H with Hs Hm Hh1 H1 Hh2 Hh3 Hi Hh4,
    change Gi ~ Hi, intro g, have p' : Gm ~2 Hm, from p,
    calc
      Gi g = Hm (Hm (Gi g) g) (Hi g) : foo
       ... = Hm (Gm (Gi g) g) (Hi g) : by rewrite p'
       ... = Hm G1 (Hi g) : by rewrite Gh4
       ... = Gm G1 (Hi g) : by rewrite p'
       ... = Hi g : Gh2
  end

  theorem one_eq_of_mul_eq {A : Type} (G H : group A)
    (p : @mul A (group.to_has_mul G) ~2 @mul A (group.to_has_mul H)) :
    @one A (group.to_has_one G) = @one A (group.to_has_one H) :=
  begin
    cases G with Gm Gs Gh1 G1 Gh2 Gh3 Gi Gh4,
    cases H with Hm Hs Hh1 H1 Hh2 Hh3 Hi Hh4,
    exact (Hh2 G1)⁻¹ ⬝ (p H1 G1)⁻¹ ⬝ Gh3 H1,
  end
  end

  definition group_of_Group_props.{u} {A : Type.{u}} {m : A → A → A} {i : A → A} {o : A}
    (H : Group_props (m, (i, o))) : group A :=
  ⦃group, mul := m, inv := i, one := o, is_set_carrier := H.1,
    mul_one := H.2.1, one_mul := H.2.2.1, mul_assoc := H.2.2.2.1, mul_left_inv := H.2.2.2.2⦄

  theorem Group_eq_equiv_lemma2 {A : Type} {m m' : A → A → A} {i i' : A → A} {o o' : A}
    (H : Group_props (m, (i, o))) (H' : Group_props (m', (i', o'))) :
    (m, (i, o)) = (m', (i', o')) ≃ (m ~2 m') :=
  begin
    have is_set A, from pr1 H,
    refine equiv_of_is_prop _ _ _ _,
    { intro p, exact apd100 (eq_pr1 p)},
    { intro p, apply prod_eq (eq_of_homotopy2 p),
      apply prod_eq: esimp [Group_props] at *; esimp,
      { apply eq_of_homotopy,
        exact inv_eq_of_mul_eq (group_of_Group_props H) (group_of_Group_props H') p },
      { exact one_eq_of_mul_eq (group_of_Group_props H) (group_of_Group_props H') p }}
  end

  open Group

  theorem Group_eq_equiv_lemma {G H : Group}
    (p : (sigma_char2 G).1 = (sigma_char2 H).1) :
    ((sigma_char2 G).2 =[p] (sigma_char2 H).2) ≃
    (is_mul_hom (equiv_of_eq (proof p qed : Group.carrier G = Group.carrier H))) :=
  begin
    refine !sigma_pathover_equiv_of_is_prop ⬝e _,
    induction G with G g, induction H with H h,
    esimp [sigma_char2] at p,
esimp [sigma_functor] at p, esimp [Group_sigma] at *,
induction p,
    refine !pathover_idp ⬝e _,
    induction g with s m ma o om mo i mi, induction h with σ μ μa ε εμ με ι μι,
    exact Group_eq_equiv_lemma2 (sigma_char2 (Group.mk G (group.mk s m ma o om mo i mi))).2.2
                                (sigma_char2 (Group.mk G (group.mk σ μ μa ε εμ με ι μι))).2.2
  end

  definition isomorphism.sigma_char (G H : Group) : (G ≃g H) ≃ Σ(e : G ≃ H), is_mul_hom e :=
  begin
    fapply equiv.MK,
    { intro φ, exact ⟨equiv_of_isomorphism φ, to_respect_mul φ⟩ },
    { intro v, induction v with e p, exact isomorphism_of_equiv e p },
    { intro v, induction v with e p, induction e, reflexivity },
    { intro φ, induction φ with φ H, induction φ, reflexivity },
  end

  definition Group_eq_equiv (G H : Group) : G = H ≃ (G ≃g H) :=
  begin
    refine (eq_equiv_fn_eq sigma_char2 G H) ⬝e _,
    refine !sigma_eq_equiv ⬝e _,
    refine sigma_equiv_sigma_right Group_eq_equiv_lemma ⬝e _,
    transitivity (Σ(e : (sigma_char2 G).1 ≃ (sigma_char2 H).1),
      @is_mul_hom _ _ _ _ (to_fun e)), apply sigma_ua,
    exact !isomorphism.sigma_char⁻¹ᵉ
  end

  definition to_fun_Group_eq_equiv {G H : Group} (p : G = H)
    : Group_eq_equiv G H p ~ isomorphism_of_eq p :=
  begin induction p, reflexivity end

  definition Group_eq2 {G H : Group} {p q : G = H}
    (r : isomorphism_of_eq p ~ isomorphism_of_eq q) : p = q :=
  begin
    apply inj (Group_eq_equiv G H),
    apply isomorphism_eq,
    intro g, refine to_fun_Group_eq_equiv p g ⬝ r g ⬝ (to_fun_Group_eq_equiv q g)⁻¹,
  end

  definition Group_eq_equiv_Group_iso (G₁ G₂ : Group) : G₁ = G₂ ≃ G₁ ≅ G₂ :=
  Group_eq_equiv G₁ G₂ ⬝e (Group_iso_equiv G₁ G₂)⁻¹ᵉ

  definition category_Group.{u} : category Group.{u} :=
  category.mk precategory_Group
  begin
    intro G H,
    apply is_equiv_of_equiv_of_homotopy (Group_eq_equiv_Group_iso G H),
    intro p, induction p, fapply iso_eq, apply homomorphism_eq, reflexivity
  end

definition AbGroup_to_Group [constructor] : functor (Precategory.mk AbGroup _)
                                                    (Category.mk Group category_Group)
:= mk (λ x : AbGroup, (x : Group)) (λ a b x, x) (λ x, rfl) begin intros, reflexivity end


definition is_set_group (X : Type) : is_set (group X) :=
begin
apply is_trunc_of_imp_is_trunc, intros, assert H : is_set X, exact @group.is_set_carrier X a, clear a,
exact is_trunc_equiv_closed_rev _ !group.sigma_char _
end

definition ab_group_to_group (A  : Type) (g : ab_group A) : group A := _

definition group_comm_to_group (A : Type) : (Σ g : group A, ∀ (a b : A), a*b = b*a) → group A := pr1

definition is_embedding_group_comm_to_group (A : Type) : is_embedding (group_comm_to_group A) :=
begin
unfold group_comm_to_group,
intros, induction a,
assert H : is_set A, induction a, assumption,
assert H :is_set (group A), apply is_set_group,
induction a', fconstructor, intros, apply sigma_eq,
 apply is_prop.elimo, intro, esimp at *, assumption, intros,
 apply is_prop.elim, intros, apply is_prop.elim, intros, apply is_prop.elim
end

definition ab_group_to_group_homot (A : Type) :
  @ab_group_to_group A ~ group_comm_to_group A ∘ ab_group_equiv_group_comm A :=
begin intro, induction x, reflexivity end

definition is_embedding_ab_group_to_group (A : Type) : is_embedding (@ab_group_to_group A) :=
begin
apply is_embedding_homotopy_closed_rev (ab_group_to_group_homot A), apply is_embedding_compose,
exact is_embedding_group_comm_to_group A, apply is_embedding_of_is_equiv
 end

definition is_embedding_total_of_is_embedding_fiber {A} {B C : A → Type} {f : Π a, B a → C a}
  : (∀ a, is_embedding (f a)) → is_embedding (total f) :=
begin
intro e, fapply is_embedding_of_is_prop_fiber, intro p, induction p with a c,
assert H : (fiber (total f) ⟨a, c⟩)≃ fiber (f a) c,
apply fiber_total_equiv,
assert H2 : is_prop (fiber (f a) c),
apply is_prop_fiber_of_is_embedding,
exact is_trunc_equiv_closed -1 (H⁻¹ᵉ) _
end

definition AbGroup_to_Group_homot : AbGroup_to_Group ~ Group_sigma⁻¹ ∘ total ab_group_to_group ∘ AbGroup_sigma :=
begin intro g, induction g, reflexivity end

definition is_embedding_AbGroup_to_Group : is_embedding AbGroup_to_Group :=
begin
apply is_embedding_homotopy_closed_rev AbGroup_to_Group_homot,
apply is_embedding_compose,
apply is_embedding_of_is_equiv,
apply is_embedding_compose,
apply is_embedding_total_of_is_embedding_fiber is_embedding_ab_group_to_group,
apply is_embedding_of_is_equiv
end

definition is_univalent_AbGroup : is_univalent precategory_AbGroup :=
begin
apply is_univalent_domain_of_fully_faithful_embedding AbGroup_to_Group is_embedding_AbGroup_to_Group, intros, apply is_equiv_id
end

definition category_AbGroup : category AbGroup := category.mk precategory_AbGroup is_univalent_AbGroup

definition Grp.{u} [constructor] : Category := category.Mk Group.{u} category_Group
definition AbGrp [constructor] : Category := category.Mk AbGroup category_AbGroup

end category
