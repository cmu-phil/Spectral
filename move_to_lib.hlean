-- definitions, theorems and attributes which should be moved to files in the HoTT library

import homotopy.sphere2 homotopy.cofiber homotopy.wedge hit.prop_trunc hit.set_quotient eq2 types.pointed2

open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc pi group
     is_trunc function sphere unit prod bool

namespace eq

  definition apd10_prepostcompose_nondep {A B C D : Type} (h : C → D) {g g' : B → C} (p : g = g')
    (f : A → B) (a : A) : apd10 (ap (λg a, h (g (f a))) p) a = ap h (apd10 p (f a)) :=
  begin induction p, reflexivity end

  definition apd10_prepostcompose {A B : Type} {C : B → Type} {D : A → Type}
    (f : A → B) (h : Πa, C (f a) → D a) {g g' : Πb, C b}
    (p : g = g') (a : A) :
    apd10 (ap (λg a, h a (g (f a))) p) a = ap (h a) (apd10 p (f a)) :=
  begin induction p, reflexivity end

  definition eq.rec_to {A : Type} {a₀ : A} {P : Π⦃a₁⦄, a₀ = a₁ → Type}
    {a₁ : A} (p₀ : a₀ = a₁) (H : P p₀) ⦃a₂ : A⦄ (p : a₀ = a₂) : P p :=
  begin
    induction p₀, induction p, exact H
  end

  definition eq.rec_to2 {A : Type} {P : Π⦃a₀ a₁⦄, a₀ = a₁ → Type}
    {a₀ a₀' a₁' : A} (p' : a₀' = a₁') (p₀ : a₀ = a₀') (H : P p') ⦃a₁ : A⦄ (p : a₀ = a₁) : P p :=
  begin
   induction p₀, induction p', induction p, exact H
  end

  definition eq.rec_right_inv {A : Type} (f : A ≃ A) {P : Π⦃a₀ a₁⦄, f a₀ = a₁ → Type}
    (H : Πa, P (right_inv f a)) ⦃a₀ a₁ : A⦄ (p : f a₀ = a₁) : P p :=
  begin
    revert a₀ p, refine equiv_rect f⁻¹ᵉ _ _,
    intro a₀ p, exact eq.rec_to (right_inv f a₀) (H a₀) p,
  end

  definition eq.rec_equiv {A B : Type} {a₀ : A} (f : A ≃ B) {P : Π{a₁}, f a₀ = f a₁ → Type}
    (H : P (idpath (f a₀))) ⦃a₁ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    assert qr : Σ(q : a₀ = a₁), ap f q = p,
    { exact ⟨eq_of_fn_eq_fn f p, ap_eq_of_fn_eq_fn' f p⟩ },
    cases qr with q r, apply transport P r, induction q, exact H
  end

  definition eq.rec_equiv_symm {A B : Type} {a₁ : A} (f : A ≃ B) {P : Π{a₀}, f a₀ = f a₁ → Type}
    (H : P (idpath (f a₁))) ⦃a₀ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    assert qr : Σ(q : a₀ = a₁), ap f q = p,
    { exact ⟨eq_of_fn_eq_fn f p, ap_eq_of_fn_eq_fn' f p⟩ },
    cases qr with q r, apply transport P r, induction q, exact H
  end

  definition eq.rec_equiv_to_same {A B : Type} {a₀ : A} (f : A ≃ B) {P : Π{a₁}, f a₀ = f a₁ → Type}
    ⦃a₁' : A⦄ (p' : f a₀ = f a₁') (H : P p') ⦃a₁ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    revert a₁' p' H a₁ p,
    refine eq.rec_equiv f _,
    exact eq.rec_equiv f
  end

  definition eq.rec_equiv_to {A A' B : Type} {a₀ : A} (f : A ≃ B) (g : A' ≃ B)
    {P : Π{a₁}, f a₀ = g a₁ → Type}
    ⦃a₁' : A'⦄ (p' : f a₀ = g a₁') (H : P p') ⦃a₁ : A'⦄ (p : f a₀ = g a₁) : P p :=
  begin
    assert qr : Σ(q : g⁻¹ (f a₀) = a₁), (right_inv g (f a₀))⁻¹ ⬝ ap g q = p,
    { exact ⟨eq_of_fn_eq_fn g (right_inv g (f a₀) ⬝ p),
             whisker_left _ (ap_eq_of_fn_eq_fn' g _) ⬝ !inv_con_cancel_left⟩ },
    assert q'r' : Σ(q' : g⁻¹ (f a₀) = a₁'), (right_inv g (f a₀))⁻¹ ⬝ ap g q' = p',
    { exact ⟨eq_of_fn_eq_fn g (right_inv g (f a₀) ⬝ p'),
             whisker_left _ (ap_eq_of_fn_eq_fn' g _) ⬝ !inv_con_cancel_left⟩ },
    induction qr with q r, induction q'r' with q' r',
    induction q, induction q',
    induction r, induction r',
    exact H
  end

  definition eq.rec_grading {A A' B : Type} {a : A} (f : A ≃ B) (g : A' ≃ B)
    {P : Π{b}, f a = b → Type}
    {a' : A'} (p' : f a = g a') (H : P p') ⦃b : B⦄ (p : f a = b) : P p :=
  begin
    revert b p, refine equiv_rect g _ _,
    exact eq.rec_equiv_to f g p' H
  end

  definition eq.rec_grading_unbased {A B B' C : Type} (f : A ≃ B) (g : B ≃ C) (h : B' ≃ C)
    {P : Π{b c}, g b = c → Type}
    {a' : A} {b' : B'} (p' : g (f a') = h b') (H : P p') ⦃b : B⦄ ⦃c : C⦄ (q : f a' = b)
    (p : g b = c) : P p :=
  begin
    induction q, exact eq.rec_grading (f ⬝e g) h p' H p
  end

  -- definition homotopy_group_homomorphism_pinv (n : ℕ) {A B : Type*} (f : A ≃* B) :
  --   π→g[n+1] f⁻¹ᵉ* ~ (homotopy_group_isomorphism_of_pequiv n f)⁻¹ᵍ :=
  -- begin
  --   -- refine ptrunc_functor_phomotopy 0 !apn_pinv ⬝hty _,
  --   -- intro x, esimp,
  -- end

  -- definition natural_square_tr_eq {A B : Type} {a a' : A} {f g : A → B}
  --   (p : f ~ g) (q : a = a') : natural_square p q = square_of_pathover (apd p q) :=
  -- idp

  lemma homotopy_group_isomorphism_of_ptrunc_pequiv {A B : Type*}
    (n k : ℕ) (H : n+1 ≤[ℕ] k) (f : ptrunc k A ≃* ptrunc k B) : πg[n+1] A ≃g πg[n+1] B :=
  (ghomotopy_group_ptrunc_of_le H A)⁻¹ᵍ ⬝g
  homotopy_group_isomorphism_of_pequiv n f ⬝g
  ghomotopy_group_ptrunc_of_le H B

  section hsquare
  variables {A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type}
            {f₁₀ : A₀₀ → A₂₀} {f₃₀ : A₂₀ → A₄₀}
            {f₀₁ : A₀₀ → A₀₂} {f₂₁ : A₂₀ → A₂₂} {f₄₁ : A₄₀ → A₄₂}
            {f₁₂ : A₀₂ → A₂₂} {f₃₂ : A₂₂ → A₄₂}
            {f₀₃ : A₀₂ → A₀₄} {f₂₃ : A₂₂ → A₂₄} {f₄₃ : A₄₂ → A₄₄}
            {f₁₄ : A₀₄ → A₂₄} {f₃₄ : A₂₄ → A₄₄}

  definition trunc_functor_hsquare (n : ℕ₋₂) (h : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
    hsquare (trunc_functor n f₁₀) (trunc_functor n f₁₂)
            (trunc_functor n f₀₁) (trunc_functor n f₂₁) :=
  λa, !trunc_functor_compose⁻¹ ⬝ trunc_functor_homotopy n h a ⬝ !trunc_functor_compose

  end hsquare
  definition homotopy_group_succ_in_natural (n : ℕ) {A B : Type*} (f : A →* B) :
    hsquare (homotopy_group_succ_in A n) (homotopy_group_succ_in B n) (π→[n+1] f) (π→[n] (Ω→ f)) :=
  trunc_functor_hsquare _ (loopn_succ_in_natural n f)⁻¹*

end eq open eq

namespace nat

  protected definition rec_down (P : ℕ → Type) (s : ℕ) (H0 : P s) (Hs : Πn, P (n+1) → P n) : P 0 :=
  have Hp : Πn, P n → P (pred n),
  begin
    intro n p, cases n with n,
    { exact p },
    { exact Hs n p }
  end,
  have H : Πn, P (s - n),
  begin
    intro n, induction n with n p,
    { exact H0 },
    { exact Hp (s - n) p }
  end,
  transport P (nat.sub_self s) (H s)

end nat


namespace trunc_index
  open is_conn nat trunc is_trunc
  lemma minus_two_add_plus_two (n : ℕ₋₂) : -2+2+n = n :=
  by induction n with n p; reflexivity; exact ap succ p

  protected definition of_nat_monotone {n k : ℕ} : n ≤ k → of_nat n ≤ of_nat k :=
  begin
    intro H, induction H with k H K,
    { apply le.tr_refl },
    { apply le.step K }
  end

  lemma add_plus_two_comm (n k : ℕ₋₂) : n +2+ k = k +2+ n :=
  begin
    induction n with n IH,
    { exact minus_two_add_plus_two k },
    { exact !succ_add_plus_two ⬝ ap succ IH}
  end

end trunc_index

namespace int

  open trunc_index
  /-
    The function from integers to truncation indices which sends
    positive numbers to themselves, and negative numbers to negative
    2. In particular -1 is sent to -2, but since we only work with
    pointed types, that doesn't matter for us -/
  definition maxm2 [unfold 1] : ℤ → ℕ₋₂ :=
  λ n, int.cases_on n trunc_index.of_nat (λk, -2)

  -- we also need the max -1 - function
  definition maxm1 [unfold 1] : ℤ → ℕ₋₂ :=
  λ n, int.cases_on n trunc_index.of_nat (λk, -1)

  definition maxm2_le_maxm1 (n : ℤ) : maxm2 n ≤ maxm1 n :=
  begin
    induction n with n n,
    { exact le.tr_refl n },
    { exact minus_two_le -1 }
  end

  -- the is maxm1 minus 1
  definition maxm1m1 [unfold 1] : ℤ → ℕ₋₂ :=
  λ n, int.cases_on n (λ k, k.-1) (λ k, -2)

  definition maxm1_eq_succ (n : ℤ) : maxm1 n = (maxm1m1 n).+1 :=
  begin
    induction n with n n,
    { reflexivity },
    { reflexivity }
  end

  definition maxm2_le_maxm0 (n : ℤ) : maxm2 n ≤ max0 n :=
  begin
    induction n with n n,
    { exact le.tr_refl n },
    { exact minus_two_le 0 }
  end

  definition max0_le_of_le {n : ℤ} {m : ℕ} (H : n ≤ of_nat m)
    : nat.le (max0 n) m :=
  begin
    induction n with n n,
    { exact le_of_of_nat_le_of_nat H },
    { exact nat.zero_le m }
  end

  definition not_neg_succ_le_of_nat {n m : ℕ} : ¬m ≤ -[1+n] :=
  by cases m: exact id

  definition maxm2_monotone {n m : ℤ} (H : n ≤ m) : maxm2 n ≤ maxm2 m :=
  begin
    induction n with n n,
    { induction m with m m,
      { apply of_nat_le_of_nat, exact le_of_of_nat_le_of_nat H },
      { exfalso, exact not_neg_succ_le_of_nat H }},
    { apply minus_two_le }
  end

  definition sub_nat_le (n : ℤ) (m : ℕ) : n - m ≤ n :=
  le.intro !sub_add_cancel

  definition sub_one_le (n : ℤ) : n - 1 ≤ n :=
  sub_nat_le n 1

  definition le_add_nat (n : ℤ) (m : ℕ) : n ≤ n + m :=
  le.intro rfl

  definition le_add_one (n : ℤ) : n ≤ n + 1:=
  le_add_nat n 1

end int open int

namespace pmap

  definition eta {A B : Type*} (f : A →* B) : pmap.mk f (respect_pt f) = f :=
  begin induction f, reflexivity end

end pmap

namespace lift

  definition is_trunc_plift [instance] [priority 1450] (A : Type*) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc n (plift A) :=
  is_trunc_lift A n

end lift

namespace trunc
  open trunc_index
  definition trunc_index_equiv_nat [constructor] : ℕ₋₂ ≃ ℕ :=
  equiv.MK add_two sub_two add_two_sub_two sub_two_add_two

  definition is_set_trunc_index [instance] : is_set ℕ₋₂ :=
  is_trunc_equiv_closed_rev 0 trunc_index_equiv_nat

  definition is_contr_ptrunc_minus_one (A : Type*) : is_contr (ptrunc -1 A) :=
  is_contr_of_inhabited_prop pt

  -- TODO: redefine loopn_ptrunc_pequiv
  definition apn_ptrunc_functor (n : ℕ₋₂) (k : ℕ) {A B : Type*} (f : A →* B) :
    Ω→[k] (ptrunc_functor (n+k) f) ∘* (loopn_ptrunc_pequiv n k A)⁻¹ᵉ* ~*
    (loopn_ptrunc_pequiv n k B)⁻¹ᵉ* ∘* ptrunc_functor n (Ω→[k] f) :=
  begin
    revert n, induction k with k IH: intro n,
    { reflexivity },
    { exact sorry }
  end

  definition ptrunc_pequiv_natural [constructor] (n : ℕ₋₂) {A B : Type*} (f : A →* B) [is_trunc n A]
    [is_trunc n B] : f ∘* ptrunc_pequiv n A ~* ptrunc_pequiv n B ∘* ptrunc_functor n f :=
  begin
    fapply phomotopy.mk,
    { intro a, induction a with a, reflexivity },
    { refine !idp_con ⬝ _ ⬝ !idp_con⁻¹, refine !ap_compose'⁻¹ ⬝ _, apply ap_id }
  end

  definition ptr_natural [constructor] (n : ℕ₋₂) {A B : Type*} (f : A →* B) :
    ptrunc_functor n f ∘* ptr n A ~* ptr n B ∘* f :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity },
    { reflexivity }
  end

  definition ptrunc_elim_pcompose (n : ℕ₋₂) {A B C : Type*} (g : B →* C) (f : A →* B) [is_trunc n B]
    [is_trunc n C] : ptrunc.elim n (g ∘* f) ~* g ∘* ptrunc.elim n f :=
  begin
    fapply phomotopy.mk,
    { intro a, induction a with a, reflexivity },
    { apply idp_con }
  end

  definition ptrunc_elim_ptr_phomotopy_pid (n : ℕ₋₂) (A : Type*):
    ptrunc.elim n (ptr n A) ~* pid (ptrunc n A) :=
  begin
    fapply phomotopy.mk,
    { intro a, induction a with a, reflexivity },
    { apply idp_con }
  end

  definition is_trunc_ptrunc_of_is_trunc [instance] [priority 500] (A : Type*)
    (n m : ℕ₋₂) [H : is_trunc n A] : is_trunc n (ptrunc m A) :=
  is_trunc_trunc_of_is_trunc A n m

  definition ptrunc_pequiv_ptrunc_of_is_trunc {n m k : ℕ₋₂} {A : Type*}
    (H1 : n ≤ m) (H2 : n ≤ k) (H : is_trunc n A) : ptrunc m A ≃* ptrunc k A :=
  have is_trunc m A, from is_trunc_of_le A H1,
  have is_trunc k A, from is_trunc_of_le A H2,
  pequiv.MK (ptrunc.elim _ (ptr k A)) (ptrunc.elim _ (ptr m A))
    abstract begin
      refine !ptrunc_elim_pcompose⁻¹* ⬝* _,
      exact ptrunc_elim_phomotopy _ !ptrunc_elim_ptr ⬝* !ptrunc_elim_ptr_phomotopy_pid,
    end end
    abstract begin
      refine !ptrunc_elim_pcompose⁻¹* ⬝* _,
      exact ptrunc_elim_phomotopy _ !ptrunc_elim_ptr ⬝* !ptrunc_elim_ptr_phomotopy_pid,
    end end

  definition ptrunc_change_index {k l : ℕ₋₂} (p : k = l) (X : Type*)
    : ptrunc k X ≃* ptrunc l X :=
  pequiv_ap (λ n, ptrunc n X) p

  definition ptrunc_functor_le {k l : ℕ₋₂} (p : l ≤ k) (X : Type*)
    : ptrunc k X →* ptrunc l X :=
  have is_trunc k (ptrunc l X), from is_trunc_of_le _ p,
  ptrunc.elim _ (ptr l X)

  definition trunc_index.pred [unfold 1] (n : ℕ₋₂) : ℕ₋₂ :=
  begin cases n with n, exact -2, exact n end

end trunc

namespace is_trunc

  open trunc_index is_conn

  definition is_trunc_of_eq {n m : ℕ₋₂} (p : n = m) {A : Type} (H : is_trunc n A) : is_trunc m A :=
  transport (λk, is_trunc k A) p H

  definition is_trunc_succ_succ_of_is_trunc_loop (n : ℕ₋₂) (A : Type*) (H : is_trunc (n.+1) (Ω A))
    (H2 : is_conn 0 A) : is_trunc (n.+2) A :=
  begin
    apply is_trunc_succ_of_is_trunc_loop, apply minus_one_le_succ,
    refine is_conn.elim -1 _ _, exact H
  end

  lemma is_trunc_of_is_trunc_loopn (m n : ℕ) (A : Type*) (H : is_trunc n (Ω[m] A))
    (H2 : is_conn m A) : is_trunc (m + n) A :=
  begin
    revert A H H2; induction m with m IH: intro A H H2,
    { rewrite [nat.zero_add], exact H },
    rewrite [succ_add],
    apply is_trunc_succ_succ_of_is_trunc_loop,
    { apply IH,
      { apply is_trunc_equiv_closed _ !loopn_succ_in },
      apply is_conn_loop },
    exact is_conn_of_le _ (zero_le_of_nat (succ m))
  end

  lemma is_trunc_of_is_set_loopn (m : ℕ) (A : Type*) (H : is_set (Ω[m] A))
    (H2 : is_conn m A) : is_trunc m A :=
  is_trunc_of_is_trunc_loopn m 0 A H H2

end is_trunc
namespace sigma

  -- definition sigma_pathover_equiv_of_is_prop {A : Type} {B : A → Type} {C : Πa, B a → Type}
  --   {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'}
  --   [Πa b, is_prop (C a b)] : ⟨b, c⟩ =[p] ⟨b', c'⟩ ≃ b =[p] b' :=
  -- begin
  --   fapply equiv.MK,
  --   { exact pathover_pr1 },
  --   { intro q, induction q, apply pathover_idp_of_eq, exact sigma_eq idp !is_prop.elimo },
  --   { intro q, induction q,
  --     have c = c', from !is_prop.elim, induction this,
  --     rewrite [▸*, is_prop_elimo_self (C a) c] },
  --   { esimp, generalize ⟨b, c⟩, intro x q, }
  -- end
--rexact @(ap pathover_pr1) _ idpo _,

end sigma open sigma

namespace group
--  definition is_equiv_isomorphism


  -- some extra instances for type class inference
  -- definition is_mul_hom_comm_homomorphism [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_mul_hom G G' (@ab_group.to_group _ (AbGroup.struct G))
  --                           (@ab_group.to_group _ (AbGroup.struct G')) φ :=
  -- homomorphism.struct φ

  -- definition is_mul_hom_comm_homomorphism1 [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_mul_hom G G' _
  --                           (@ab_group.to_group _ (AbGroup.struct G')) φ :=
  -- homomorphism.struct φ

  -- definition is_mul_hom_comm_homomorphism2 [instance] {G G' : AbGroup} (φ : G →g G')
  --   : @is_mul_hom G G' (@ab_group.to_group _ (AbGroup.struct G)) _ φ :=
  -- homomorphism.struct φ

  definition pgroup_of_Group (X : Group) : pgroup X :=
  pgroup_of_group _ idp

  definition isomorphism_ap {A : Type} (F : A → Group) {a b : A} (p : a = b) : F a ≃g F b :=
    isomorphism_of_eq (ap F p)

  definition interchange (G : AbGroup) (a b c d : G) : (a * b) * (c * d) = (a * c) * (b * d) :=
  calc (a * b) * (c * d) = a * (b * (c * d)) : by exact mul.assoc a b (c * d)
                     ... = a * ((b * c) * d) : by exact ap (λ bcd, a * bcd) (mul.assoc b c d)⁻¹
                     ... = a * ((c * b) * d) : by exact ap (λ bc, a * (bc * d)) (mul.comm b c)
                     ... = a * (c * (b * d)) : by exact ap (λ bcd, a * bcd) (mul.assoc c b d)
                     ... = (a * c) * (b * d) : by exact (mul.assoc a c (b * d))⁻¹

  definition homomorphism_comp_compute {G H K : Group} (g : H →g K) (f : G →g H) (x : G) : (g ∘g f) x = g (f x) :=
  begin
    reflexivity
  end

  open option
  definition add_point_AbGroup [unfold 3] {X : Type} (G : X → AbGroup) : X₊ → AbGroup
  | (some x) := G x
  | none     := trivial_ab_group_lift

  definition isomorphism_of_is_contr {G H : Group} (hG : is_contr G) (hH : is_contr H) : G ≃g H :=
  trivial_group_of_is_contr G ⬝g (trivial_group_of_is_contr H)⁻¹ᵍ

end group open group

namespace fiber

  definition is_contr_pfiber_pid (A : Type*) : is_contr (pfiber (pid A)) :=
  is_contr.mk pt begin intro x, induction x with a p, esimp at p, cases p, reflexivity end

end fiber

namespace function
  variables {A B : Type} {f f' : A → B}
  open is_conn sigma.ops

  definition merely_constant {A B : Type} (f : A → B) : Type :=
  Σb, Πa, merely (f a = b)

  definition merely_constant_pmap {A B : Type*} {f : A →* B} (H : merely_constant f) (a : A) :
    merely (f a = pt) :=
  tconcat (tconcat (H.2 a) (tinverse (H.2 pt))) (tr (respect_pt f))

  definition merely_constant_of_is_conn {A B : Type*} (f : A →* B) [is_conn 0 A] : merely_constant f :=
  ⟨pt, is_conn.elim -1 _ (tr (respect_pt f))⟩

  definition homotopy_group_isomorphism_of_is_embedding (n : ℕ) [H : is_succ n] {A B : Type*}
    (f : A →* B) [H2 : is_embedding f] : πg[n] A ≃g πg[n] B :=
  begin
    apply isomorphism.mk (homotopy_group_homomorphism n f),
    induction H with n,
    apply is_equiv_of_equiv_of_homotopy
      (ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn_of_is_embedding (n+1) f)),
    exact sorry
  end

end function open function

namespace is_conn

  open unit trunc_index nat is_trunc pointed.ops

  definition is_conn_fun_compose {n : ℕ₋₂} {A B C : Type} (g : B → C) (f : A → B)
    (H : is_conn_fun n g) (K : is_conn_fun n f) : is_conn_fun n (g ∘ f) :=
  sorry

end is_conn

namespace misc
  open is_conn

  open sigma.ops pointed trunc_index

  definition component [constructor] (A : Type*) : Type* :=
  pType.mk (Σ(a : A), merely (pt = a)) ⟨pt, tr idp⟩

  lemma is_conn_component [instance] (A : Type*) : is_conn 0 (component A) :=
  is_contr.mk (tr pt)
    begin
      intro x, induction x with x, induction x with a p, induction p with p, induction p, reflexivity
    end

  definition component_incl [constructor] (A : Type*) : component A →* A :=
  pmap.mk pr1 idp

  definition is_embedding_component_incl [instance] (A : Type*) : is_embedding (component_incl A) :=
  is_embedding_pr1 _

  definition component_intro [constructor] {A B : Type*} (f : A →* B) (H : merely_constant f) :
    A →* component B :=
  begin
    fapply pmap.mk,
    { intro a, refine ⟨f a, _⟩, exact tinverse (merely_constant_pmap H a) },
    exact subtype_eq !respect_pt
  end

  definition component_functor [constructor] {A B : Type*} (f : A →* B) : component A →* component B :=
  component_intro (f ∘* component_incl A) !merely_constant_of_is_conn

  -- definition component_elim [constructor] {A B : Type*} (f : A →* B) (H : merely_constant f) :
  --   A →* component B :=
  -- begin
  --   fapply pmap.mk,
  --   { intro a, refine ⟨f a, _⟩, exact tinverse (merely_constant_pmap H a) },
  --   exact subtype_eq !respect_pt
  -- end

  definition loop_component (A : Type*) : Ω (component A) ≃* Ω A :=
  loop_pequiv_loop_of_is_embedding (component_incl A)

  lemma loopn_component (n : ℕ) (A : Type*) : Ω[n+1] (component A) ≃* Ω[n+1] A :=
  !loopn_succ_in ⬝e* loopn_pequiv_loopn n (loop_component A) ⬝e* !loopn_succ_in⁻¹ᵉ*

  -- lemma fundamental_group_component (A : Type*) : π₁ (component A) ≃g π₁ A :=
  -- isomorphism_of_equiv (trunc_equiv_trunc 0 (loop_component A)) _

  lemma homotopy_group_component (n : ℕ) (A : Type*) : πg[n+1] (component A) ≃g πg[n+1] A :=
  homotopy_group_isomorphism_of_is_embedding (n+1) (component_incl A)

  definition is_trunc_component [instance] (n : ℕ₋₂) (A : Type*) [is_trunc n A] :
    is_trunc n (component A) :=
  begin
    apply @is_trunc_sigma, intro a, cases n with n,
    { apply is_contr_of_inhabited_prop, exact tr !is_prop.elim },
    { apply is_trunc_succ_of_is_prop },
  end

  definition ptrunc_component' (n : ℕ₋₂) (A : Type*) :
    ptrunc (n.+2) (component A) ≃* component (ptrunc (n.+2) A) :=
  begin
    fapply pequiv.MK',
    { exact ptrunc.elim (n.+2) (component_functor !ptr) },
    { intro x, cases x with x p, induction x with a,
      refine tr ⟨a, _⟩,
      note q := trunc_functor -1 !tr_eq_tr_equiv p,
      exact trunc_trunc_equiv_left _ !minus_one_le_succ q },
    { exact sorry },
    { exact sorry }
  end

  definition ptrunc_component (n : ℕ₋₂) (A : Type*) :
    ptrunc n (component A) ≃* component (ptrunc n A) :=
  begin
    cases n with n, exact sorry,
    cases n with n, exact sorry,
    exact ptrunc_component' n A
  end

  definition pfiber_pequiv_component_of_is_contr [constructor] {A B : Type*} (f : A →* B) [is_contr B]
    /- extra condition, something like trunc_functor 0 f is an embedding -/ : pfiber f ≃* component A :=
  sorry

end misc

namespace category

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
  open iso
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

  definition Group.sigma_char2.{u} : Group.{u} ≃
    Σ(A : Type.{u}) (v : (A → A → A) × (A → A) × A), Group_props v :=
  begin
    fapply equiv.MK,
    { intro G, refine ⟨G, _⟩, induction G with G g, induction g with m s ma o om mo i mi,
      repeat (fconstructor; do 2 try assumption), },
    { intro v, induction v with x v, induction v with y v, repeat induction y with x y,
      repeat induction v with x v, constructor, fconstructor, repeat assumption },
    { intro v, induction v with x v, induction v with y v, repeat induction y with x y,
      repeat induction v with x v, reflexivity },
    { intro v, repeat induction v with x v, reflexivity },
  end
  open is_trunc

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

  open prod.ops
  definition group_of_Group_props.{u} {A : Type.{u}} {m : A → A → A} {i : A → A} {o : A}
    (H : Group_props (m, (i, o))) : group A :=
  ⦃group, mul := m, inv := i, one := o, is_set_carrier := H.1,
    mul_one := H.2.1, one_mul := H.2.2.1, mul_assoc := H.2.2.2.1, mul_left_inv := H.2.2.2.2⦄

  theorem Group_eq_equiv_lemma2 {A : Type} {m m' : A → A → A} {i i' : A → A} {o o' : A}
    (H : Group_props (m, (i, o))) (H' : Group_props (m', (i', o'))) :
    (m, (i, o)) = (m', (i', o')) ≃ (m ~2 m') :=
  begin
    have is_set A, from pr1 H,
    apply equiv_of_is_prop,
    { intro p, exact apd100 (eq_pr1 p)},
    { intro p, apply prod_eq (eq_of_homotopy2 p),
      apply prod_eq: esimp [Group_props] at *; esimp,
      { apply eq_of_homotopy,
        exact inv_eq_of_mul_eq (group_of_Group_props H) (group_of_Group_props H') p },
      { exact one_eq_of_mul_eq (group_of_Group_props H) (group_of_Group_props H') p }}
  end

  open sigma.ops

  theorem Group_eq_equiv_lemma {G H : Group}
    (p : (Group.sigma_char2 G).1 = (Group.sigma_char2 H).1) :
    ((Group.sigma_char2 G).2 =[p] (Group.sigma_char2 H).2) ≃
    (is_mul_hom (equiv_of_eq (proof p qed : Group.carrier G = Group.carrier H))) :=
  begin
    refine !sigma_pathover_equiv_of_is_prop ⬝e _,
    induction G with G g, induction H with H h,
    esimp [Group.sigma_char2] at p, induction p,
    refine !pathover_idp ⬝e _,
    induction g with s m ma o om mo i mi, induction h with σ μ μa ε εμ με ι μι,
    exact Group_eq_equiv_lemma2 (Group.sigma_char2 (Group.mk G (group.mk s m ma o om mo i mi))).2.2
                                (Group.sigma_char2 (Group.mk G (group.mk σ μ μa ε εμ με ι μι))).2.2
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
    refine (eq_equiv_fn_eq_of_equiv Group.sigma_char2 G H) ⬝e _,
    refine !sigma_eq_equiv ⬝e _,
    refine sigma_equiv_sigma_right Group_eq_equiv_lemma ⬝e _,
    transitivity (Σ(e : (Group.sigma_char2 G).1 ≃ (Group.sigma_char2 H).1),
      @is_mul_hom _ _ _ _ (to_fun e)), apply sigma_ua,
    exact !isomorphism.sigma_char⁻¹ᵉ
  end

  definition to_fun_Group_eq_equiv {G H : Group} (p : G = H)
    : Group_eq_equiv G H p ~ isomorphism_of_eq p :=
  begin
    induction p, reflexivity
  end

  definition Group_eq2 {G H : Group} {p q : G = H}
    (r : isomorphism_of_eq p ~ isomorphism_of_eq q) : p = q :=
  begin
    apply eq_of_fn_eq_fn (Group_eq_equiv G H),
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

  definition category_AbGroup : category AbGroup :=
  category.mk precategory_AbGroup sorry

  definition Grp.{u} [constructor] : Category := category.Mk Group.{u} category_Group
  definition AbGrp [constructor] : Category := category.Mk AbGroup category_AbGroup

end category

namespace sphere

  -- definition constant_sphere_map_sphere {n m : ℕ} (H : n < m) (f : S* n →* S* m) :
  --   f ~* pconst (S* n) (S* m) :=
  -- begin
  --   assert H : is_contr (Ω[n] (S* m)),
  --   { apply homotopy_group_sphere_le, },
  --   apply phomotopy_of_eq,
  --   apply eq_of_fn_eq_fn !psphere_pmap_pequiv,
  --   apply @is_prop.elim
  -- end

end sphere

section injective_surjective
open trunc fiber image

  /- do we want to prove this without funext before we move it? -/
  variables {A B C : Type} (f : A → B)
  definition is_embedding_factor [is_set A] [is_set B] (g : B → C) (h : A → C) (H : g ∘ f ~ h) :
    is_embedding h → is_embedding f :=
  begin
    induction H using homotopy.rec_on_idp,
    intro E,
    fapply is_embedding_of_is_injective,
    intro x y p,
    fapply @is_injective_of_is_embedding _ _ _ E _ _ (ap g p)
  end

  definition is_surjective_factor (g : B → C) (h : A → C) (H : g ∘ f ~ h) :
    is_surjective h → is_surjective g :=
  begin
    induction H using homotopy.rec_on_idp,
    intro S,
    intro c,
    note p := S c,
    induction p,
    apply tr,
    fapply fiber.mk,
    exact f a,
    exact p
  end

end injective_surjective

-- Yuri Sulyma's code from HoTT MRC

notation `⅀→`:(max+5) := psusp_functor
notation `⅀⇒`:(max+5) := psusp_functor_phomotopy
notation `Ω⇒`:(max+5) := ap1_phomotopy

definition ap1_phomotopy_symm {A B : Type*} {f g : A →* B} (p : f ~* g) : (Ω⇒ p)⁻¹* = Ω⇒ (p⁻¹*) :=
begin
  induction p using phomotopy_rec_on_idp,
  rewrite ap1_phomotopy_refl,
  rewrite [+refl_symm],
  rewrite ap1_phomotopy_refl
end

definition ap1_phomotopy_trans {A B : Type*} {f g h : A →* B} (q : g ~* h) (p : f ~* g) : Ω⇒ (p ⬝* q) = Ω⇒ p ⬝* Ω⇒ q :=
begin
  induction p using phomotopy_rec_on_idp,
  induction q using phomotopy_rec_on_idp,
  rewrite trans_refl,
  rewrite [+ap1_phomotopy_refl],
  rewrite trans_refl
end


namespace pointed
  definition to_homotopy_pt_mk {A B : Type*} {f g : A →* B} (h : f ~ g)
    (p : h pt ⬝ respect_pt g = respect_pt f) : to_homotopy_pt (phomotopy.mk h p) = p :=
  to_right_inv !eq_con_inv_equiv_con_eq p


  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type*}
            {f₁₀ : A₀₀ →* A₂₀} {f₁₂ : A₀₂ →* A₂₂}
            {f₀₁ : A₀₀ →* A₀₂} {f₂₁ : A₂₀ →* A₂₂}
  definition psquare_transpose (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : psquare f₀₁ f₂₁ f₁₀ f₁₂ := p⁻¹*

end pointed

namespace pi
  definition pi_bool_left_nat {A B : bool → Type} (g : Πx, A x -> B x) :
             hsquare (pi_bool_left A) (pi_bool_left B) (pi_functor_right g) (prod_functor (g ff) (g tt)) :=
  begin intro h, esimp end

  definition pi_bool_left_inv_nat {A B : bool → Type} (g : Πx, A x -> B x) :
              hsquare (pi_bool_left A)⁻¹ᵉ (pi_bool_left B)⁻¹ᵉ (prod_functor (g ff) (g tt)) (pi_functor_right g) := hhinverse (pi_bool_left_nat g)
 
end pi
