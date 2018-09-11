/-
Copyright (c) 2015 Ulrik Buchholtz, Egbert Rijke and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke, Floris van Doorn

Formalization of the higher groups paper
-/

import .homotopy.EM algebra.category.constructions.pullback
open eq is_conn pointed is_trunc trunc equiv is_equiv trunc_index susp nat algebra
     prod.ops sigma sigma.ops category EM
namespace higher_group
set_option pp.binder_types true
universe variable u

/- Results not necessarily about higher groups which we repeat here, because they are mentioned in
  the higher group paper -/
namespace hide
open pushout
definition connect_intro_pequiv {k : ℕ} {B : Type*} (A : Type*) (H : is_conn k B) :
  ppmap B (connect k A) ≃* ppmap B A :=
is_conn.connect_intro_pequiv A H

definition is_conn_fun_prod_of_wedge (n m : ℕ) (A B : Type*)
  [cA : is_conn n A] [cB : is_conn m B] : is_conn_fun (m + n) (@prod_of_wedge A B) :=
is_conn_fun_prod_of_wedge n m A B

definition is_trunc_ppi_of_is_conn (k n : ℕ) (X : Type*) (H : is_conn (k.-1) X)
  (Y : X → Type*) (H3 : Πx, is_trunc (k + n) (Y x)) :
  is_trunc n (Π*(x : X), Y x) :=
is_conn.is_trunc_ppi_of_is_conn _ (k.-2) H _ _ (le_of_eq (sub_one_add_plus_two_sub_one k n)⁻¹) _ H3

end hide

/- The k-groupal n-types.
   We require that the carrier has a point (preserved by the equivalence) -/

structure GType (n k : ℕ) : Type := /- (n,k)GType, denoted here as [n;k]GType -/
  (car : ptrunctype.{u} n)
  (B : pconntype.{u} (k.-1)) /- this is Bᵏ -/
  (e : car ≃* Ω[k] B)

structure InfGType (k : ℕ) : Type := /- (∞,k)GType, denoted here as [∞;k]GType -/
  (car : pType.{u})
  (B : pconntype.{u} (k.-1)) /- this is Bᵏ -/
  (e : car ≃* Ω[k] B)

structure ωGType (n : ℕ) := /- (n,ω)GType, denoted here as [n;ω]GType -/
  (B : Π(k : ℕ), (n+k)-Type*[k.-1])
  (e : Π(k : ℕ), B k ≃* Ω (B (k+1)))

attribute InfGType.car GType.car [coercion]

variables {n k k' l : ℕ}
notation `[`:95 n:0 `; ` k `]GType`:0 := GType n k
notation `[∞; `:95 k:0 `]GType`:0 := InfGType k
notation `[`:95 n:0 `;ω]GType`:0 := ωGType n

open GType
open InfGType (renaming B→iB e→ie)
open ωGType (renaming B→oB e→oe)

/- some basic properties -/
lemma is_trunc_B' (G : [n;k]GType) : is_trunc (k+n) (B G) :=
begin
  apply is_trunc_of_is_trunc_loopn,
  exact is_trunc_equiv_closed _ (e G) _,
  exact _
end

lemma is_trunc_B (G : [n;k]GType) : is_trunc (n+k) (B G) :=
transport (λm, is_trunc m (B G)) (add.comm k n) (is_trunc_B' G)

local attribute [instance] is_trunc_B

definition GType.sigma_char (n k : ℕ) :
  GType.{u} n k ≃ Σ(B : pconntype.{u} (k.-1)), Σ(X : ptrunctype.{u} n), X ≃* Ω[k] B :=
begin
  fapply equiv.MK,
  { intro G, exact ⟨B G, G, e G⟩ },
  { intro v, exact GType.mk v.2.1 v.1 v.2.2 },
  { intro v, induction v with v₁ v₂, induction v₂, reflexivity },
  { intro G, induction G, reflexivity },
end

definition GType_equiv (n k : ℕ) : [n;k]GType ≃ (n+k)-Type*[k.-1] :=
GType.sigma_char n k ⬝e
sigma_equiv_of_is_embedding_left_contr
  ptruncconntype.to_pconntype
  (is_embedding_ptruncconntype_to_pconntype (n+k) (k.-1))
  begin
    intro X,
    apply is_trunc_equiv_closed_rev -2,
    { apply sigma_equiv_sigma_right, intro B',
      refine _ ⬝e (ptrunctype_eq_equiv B' (ptrunctype.mk (Ω[k] X) !is_trunc_loopn_nat pt))⁻¹ᵉ,
      assert lem : Π(A : n-Type*) (B : Type*) (H : is_trunc n B),
        (A ≃* B) ≃ (A ≃* (ptrunctype.mk B H pt)),
      { intro A B'' H, induction B'', reflexivity },
      apply lem },
    exact _
  end
  begin
    intro B' H, apply fiber.mk (ptruncconntype.mk B' (is_trunc_B (GType.mk H.1 B' H.2)) pt _),
    induction B' with G' B' e', reflexivity
  end

definition GType_equiv_pequiv {n k : ℕ} (G : [n;k]GType) : GType_equiv n k G ≃* B G :=
by reflexivity

definition GType_eq_equiv {n k : ℕ} (G H : [n;k]GType) : (G = H :> [n;k]GType) ≃ (B G ≃* B H) :=
eq_equiv_fn_eq (GType_equiv n k) _ _ ⬝e !ptruncconntype_eq_equiv

definition GType_eq {n k : ℕ} {G H : [n;k]GType} (e : B G ≃* B H) : G = H :=
(GType_eq_equiv G H)⁻¹ᵉ e

/- similar properties for [∞;k]GType -/

definition InfGType.sigma_char (k : ℕ) :
  InfGType.{u} k ≃ Σ(B : pconntype.{u} (k.-1)), Σ(X : pType.{u}), X ≃* Ω[k] B :=
begin
  fapply equiv.MK,
  { intro G, exact ⟨iB G, G, ie G⟩ },
  { intro v, exact InfGType.mk v.2.1 v.1 v.2.2 },
  { intro v, induction v with v₁ v₂, induction v₂, reflexivity },
  { intro G, induction G, reflexivity },
end

definition InfGType_equiv (k : ℕ) : [∞;k]GType ≃ Type*[k.-1] :=
InfGType.sigma_char k ⬝e
@sigma_equiv_of_is_contr_right _ _
  (λX, is_trunc_equiv_closed_rev -2 (sigma_equiv_sigma_right (λB', !pType_eq_equiv⁻¹ᵉ)) _)

definition InfGType_equiv_pequiv {k : ℕ} (G : [∞;k]GType) : InfGType_equiv k G ≃* iB G :=
by reflexivity

definition InfGType_eq_equiv {k : ℕ} (G H : [∞;k]GType) : (G = H :> [∞;k]GType) ≃ (iB G ≃* iB H) :=
eq_equiv_fn_eq (InfGType_equiv k) _ _ ⬝e !pconntype_eq_equiv

definition InfGType_eq {k : ℕ} {G H : [∞;k]GType} (e : iB G ≃* iB H) : G = H :=
(InfGType_eq_equiv G H)⁻¹ᵉ e

/- alternative constructor for ωGType -/

definition ωGType.mk_le {n : ℕ} (k₀ : ℕ)
  (C : Π⦃k : ℕ⦄, k₀ ≤ k → ((n+k)-Type*[k.-1] : Type.{u+1}))
  (e : Π⦃k : ℕ⦄ (H : k₀ ≤ k), C H ≃* Ω (C (le.step H))) : ([n;ω]GType : Type.{u+1}) :=
begin
  fconstructor,
  { apply rec_down_le _ k₀ C, intro n' D,
    refine (ptruncconntype.mk (Ω D) _ pt _),
      apply is_trunc_loop, apply is_trunc_ptruncconntype, apply is_conn_loop,
      apply is_conn_ptruncconntype },
  { intro n', apply rec_down_le_univ, exact e, intro n D, reflexivity }
end

definition ωGType.mk_le_beta {n : ℕ} {k₀ : ℕ}
  (C : Π⦃k : ℕ⦄, k₀ ≤ k → ((n+k)-Type*[k.-1] : Type.{u+1}))
  (e : Π⦃k : ℕ⦄ (H : k₀ ≤ k), C H ≃* Ω (C (le.step H)))
  (k : ℕ) (H : k₀ ≤ k) : oB (ωGType.mk_le k₀ C e) k ≃* C H :=
ptruncconntype_eq_equiv _ _ !rec_down_le_beta_ge

definition GType_hom (G H : [n;k]GType) : Type :=
B G →* B H

definition ωGType_hom (G H : [n;ω]GType) : Type* :=
pointed.MK
  (Σ(f : Πn, oB G n →* oB H n), Πn, psquare (f n) (Ω→ (f (n+1))) (oe G n) (oe H n))
  ⟨λn, pconst (oB G n) (oB H n), λn, !phconst_square ⬝vp* !ap1_pconst⟩

/- Constructions on higher groups -/
definition Decat (G : [n+1;k]GType) : [n;k]GType :=
GType.mk (ptrunctype.mk (ptrunc n G) _ pt) (pconntype.mk (ptrunc (n + k) (B G)) _ pt)
  abstract begin
    refine ptrunc_pequiv_ptrunc n (e G) ⬝e* _,
    symmetry, exact !loopn_ptrunc_pequiv_nat
  end end

definition Disc (G : [n;k]GType) : [n+1;k]GType :=
GType.mk (ptrunctype.mk G (show is_trunc (n.+1) G, from _) pt) (B G) (e G)

definition Decat_adjoint_Disc (G : [n+1;k]GType) (H : [n;k]GType) :
  ppmap (B (Decat G)) (B H) ≃* ppmap (B G) (B (Disc H)) :=
pmap_ptrunc_pequiv (n + k) (B G) (B H)

definition Decat_adjoint_Disc_natural {G G' : [n+1;k]GType} {H H' : [n;k]GType}
  (g : B G' →* B G) (h : B H →* B H') :
  psquare (Decat_adjoint_Disc G H)
          (Decat_adjoint_Disc G' H')
          (ppcompose_left h ∘* ppcompose_right (ptrunc_functor _ g))
          (ppcompose_left h ∘* ppcompose_right g) :=
pmap_ptrunc_pequiv_natural (n + k) g h

definition Decat_Disc (G : [n;k]GType) : Decat (Disc G) = G :=
GType_eq !ptrunc_pequiv

definition InfDecat (n : ℕ) (G : [∞;k]GType) : [n;k]GType :=
GType.mk (ptrunctype.mk (ptrunc n G) _ pt) (pconntype.mk (ptrunc (n + k) (iB G)) _ pt)
  abstract begin
    refine ptrunc_pequiv_ptrunc n (ie G) ⬝e* _,
    symmetry, exact !loopn_ptrunc_pequiv_nat
  end end

definition InfDisc (n : ℕ) (G : [n;k]GType) : [∞;k]GType :=
InfGType.mk G (B G) (e G)

definition InfDecat_adjoint_InfDisc (G : [∞;k]GType) (H : [n;k]GType) :
  ppmap (B (InfDecat n G)) (B H) ≃* ppmap (iB G) (iB (InfDisc n H)) :=
pmap_ptrunc_pequiv (n + k) (iB G) (B H)

definition InfDecat_adjoint_InfDisc_natural {G G' : [∞;k]GType} {H H' : [n;k]GType}
  (g : iB G' →* iB G) (h : B H →* B H') :
  psquare (InfDecat_adjoint_InfDisc G H)
          (InfDecat_adjoint_InfDisc G' H')
          (ppcompose_left h ∘* ppcompose_right (ptrunc_functor _ g))
          (ppcompose_left h ∘* ppcompose_right g) :=
pmap_ptrunc_pequiv_natural (n + k) g h

definition InfDecat_InfDisc (G : [n;k]GType) : InfDecat n (InfDisc n G) = G :=
GType_eq !ptrunc_pequiv

definition Deloop (G : [n;k+1]GType) : [n+1;k]GType :=
have is_conn k (B G), from is_conn_pconntype (B G),
have is_trunc (n + (k + 1)) (B G), from is_trunc_B G,
have is_trunc ((n + 1) + k) (B G), from transport (λ(n : ℕ), is_trunc n _) (succ_add n k)⁻¹ this,
GType.mk (ptrunctype.mk (Ω[k] (B G)) !is_trunc_loopn_nat pt)
  (pconntype.mk (B G) !is_conn_of_is_conn_succ pt)
  (pequiv_of_equiv erfl idp)

definition Loop (G : [n+1;k]GType) : [n;k+1]GType :=
GType.mk (ptrunctype.mk (Ω G) !is_trunc_loop_nat pt)
  (connconnect k (B G))
  (loop_pequiv_loop (e G) ⬝e* (loopn_connect k (B G))⁻¹ᵉ*)

definition Deloop_adjoint_Loop (G : [n;k+1]GType) (H : [n+1;k]GType) :
  ppmap (B (Deloop G)) (B H) ≃* ppmap (B G) (B (Loop H)) :=
(connect_intro_pequiv _ !is_conn_pconntype)⁻¹ᵉ*

definition Deloop_adjoint_Loop_natural {G G' : [n;k+1]GType} {H H' : [n+1;k]GType}
  (g : B G' →* B G) (h : B H →* B H') :
  psquare (Deloop_adjoint_Loop G H)
          (Deloop_adjoint_Loop G' H')
          (ppcompose_left h ∘* ppcompose_right g)
          (ppcompose_left (connect_functor k h) ∘* ppcompose_right g) :=
(connect_intro_pequiv_natural g h _ _)⁻¹ʰ*

definition Loop_Deloop (G : [n;k+1]GType) : Loop (Deloop G) = G :=
GType_eq (connect_pequiv (is_conn_pconntype (B G)))

definition Forget (G : [n;k+1]GType) : [n;k]GType :=
have is_conn k (B G), from !is_conn_pconntype,
GType.mk G (pconntype.mk (Ω (B G)) !is_conn_loop pt)
  abstract begin
    refine e G ⬝e* !loopn_succ_in
  end end

definition Stabilize (G : [n;k]GType) : [n;k+1]GType :=
have is_conn k (susp (B G)), from !is_conn_susp,
have Hconn : is_conn k (ptrunc (n + k + 1) (susp (B G))), from !is_conn_ptrunc,
GType.mk (ptrunctype.mk (ptrunc n (Ω[k+1] (susp (B G)))) _ pt)
  (pconntype.mk (ptrunc (n+k+1) (susp (B G))) Hconn pt)
  abstract begin
    refine !loopn_ptrunc_pequiv⁻¹ᵉ* ⬝e* _,
    apply loopn_pequiv_loopn,
    exact ptrunc_change_index !of_nat_add_of_nat _
  end end

definition Stabilize_pequiv {G H : [n;k]GType} (e : B G ≃* B H) :
  B (Stabilize G) ≃* B (Stabilize H) :=
ptrunc_pequiv_ptrunc (n+k+1) (susp_pequiv e)

definition Stabilize_adjoint_Forget (G : [n;k]GType) (H : [n;k+1]GType) :
  ppmap (B (Stabilize G)) (B H) ≃* ppmap (B G) (B (Forget H)) :=
have is_trunc (n + k + 1) (B H), from !is_trunc_B,
pmap_ptrunc_pequiv (n + k + 1) (⅀ (B G)) (B H) ⬝e* susp_adjoint_loop (B G) (B H)

definition Stabilize_adjoint_Forget_natural {G G' : [n;k]GType} {H H' : [n;k+1]GType}
  (g : B G' →* B G) (h : B H →* B H') :
  psquare (Stabilize_adjoint_Forget G H)
          (Stabilize_adjoint_Forget G' H')
          (ppcompose_left h ∘* ppcompose_right (ptrunc_functor (n+k+1) (⅀→ g)))
          (ppcompose_left (Ω→ h) ∘* ppcompose_right g) :=
begin
  have is_trunc (n + k + 1) (B H), from !is_trunc_B,
  have is_trunc (n + k + 1) (B H'), from !is_trunc_B,
  refine pmap_ptrunc_pequiv_natural (n+k+1) (⅀→ g) h ⬝h* _,
  exact susp_adjoint_loop_natural_left g ⬝v* susp_adjoint_loop_natural_right h
end

definition Forget_Stabilize (H : k ≥ n + 2) (G : [n;k]GType) : B (Forget (Stabilize G)) ≃* B G :=
loop_ptrunc_pequiv _ _ ⬝e*
begin
  cases k with k,
  { cases H },
  { have k ≥ succ n, from le_of_succ_le_succ H,
    assert this : n + succ k ≤ 2 * k,
    { rewrite [two_mul, add_succ, -succ_add], exact nat.add_le_add_right this k },
    exact freudenthal_pequiv this (B G) }
end⁻¹ᵉ* ⬝e*
ptrunc_pequiv (n + k) _

definition Stabilize_Forget (H : k ≥ n + 1) (G : [n;k+1]GType) : B (Stabilize (Forget G)) ≃* B G :=
begin
  assert lem1 : n + succ k ≤ 2 * k,
  { rewrite [two_mul, add_succ, -succ_add], exact nat.add_le_add_right H k },
  have is_conn k (B G), from !is_conn_pconntype,
  have Π(G' : [n;k+1]GType), is_trunc (n + k + 1) (B G'), from is_trunc_B,
  note z := is_conn_fun_loop_susp_counit (B G) (nat.le_refl (2 * k)),
  refine ptrunc_pequiv_ptrunc_of_le (of_nat_le_of_nat lem1) (@(ptrunc_pequiv_ptrunc_of_is_conn_fun _ _) z) ⬝e*
    !ptrunc_pequiv,
end

definition stabilization (H : k ≥ n + 2) : is_equiv (@Stabilize n k) :=
begin
  fapply adjointify,
  { exact Forget },
  { intro G, apply GType_eq, exact Stabilize_Forget (le.trans !self_le_succ H) _ },
  { intro G, apply GType_eq, exact Forget_Stabilize H G }
end

/- an incomplete formalization of ω-Stabilization -/
definition ωForget (k : ℕ) (G : [n;ω]GType) : [n;k]GType :=
have is_trunc (n + k) (oB G k), from _,
have is_trunc n (Ω[k] (oB G k)), from !is_trunc_loopn_nat,
GType.mk (ptrunctype.mk (Ω[k] (oB G k)) _ pt) (oB G k) (pequiv_of_equiv erfl idp)

definition nStabilize (H : k ≤ l) (G : GType.{u} n k) : GType.{u} n l :=
begin
  induction H with l H IH, exact G, exact Stabilize IH
end

definition nStabilize_pequiv (H H' : k ≤ l) {G G' : [n;k]GType}
  (e : B G ≃* B G') : B (nStabilize H G) ≃* B (nStabilize H' G') :=
begin
  induction H with l H IH,
  { exact e ⬝e* pequiv_ap (λH, B (nStabilize H G')) (is_prop.elim (le.refl k) H') },
  cases H' with l H'',
  { exfalso, exact not_succ_le_self H },
  exact Stabilize_pequiv (IH H'')
end

definition nStabilize_pequiv_of_eq (H : k ≤ l) (p : k = l) (G : [n;k]GType) :
  B (nStabilize H G) ≃* B G :=
begin induction p, exact pequiv_ap (λH, B (nStabilize H G)) (is_prop.elim H (le.refl k)) end

definition ωStabilize_of_le (H : k ≥ n + 2) (G : [n;k]GType) : [n;ω]GType :=
ωGType.mk_le k (λl H', GType_equiv n l (nStabilize H' G))
               (λl H', (Forget_Stabilize (le.trans H H') (nStabilize H' G))⁻¹ᵉ*)

definition ωStabilize_of_le_beta (H : k ≥ n + 2) (G : [n;k]GType) (H' : l ≥ k) :
  oB (ωStabilize_of_le H G) l ≃* GType_equiv n l (nStabilize H' G) :=
ptruncconntype_eq_equiv _ _ !rec_down_le_beta_ge

definition ωStabilize_of_le_pequiv (H : k ≥ n + 2) (H' : k' ≥ n + 2) {G : [n;k]GType}
  {G' : [n;k']GType} (e : B G ≃* B G') (l : ℕ) (Hl : l ≥ k) (Hl' : l ≥ k') (p : k = k') :
  oB (ωStabilize_of_le H G) l ≃* oB (ωStabilize_of_le H' G') l :=
begin
  refine ωStabilize_of_le_beta H G Hl ⬝e* _ ⬝e* (ωStabilize_of_le_beta H' G' Hl')⁻¹ᵉ*,
  induction p,
  exact nStabilize_pequiv _ _ e
end

definition ωForget_ωStabilize_of_le (H : k ≥ n + 2) (G : [n;k]GType) :
  B (ωForget k (ωStabilize_of_le H G)) ≃* B G :=
ωStabilize_of_le_beta H _ (le.refl k)

definition ωStabilize (G : [n;k]GType) : [n;ω]GType :=
ωStabilize_of_le !le_max_left (nStabilize !le_max_right G)

definition ωForget_ωStabilize (H : k ≥ n + 2) (G : [n;k]GType) :
  B (ωForget k (ωStabilize G)) ≃* B G :=
begin
  refine _ ⬝e* ωForget_ωStabilize_of_le H G,
  esimp [ωForget, ωStabilize],
  have H' : max (n + 2) k = k, from max_eq_right H,
  exact ωStabilize_of_le_pequiv !le_max_left H (nStabilize_pequiv_of_eq _ H'⁻¹ _)
          k (le_of_eq H') (le.refl k) H'
end

/-
definition ωStabilize_adjoint_ωForget (G : [n;k]GType) (H : [n;ω]GType) :
  ωGType_hom (ωStabilize G) H ≃* ppmap (B G) (B (ωForget k H)) :=
sorry

definition ωStabilize_ωForget (G : [n;ω]GType) (l : ℕ) :
  oB (ωStabilize (ωForget k G)) l ≃* oB G l :=
begin
  exact sorry
end

definition ωstabilization (H : k ≥ n + 2) : is_equiv (@ωStabilize n k) :=
begin
  apply adjointify _ (ωForget k),
  { intro G', exact sorry },
  { intro G, apply GType_eq, exact ωForget_ωStabilize H G }
end
-/

definition is_trunc_GType_hom (G H : [n;k]GType) : is_trunc n (GType_hom G H) :=
is_trunc_pmap_of_is_conn _ (k.-2) _ _ (k + n) _ (le_of_eq (sub_one_add_plus_two_sub_one k n)⁻¹)
  (is_trunc_B' H)

definition is_set_GType_hom (G H : [0;k]GType) : is_set (GType_hom G H) :=
is_trunc_GType_hom G H

definition is_trunc_GType (n k : ℕ) : is_trunc (n + 1) [n;k]GType :=
begin
  apply @is_trunc_equiv_closed_rev _ _ (n + 1) (GType_equiv n k),
  apply is_trunc_succ_intro, intros X Y,
  apply @is_trunc_equiv_closed_rev _ _ _ (ptruncconntype_eq_equiv X Y),
  apply @is_trunc_equiv_closed_rev _ _ _ (pequiv.sigma_char_pmap X Y),
  apply @is_trunc_subtype (X →* Y) (λ f, trunctype.mk' -1 (is_equiv f)),
  exact is_trunc_GType_hom ((GType_equiv n k)⁻¹ᵉ X) ((GType_equiv n k)⁻¹ᵉ Y)
end

local attribute [instance] is_set_GType_hom

definition cGType [constructor] (k : ℕ) : Precategory :=
pb_Precategory (cptruncconntype' (k.-1))
               (GType_equiv 0 k ⬝e ptruncconntype_equiv (ap of_nat (zero_add k)) idp ⬝e
                 (ptruncconntype'_equiv_ptruncconntype (k.-1))⁻¹ᵉ)

example (k : ℕ) : Precategory.carrier (cGType k) = [0;k]GType := by reflexivity
example (k : ℕ) (G H : cGType k) : (G ⟶ H) = (B G →* B H) := by reflexivity

definition cGType_equivalence_cType [constructor] (k : ℕ) : cGType k ≃c cType*[k.-1] :=
!pb_Precategory_equivalence_of_equiv

definition cGType_equivalence_Grp [constructor] : cGType.{u} 1 ≃c Grp.{u} :=
equivalence.trans !pb_Precategory_equivalence_of_equiv
                  (equivalence.trans (equivalence.symm Grp_equivalence_cptruncconntype')
                    proof equivalence.refl _ qed)

definition cGType_equivalence_AbGrp [constructor] (k : ℕ) : cGType.{u} (k+2) ≃c AbGrp.{u} :=
equivalence.trans !pb_Precategory_equivalence_of_equiv
                  (equivalence.trans (equivalence.symm (AbGrp_equivalence_cptruncconntype' k))
                    proof equivalence.refl _ qed)

/-
print axioms GType_equiv
print axioms InfGType_equiv
print axioms Decat_adjoint_Disc
print axioms Decat_adjoint_Disc_natural
print axioms InfDecat_adjoint_InfDisc
print axioms InfDecat_adjoint_InfDisc_natural
print axioms Deloop_adjoint_Loop
print axioms Deloop_adjoint_Loop_natural
print axioms Stabilize_adjoint_Forget
print axioms Stabilize_adjoint_Forget_natural
print axioms stabilization
print axioms is_trunc_GType
print axioms cGType_equivalence_Grp
print axioms cGType_equivalence_AbGrp
-/

end higher_group
