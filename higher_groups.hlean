/-
Copyright (c) 2015 Ulrik Buchholtz, Egbert Rijke and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke, Floris van Doorn

Formalization of the higher groups paper
-/

import .move_to_lib
open eq is_conn pointed is_trunc trunc equiv is_equiv trunc_index susp nat algebra prod.ops sigma sigma.ops
namespace higher_group
set_option pp.binder_types true

  /- We require that the carrier has a point (preserved by the equivalence) -/

  structure Grp.{u} (n k : ℕ) : Type.{u+1} := /- (n,k)Grp, denoted here as [n;k]Grp -/
    (car : ptrunctype.{u} n)
    (B : pconntype.{u} (k.-1))
    (e : car ≃* Ω[k] B)

  structure InfGrp.{u} (k : ℕ) : Type.{u+1} := /- (∞,k)Grp, denoted here as [∞;k]Grp -/
    (car : pType.{u})
    (B : pconntype.{u} (k.-1))
    (e : car ≃* Ω[k] B)

  structure ωGrp (n : ℕ) := /- (n,ω)Grp, denoted here as [n;ω]Grp -/
    (B : Π(k : ℕ), (n+k)-Type*[k.-1])
    (e : Π(k : ℕ), B k ≃* Ω (B (k+1)))

  attribute InfGrp.car Grp.car [coercion]

  variables {n k l : ℕ}
  notation `[`:95 n:0 `; ` k `]Grp`:0 := Grp n k
  notation `[∞; `:95 k:0 `]Grp`:0 := InfGrp k
  notation `[`:95 n:0 `;ω]Grp`:0 := ωGrp n

  open Grp
  open InfGrp (renaming B→iB e→ie)
  open ωGrp (renaming B→oB e→oe)

  /- some basic properties -/
  lemma is_trunc_B' (G : [n;k]Grp) : is_trunc (k+n) (B G) :=
  begin
    apply is_trunc_of_is_trunc_loopn,
    exact is_trunc_equiv_closed _ (e G),
    exact _
  end

  lemma is_trunc_B (G : [n;k]Grp) : is_trunc (n+k) (B G) :=
  transport (λm, is_trunc m (B G)) (add.comm k n) (is_trunc_B' G)

  local attribute [instance] is_trunc_B

  /- some equivalences -/
  definition Grp_equiv (n k : ℕ) : [n;k]Grp ≃ (n+k)-Type*[k.-1] :=
  let f : Π(B : Type*[k.-1]) (H : Σ(X : n-Type*), X ≃* Ω[k] B), (n+k)-Type*[k.-1] :=
    λB' H, ptruncconntype.mk B' (is_trunc_B (Grp.mk H.1 B' H.2)) pt _
  in
  calc
    [n;k]Grp ≃ Σ(B : Type*[k.-1]), Σ(X : n-Type*), X ≃* Ω[k] B : sorry
         ... ≃ Σ(B : (n+k)-Type*[k.-1]), Σ(X : n-Type*), X ≃* Ω[k] B :
               @sigma_equiv_of_is_embedding_left _ _ _ sorry ptruncconntype.to_pconntype sorry
                 (λB' H, fiber.mk (f B' H) sorry)
         ... ≃ Σ(B : (n+k)-Type*[k.-1]), Σ(X : n-Type*),
                 X = ptrunctype_of_pType (Ω[k] B) !is_trunc_loopn_nat :> n-Type* :
               sigma_equiv_sigma_right (λB, sigma_equiv_sigma_right (λX, sorry))
         ... ≃ (n+k)-Type*[k.-1] : sigma_equiv_of_is_contr_right

  definition Grp_eq_equiv {n k : ℕ} (G H : [n;k]Grp) : (G = H) ≃ (B G ≃* B H) :=
  sorry

  definition Grp_eq {n k : ℕ} {G H : [n;k]Grp} (e : B G ≃* B H) : G = H :=
  (Grp_eq_equiv G H)⁻¹ᵉ e

  definition InfGrp_equiv (k : ℕ) : [∞;k]Grp ≃ Type*[k.-1] :=
  sorry

  -- maybe to do: ωGrp ≃ Σ(X : spectrum), is_sconn n X

  /- Constructions -/
  definition Decat (G : [n+1;k]Grp) : [n;k]Grp :=
  Grp.mk (ptrunctype.mk (ptrunc n G) _ pt) (pconntype.mk (ptrunc (n + k) (B G)) _ pt)
    abstract begin
      refine ptrunc_pequiv_ptrunc n (e G) ⬝e* _,
      symmetry, exact sorry --!loopn_ptrunc_pequiv
    end end

  definition Disc (G : [n;k]Grp) : [n+1;k]Grp :=
  Grp.mk (ptrunctype.mk G (show is_trunc (n.+1) G, from _) pt) (B G) (e G)

  definition Decat_adjoint_Disc (G : [n+1;k]Grp) (H : [n;k]Grp) :
    ppmap (B (Decat G)) (B H) ≃* ppmap (B G) (B (Disc H)) :=
  pmap_ptrunc_pequiv (n + k) (B G) (B H)

  definition Decat_adjoint_Disc_natural {G G' : [n+1;k]Grp} {H H' : [n;k]Grp}
    (eG : B G' ≃* B G) (eH : B H ≃* B H') :
    psquare (Decat_adjoint_Disc G H)
            (Decat_adjoint_Disc G' H')
            (ppcompose_left eH ∘* ppcompose_right (ptrunc_functor _ eG))
            (ppcompose_left eH ∘* ppcompose_right eG) :=
  sorry

  definition Decat_Disc (G : [n;k]Grp) : Decat (Disc G) = G :=
  Grp_eq !ptrunc_pequiv

  definition InfDecat (n : ℕ) (G : [∞;k]Grp) : [n;k]Grp :=
  Grp.mk (ptrunctype.mk (ptrunc n G) _ pt) (pconntype.mk (ptrunc (n + k) (iB G)) _ pt)
    abstract begin
      refine ptrunc_pequiv_ptrunc n (ie G) ⬝e* _,
      symmetry, exact !loopn_ptrunc_pequiv_nat
    end end

  definition InfDisc (n : ℕ) (G : [n;k]Grp) : [∞;k]Grp :=
  InfGrp.mk G (B G) (e G)

  definition InfDecat_adjoint_InfDisc (G : [∞;k]Grp) (H : [n;k]Grp) :
    ppmap (B (InfDecat n G)) (B H) ≃* ppmap (iB G) (iB (InfDisc n H)) :=
  pmap_ptrunc_pequiv (n + k) (iB G) (B H)

  /- To do: naturality -/

  definition InfDecat_InfDisc (G : [n;k]Grp) : InfDecat n (InfDisc n G) = G :=
  sorry

  definition Loop (G : [n+1;k]Grp) : [n;k+1]Grp :=
  Grp.mk (ptrunctype.mk (Ω G) !is_trunc_loop_nat pt)
    (connconnect k (B G))
    (loop_pequiv_loop (e G) ⬝e* (loopn_connect k (B G))⁻¹ᵉ*)

  definition Deloop (G : [n;k+1]Grp) : [n+1;k]Grp :=
  have is_conn k (B G), from is_conn_pconntype (B G),
  have is_trunc (n + (k + 1)) (B G), from is_trunc_B G,
  have is_trunc ((n + 1) + k) (B G), from transport (λ(n : ℕ), is_trunc n _) (succ_add n k)⁻¹ this,
  Grp.mk (ptrunctype.mk (Ω[k] (B G)) !is_trunc_loopn_nat pt)
    (pconntype.mk (B G) !is_conn_of_is_conn_succ pt)
    (pequiv_of_equiv erfl idp)

  /- to do: adjunction, and Loop ∘ Deloop = id -/

  definition Forget (G : [n;k+1]Grp) : [n;k]Grp :=
  have is_conn k (B G), from !is_conn_pconntype,
  Grp.mk G (pconntype.mk (Ω (B G)) !is_conn_loop pt)
    abstract begin
      refine e G ⬝e* !loopn_succ_in
    end end

  definition Stabilize (G : [n;k]Grp) : [n;k+1]Grp :=
  have is_conn k (susp (B G)), from !is_conn_susp,
  have Hconn : is_conn k (ptrunc (n + k + 1) (susp (B G))), from !is_conn_ptrunc,
  Grp.mk (ptrunctype.mk (ptrunc n (Ω[k+1] (susp (B G)))) _ pt)
    (pconntype.mk (ptrunc (n+k+1) (susp (B G))) Hconn pt)
    abstract begin
      refine !loopn_ptrunc_pequiv⁻¹ᵉ* ⬝e* _,
      apply loopn_pequiv_loopn,
      exact ptrunc_change_index !of_nat_add_of_nat _
    end end

  /- to do: adjunction -/

  definition ωForget (k : ℕ) (G : [n;ω]Grp) : [n;k]Grp :=
  have is_trunc (n + k) (oB G k), from _,
  have is_trunc (n +[ℕ₋₂] k) (oB G k), from transport (λn, is_trunc n _) !of_nat_add_of_nat⁻¹ this,
  have is_trunc n (Ω[k] (oB G k)), from !is_trunc_loopn,
  Grp.mk (ptrunctype.mk (Ω[k] (oB G k)) _ pt) (oB G k) (pequiv_of_equiv erfl idp)

  definition nStabilize.{u} (H : k ≤ l) (G : Grp.{u} n k) : Grp.{u} n l :=
  begin
    induction H with l H IH, exact G, exact Stabilize IH
  end

  theorem stabilization (H : k ≥ n + 2) : is_equiv (@Stabilize n k) :=
  sorry

  definition ωStabilize_of_le (H : k ≥ n + 2) (G : [n;k]Grp) : [n;ω]Grp :=
  ωGrp.mk (λl, sorry) (λl, sorry)

  /- for l ≤ k we want to define it as Ω[k-l] (B G),
     for H : l ≥ k we want to define it as nStabilize H G -/

  definition ωStabilize (G : [n;k]Grp) : [n;ω]Grp :=
  ωStabilize_of_le !le_max_left (nStabilize !le_max_right G)

  /- to do: adjunction (and ωStabilize ∘ ωForget =?= id) -/

end higher_group
