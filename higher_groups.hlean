/-
Copyright (c) 2015 Ulrik Buchholtz, Egbert Rijke and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke, Floris van Doorn

Formalization of the higher groups paper
-/

import .move_to_lib
open eq is_conn pointed is_trunc trunc equiv is_equiv trunc_index susp nat algebra
namespace higher_group

  /- We require that the carrier has a point (preserved by the equivalence) -/

  structure Grp.{u} (n k : ℕ) : Type.{u+1} := /- (n,k)Grp, denoted here as [n;k]Grp -/
    (car : ptrunctype.{u} n)
    (B : pconntype.{u} k)
    (e : car ≃* Ω[k] B)

  structure InfGrp.{u} (k : ℕ) : Type.{u+1} := /- (∞,k)Grp, denoted here as [∞;k]Grp -/
    (car : pType.{u})
    (B : pconntype.{u} k)
    (e : car ≃* Ω[k] B)

  structure ωGrp (n : ℕ) := /- (n,ω)Grp, denoted here as [n;ω]Grp -/
    (B : Π(k : ℕ), (n+k)-Type*[k])
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
  lemma is_trunc_B (G : [n;k]Grp) : is_trunc (n+k) (B G) :=
  sorry

  /- some equivalences -/
  definition Grp_equiv (n k : ℕ) : [n;k]Grp ≃ (n+k)-Type*[k] :=
  sorry

  definition InfGrp_equiv (k : ℕ) : [∞;k]Grp ≃ Type*[k] :=
  sorry

  -- maybe to do: ωGrp ≃ Σ(X : spectrum), is_sconn n X

  /- Constructions -/
  definition Decat (G : [n+1;k]Grp) : [n;k]Grp :=
  Grp.mk (ptrunctype.mk (ptrunc n G) _ pt) (pconntype.mk (ptrunc (n +[ℕ₋₂] k) (B G)) _ pt)
    abstract begin
      refine ptrunc_pequiv_ptrunc n (e G) ⬝e* _,
      symmetry, exact !loopn_ptrunc_pequiv
    end end

  definition Disc (G : [n;k]Grp) : [n+1;k]Grp :=
  Grp.mk (ptrunctype.mk G (show is_trunc (n.+1) G, from _) pt) (B G) (e G)

  definition Disc_adjoint_Decat (G : [n;k]Grp) (H : [n+1;k]Grp) :
    ppmap (B (Disc G)) (B H) ≃* ppmap (B G) (B (Decat H)) :=
  sorry
  /- To do: naturality -/

  definition Decat_Disc (G : [n;k]Grp) : Decat (Disc G) = G :=
  sorry

  definition InfDecat (n : ℕ) (G : [∞;k]Grp) : [n;k]Grp :=
  Grp.mk (ptrunctype.mk (ptrunc n G) _ pt) (pconntype.mk (ptrunc (n +[ℕ₋₂] k) (iB G)) _ pt)
    abstract begin
      refine ptrunc_pequiv_ptrunc n (ie G) ⬝e* _,
      symmetry, exact !loopn_ptrunc_pequiv
    end end

  definition InfDisc (n : ℕ) (G : [n;k]Grp) : [∞;k]Grp :=
  InfGrp.mk G (B G) (e G)

  definition InfDisc_adjoint_InfDecat (G : [n;k]Grp) (H : [∞;k]Grp) :
    ppmap (iB (InfDisc n G)) (iB H) ≃* ppmap (B G) (B (InfDecat n H)) :=
  sorry
  /- To do: naturality -/

  definition InfDecat_InfDisc (G : [n;k]Grp) : InfDecat n (InfDisc n G) = G :=
  sorry

  definition Loop (G : [n+1;k]Grp) : [n;k+1]Grp :=
  have is_trunc (n.+1) G, from !is_trunc_ptrunctype,
  Grp.mk (ptrunctype.mk (Ω G) !is_trunc_loop pt)
    sorry
    abstract begin
      exact sorry
    end end

  definition Deloop (G : [n;k+1]Grp) : [n+1;k]Grp :=
  have is_conn (k.+1) (B G), from !is_conn_pconntype,
  have is_trunc (n + (k + 1)) (B G), from is_trunc_B G,
  have is_trunc (n +[ℕ] 1 +[ℕ₋₂] k) (pconntype.to_pType (B G)), from transport (λn, is_trunc n _)
    (ap trunc_index.of_nat (nat.succ_add n k)⁻¹ ⬝ !of_nat_add_of_nat⁻¹) this,
  have is_trunc (n + 1) (Ω[k] (B G)), from !is_trunc_loopn,
  Grp.mk (ptrunctype.mk (Ω[k] (B G)) _ pt)
    (pconntype.mk (B G) !is_conn_of_is_conn_succ pt)
    (pequiv_of_equiv erfl idp)

  /- to do: adjunction, and Loop ∘ Deloop = id -/

  definition Forget (G : [n;k+1]Grp) : [n;k]Grp :=
  have is_conn (k.+1) (B G), from !is_conn_pconntype,
  Grp.mk G (pconntype.mk (Ω (B G)) !is_conn_loop pt)
    abstract begin
      refine e G ⬝e* !loopn_succ_in
    end end

  definition Stabilize (G : [n;k]Grp) : [n;k+1]Grp :=
  have is_conn (k+1) (susp (B G)), from !is_conn_susp,
  have Hconn : is_conn (k+1) (ptrunc (n + k + 1) (susp (B G))), from !is_conn_ptrunc,
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
