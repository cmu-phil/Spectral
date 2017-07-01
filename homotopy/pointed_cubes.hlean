/-
Copyright (c) 2017 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke

-/

/- 
The goal of this file is to extend the library of pointed types and pointed maps to support the library of prespectra 

-/

import types.pointed2

open eq pointed

definition psquare_of_phtpy_top {A B C D : Type*}  {ftop : A →* B} {fbot : C →* D} {fleft : A →* C} {fright : B →* D} {ftop' : A →* B} (phtpy : ftop ~* ftop') (psq : psquare ftop' fbot fleft fright) : psquare ftop fbot fleft fright :=
begin
  induction phtpy using phomotopy_rec_on_idp, exact psq,
end

definition psquare_of_phtpy_bot {A B C D : Type*} {ftop : A →* B} {fbot : C →* D} {fleft : A →* C} {fright : B →* D} {fbot' : C →* D} (phtpy : fbot ~* fbot') (psq : psquare ftop fbot' fleft fright) : psquare ftop fbot fleft fright :=
begin
  induction phtpy using phomotopy_rec_on_idp, exact psq,
end

definition psquare_of_phtpy_left {A B C D : Type*} {ftop : A →* B} {fbot : C →* D} {fleft : A →* C} {fright : B →* D} {fleft' : A →* C} (phtpy : fleft ~* fleft') (psq : psquare ftop fbot fleft fright) : psquare ftop fbot fleft' fright :=
begin
  induction phtpy using phomotopy_rec_on_idp, exact psq,
end

definition psquare_of_phtpy_right {A B C D : Type*} {ftop : A →* B} {fbot : C →* D} {fleft : A →* C} {fright : B →* D} {fright' : B →* D} (phtpy : fright ~* fright') (psq : psquare ftop fbot fleft fright) : psquare ftop fbot fleft fright' :=
begin
  induction phtpy using phomotopy_rec_on_idp, exact psq,
end

definition psquare_of_pid_top_bot {A B : Type*} {fleft : A →* B} {fright : A →* B} (phtpy : fright ~* fleft) : psquare (pid A) (pid B) fleft fright :=
psquare_of_phomotopy ((pcompose_pid fright) ⬝* phtpy ⬝* (pid_pcompose fleft)⁻¹*)

print psquare_of_pid_top_bot

--λ phtpy, psquare_of_phomotopy ((pid_pcompose fleft) ⬝* phtpy ⬝* ((pcompose_pid fright)⁻¹*))

definition psquare_of_pid_left_right {A B : Type*} {ftop : A →* B} {fbot : A →* B} (phtpy : ftop ~* fbot) : psquare ftop fbot (pid A) (pid B) :=
psquare_of_phomotopy ((pid_pcompose ftop) ⬝* phtpy ⬝* ((pcompose_pid fbot)⁻¹*))

print psquare_of_pid_left_right

definition psquare_hcompose {A B C D E F : Type*} {ftop : A →* B} {fbot : D →* E} {fleft : A →* D} {fright : B →* E} {gtop : B →* C} {gbot : E →* F} {gright : C →* F} (psq_left : psquare ftop fbot fleft fright) (psq_right : psquare gtop gbot fright gright) : psquare (gtop ∘* ftop) (gbot ∘* fbot) fleft gright :=
begin
  fapply psquare_of_phomotopy,
  refine (passoc gright gtop ftop)⁻¹* ⬝* _ ⬝* (passoc gbot fbot fleft)⁻¹*,
  refine (pwhisker_right ftop psq_right) ⬝* (passoc gbot fright ftop) ⬝* _,
  exact (pwhisker_left gbot psq_left),
end
