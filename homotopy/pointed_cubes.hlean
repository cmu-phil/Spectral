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

definition psquare_vcompose {A B C D E F : Type*} {ftop : A →* B} {fbot : C →* D} {fleft : A →* C} {fright : B →* D} {gbot : E →* F} {gleft : C →* E} {gright : D →* F} (psq_top : psquare ftop fbot fleft fright) (psq_bot : psquare fbot gbot gleft gright) : psquare ftop gbot (gleft ∘* fleft) (gright ∘* fright) :=
begin
  fapply psquare_of_phomotopy,
  refine (passoc gright fright ftop) ⬝* _ ⬝* (passoc gbot gleft fleft),
  refine (pwhisker_left gright psq_top) ⬝* _,
  refine (passoc gright fbot fleft)⁻¹* ⬝* _,
  exact pwhisker_right fleft psq_bot,
end

definition psquare_of_pconst_top_bot {A B C D : Type*} (fleft : A →* C) (fright : B →* D) : psquare (pconst A B) (pconst C D) fleft fright :=
begin
  fapply psquare_of_phomotopy,
  refine (pcompose_pconst fright) ⬝* _,
  exact (pconst_pcompose fleft)⁻¹*,
end

definition psquare_of_pconst_left_right {A B C D : Type*} (ftop : A →* B) (fbot : C →* D) : psquare ftop fbot (pconst A C) (pconst B D) :=
begin
  fapply psquare_of_phomotopy,
  refine (pconst_pcompose ftop) ⬝* _,
  exact (pcompose_pconst fbot)⁻¹*
end

definition psquare_of_pconst_top_left {A B C D : Type*} (fbot : C →* D) (fright : B →* D) : psquare (pconst A B) fbot (pconst A C) fright :=
begin
  fapply psquare_of_phomotopy,
  refine (pcompose_pconst fright) ⬝* _,
  exact (pcompose_pconst fbot)⁻¹*,
end

definition psquare_of_pconst_bot_right {A B C D : Type*} (ftop : A →* B) (fleft : A →* C) : psquare ftop (pconst C D) fleft (pconst B D) :=
begin
  fapply psquare_of_phomotopy,
  refine (pconst_pcompose ftop) ⬝* _,
  exact (pconst_pcompose fleft)⁻¹*,
end

definition ptube_v {A B C D : Type*} {ftop ftop' : A →* B} (phtpy_top : ftop ~* ftop') {fbot fbot' : C →* D} (phtpy_bot : fbot ~* fbot') {fleft : A →* C} {fright : B →* D} (psq_back : psquare ftop fbot fleft fright) (psq_front : psquare ftop' fbot' fleft fright) : Type :=
phsquare (pwhisker_left fright phtpy_top) (pwhisker_right fleft phtpy_bot) psq_back psq_front

definition ptube_h {A B C D : Type*} {ftop : A →* B} {fbot : C →* D} {fleft fleft' : A →* C} (phtpy_left : fleft ~* fleft') {fright fright' : B →* D} (phtpy_right : fright ~* fright') (psq_back : psquare ftop fbot fleft fright) (psq_front : psquare ftop fbot fleft' fright') : Type :=
phsquare (pwhisker_right ftop phtpy_right) (pwhisker_left fbot phtpy_left) psq_back psq_front
