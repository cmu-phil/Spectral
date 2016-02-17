/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Finite ordinal types.
-/

import types.fin

open eq nat fin algebra

inductive is_succ [class] : ℕ → Type :=
| mk : Πn, is_succ (succ n)

attribute is_succ.mk [instance]

definition is_succ_add_right [instance] (n m : ℕ) [H : is_succ m] : is_succ (n+m) :=
by induction H with m; constructor

definition is_succ_add_left (n m : ℕ) [H : is_succ n] : is_succ (n+m) :=
by induction H with n; cases m with m: constructor

definition is_succ_bit0 [instance] (n : ℕ) [H : is_succ n] : is_succ (bit0 n) :=
by induction H with n; constructor


namespace fin

  definition my_succ {n : ℕ} (x : fin n) : fin n :=
  begin
    cases n with n,
    { exfalso, apply not_lt_zero _ (is_lt x)},
    { exact
      if H : val x = n
        then fin.mk 0 !zero_lt_succ
        else fin.mk (nat.succ (val x)) (succ_lt_succ (lt_of_le_of_ne (le_of_lt_succ (is_lt x)) H))}
  end

  protected definition add {n : ℕ} (x y : fin n) : fin n :=
  iterate my_succ (val y) x

  definition has_zero_fin [instance] (n : ℕ) [H : is_succ n] : has_zero (fin n) :=
  by induction H with n; exact has_zero.mk (fin.zero n)

  definition has_one_fin [instance] (n : ℕ) [H : is_succ n] : has_one (fin n) :=
  by induction H with n; exact has_one.mk (my_succ (fin.zero n))

  definition has_add_fin [instance] (n : ℕ) : has_add (fin n) :=
  has_add.mk fin.add

  -- definition my_succ_eq_zero {n : ℕ} (x : fin (nat.succ n)) (p : val x = n) : my_succ x = 0 :=
  -- if H : val x = n
  --   then fin.mk 0 !zero_lt_succ
  --   else fin.mk (nat.succ (val x)) (succ_lt_succ (lt_of_le_of_ne (le_of_lt_succ (is_lt x)) H))



end fin
