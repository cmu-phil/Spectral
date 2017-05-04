/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Short exact sequences
-/
import .quotient_group
open eq nat int susp pointed pmap sigma is_equiv equiv fiber algebra trunc trunc_index pi group
     is_trunc function sphere unit sum prod

structure is_short_exact {A B : Type} {C : Type*} (f : A → B) (g : B → C) :=
  (is_emb    : is_embedding f)
  (im_in_ker : Π(a:A), g (f a) = pt)
  (ker_in_im : Π(b:B), (g b = pt) → image f b)
  (is_surj   : is_surjective g)

structure is_short_exact_t {A B : Type} {C : Type*} (f : A → B) (g : B → C) :=
  (is_emb    : is_embedding f)
  (im_in_ker : Π(a:A), g (f a) = pt)
  (ker_in_im : Π(b:B), (g b = pt) → fiber f b)
  (is_surj   : is_split_surjective g)

definition is_short_exact_of_is_exact {X A B C Y : Type*}
  (k : X → A) (f : A → B) (g : B → C) (l : C → Y)
  (hX : is_contr X) (hY : is_contr Y)
  (kf : is_exact k f) (fg : is_exact f g) (gl : is_exact g l) : is_short_exact f g :=
sorry

definition is_short_exact_equiv {A B A' B' : Type} {C C' : Type*}
  {f' : A' → B'} {g' : B' → C'} (f : A → B) (g : B → C)
  (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃* C')
  (h : hsquare f f' eA eB) (h : hsquare g g' eB eC)
  (H : is_short_exact f' g') : is_short_exact f g :=
sorry
