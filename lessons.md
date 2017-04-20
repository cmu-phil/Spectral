Things I would do differently with hindsight:

* Make pointed dependent maps primitive:
```lean
structure ppi (A : Type*) (P : A → Type) (p : P pt) :=
  (to_fun : Π a : A, P a)
  (resp_pt : to_fun (Point A) = p)
```
(maybe the last argument should be `[p : pointed (P pt)]`). Define pointed (non-dependent) maps as a special case.
Note: assuming `P : A → Type*` is not general enough.

* Use squares, also for maps, pointed maps, ... heavily

* Type classes for equivalences don't really work

* Coercions should all be defined *immediately* after defining a structure, *before* declaring any
  instances. This is because the coercion graph is updated after each declared coercion.

* [maybe] make bundled structures primitive
