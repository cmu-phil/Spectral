In this file I (Floris) will collect some lessons learned from building and working with a HoTT library.
Some of these things still need to be changes, some of them are already changed, and some of them are not worth the effort to change.

- Spheres should be indexed by ℕ, it is not worth the effort to start counting at -1 (pointed spheres are much more useful anyway).
- I think the type `trunc_index` / `ℕ₋₂` is superfluous and `ℤ` should be used instead (defined so that `is_trunc n A`and `trunc n A is` constant for `n ≤ -2`). This saves defining operations and proving properties on an additional type, and it is useful when defining truncations / truncatedness for spectra, which are naturally indexed by `ℤ`.
- Don't have both susp and psusp. psusp should be the default (otherwise there is a distinction between iterate susp and iterate psusp)
- Pointed maps should be special cases of dependent pointed maps. Pointed homotopies (between dependent pointed maps) should be special cases of dependent pointed maps, and pointed homotopies should be related themselves by pointed homotopies.
- Type classes don't work well together with bundled structures and coercions in Lean (the instance is_contr_unit will not unify with (is_contr punit).
- Overloading doesn't work well in Lean (mostly by degrading error messages)
- avoid rec_on, don't formulate induction principles using "on", the order of arguments is worse
- squares of maps, pointed maps and similar objects should be defined with operations on them. Squares of maps should be a structure, because we don't want that `hsquare t b l r` is definitionally equal to `hsquare (r ∘ t) b l id`.
- It is useful to do categorical properties more uniformly. Define a 1-coherent ∞-category, which is a precategory (or category?) where the homs are not assumed to be sets. Examples include
  + `Type` (with `→`),
  + `A → B` (with `~`),
  + `Type*` (with `→*`),
  + `A →* B` (with `~*`),
  + `A` (with `=`),
  + spectrum (with `→ₛ`)
  + ...
  You cannot formulate everything in this, but it would be useful to compose natural transformations (instead of composing functions and manually show naturality).
  Disadvantage: doesn't work for everything, at some point you have to resort to higher categorical reasoning. Also, it might be challenging to formulate things like functoriality of pi's and sigma's.
- Type class inference for equivalences doesn't really work in Lean, since it recognizes that `f ∘ id` is definitionally `f`, hence it can always apply `is_equiv_compose` and get trapped in a loop.
- Coercions should all be defined *immediately* after defining a structure, *before* declaring any
  instances. This is because the coercion graph is updated after each declared coercion.
