In this file I (Floris) will collect some lessons learned from building and working with a HoTT library.
Some of these things still need to be changes, some of them are already changed, and some of them are not worth the effort to change.

- Spheres should be indexed by ℕ, it is not worth the effort to start counting at -1 (pointed spheres are much more useful anyway).
- Don't have both susp and psusp. psusp should be the default (otherwise there is a distinction between iterate susp and iterate psusp)
- Pointed maps should be special cases of dependent pointed maps. Pointed homotopies (between dependent pointed maps) should be special cases of dependent pointed maps, and pointed homotopies should be related themselves by pointed homotopies.
- Type classes don't work well together with bundled structures and coercions in Lean (the instance is_contr_unit will not unify with (is_contr punit).
- Overloading doesn't work well in Lean (mostly by degrading error messages)
- It is useful to do categorical properties more uniformly. Define a 1-coherent ∞-category, which is a precategory (or category?) where the homs are not assumed to be sets. Examples include
  + `Type` (with `→`),
  + `A → B` (with `~`),
  + `Type*` (with `→*`),
  + `A →* B` (with `~*`),
  + `A` (with `=`),
  + spectrum (with `→ₛ`)
  + ...
  You cannot formulate everything in this, but it would be useful to compose natural transformations (instead of composing functions and manually show naturality).
  Disadvantage: doesn't work
