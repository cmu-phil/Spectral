# Spectral Sequences in Homotopy Type Theory

Formalization project of the CMU HoTT group to formalize the Serre spectral sequence in Lean 2.

*Update July 16, 2017*: The construction of the Serre spectral sequence has been completed. The result is `serre_convergence` in `cohomology.serre`.
The main algebra part is in `algebra.exact_couple`.

This repository also contains: 
* a formalization of colimits which is in progress by Floris van Doorn, Egbert Rijke and Kristina Sojakova.
* a formalization and notes (in progress) about the smash product by Floris van Doorn and Stefano Piceghello.
* a formalization of *The real projective spaces in homotopy type theory*, Ulrik Buchholtz and Egbert Rijke, LICS 2017.
* a formalization of *Higher Groups in Homotopy Type Theory*, Ulrik Buchholtz, Floris van Doorn, Egbert Rijke, LICS 2018.
* the contents of the MRC 2017 group on formalizing homology in Lean.

#### Participants
Jeremy Avigad, Steve Awodey, Ulrik Buchholtz, Floris van Doorn, Clive Newstead, Egbert Rijke, Mike Shulman.

## Resources
- [Mike's blog posts on ncatlab](https://ncatlab.org/homotopytypetheory/show/spectral+sequences).
- The [Licata-Finster article](http://dlicata.web.wesleyan.edu/pubs/lf14em/lf14em.pdf) about Eilenberg-Mac Lane spaces.
- We learned about the Serre spectral sequence from [Hatcher's chapter about spectral sequences](https://www.math.cornell.edu/~hatcher/SSAT/SSATpage.html).
- Lang's algebra (revised 3rd edition) contains a chapter on general homology theory, with a section on spectral sequences. Thus, we can use this book at least as an outline for the algebraic part of the project.
- Mac Lane's Homology contains a lot of homological algebra and a chapter on spectral sequences, including exact couples.

## Contents for Lean spectral sequences project

### Outline

These projects are done

- Given a sequence of spectra and maps, indexed over `ℤ`, we get an exact couple, indexed over `ℤ × ℤ`.
- We can derive an exact couple.
- If the exact couple is bounded, we repeat this process to get a convergent spectral sequence.
- We construct the Atiyah-Hirzebruch and Serre spectral sequences for cohomology.

### Future directions
- Hurewicz Theorem and Hurewicz theorem modulo a Serre class. There is a proof in Hatcher. Also, [this](http://www.math.uni-frankfurt.de/~johannso/SkriptAll/SkriptTopAlg/SkriptTopCW/homotop12.pdf) might be useful.
- Homological Serre spectral sequence.
- Interaction between steenrod squares and cup product with spectral sequences
- ...

### Algebra

#### To do
- Constructions: tensor, hom, projective, Tor (at least on groups)
- Finite groups, Finitely generated groups, torsion groups
- Serre classes
- [vector spaces](http://ncatlab.org/nlab/show/vector+space),

#### In Progress


#### Done
- groups, rings, fields, [R-modules](http://ncatlab.org/nlab/show/module), graded R-modules.
- Constructions on groups and abelian groups:: subgroup, quotient, product, free groups.
- Constructions on ablian groups: direct sum, sequential colimi.
- exact sequences, short and long.
- [chain complexes](http://ncatlab.org/nlab/show/chain+complex) and [homology](http://ncatlab.org/nlab/show/homology).
- [exact couples](http://ncatlab.org/nlab/show/exact+couple) graded over an arbitrary indexing set.
- spectral sequence of an exact couple.
- [convergence of spectral sequences](http://ncatlab.org/nlab/show/spectral+sequence#ConvergenceOfSpectralSequences).

### Topology

#### To do
- cofiber sequences
  + Hom'ing out gives a fiber sequence: if `A → B → coker f` cofiber
    sequences, then `X^A → X^B → X^(coker f)` is a fiber sequence.
- fiber and cofiber sequences of spectra, stability
  + limits are levelwise
  + colimits need to be spectrified
- long exact sequence from cofiber sequences of spectra
  + indexed on ℤ, need to splice together LES's
- Parametrized and unreduced homology
- Cup product on cohomology groups
- Show that the spectral sequence respect the cup product structure of cohomology
- Steenrod squares
- ...

#### To do (short-term easy projects)

- Compute cohomology groups of `K(ℤ, n)`
- Compute cohomology groups of `ΩSⁿ`
- Show that all fibration sequences between spheres are of the form `Sⁿ → S²ⁿ⁺¹ → Sⁿ⁺¹`.
- Compute fiber of `K(φ, n)` for group hom `φ` in general and if it's injective/surjective
- [Steve] Prove `Σ (X × Y) ≃* Σ X ∨ Σ Y ∨ Σ (X ∧ Y)`, where `Σ` is suspension. See `homotopy.susp_product`

#### In Progress
- [prespectra](http://ncatlab.org/nlab/show/spectrum+object) and [spectra](http://ncatlab.org/nlab/show/spectrum), indexed over an arbitrary type with a successor
  + think about equivariant spectra indexed by representations of `G`
- [spectrification](http://ncatlab.org/nlab/show/higher+inductive+type#spectrification)
  + adjoint to forgetful
  + as sequential colimit, prove induction principle
  + connective spectrum: `is_conn n.-2 Eₙ`
- Postnikov towers of spectra.
  + basic definition already there
  + fibers of Postnikov sequence unstably and stably
- [parametrized spectra](http://ncatlab.org/nlab/show/parametrized+spectrum), parametrized smash and hom between types and spectra.
- Check Eilenberg-Steenrod axioms for reduced homology.


#### Done
- Most things in the HoTT Book up to Section 8.9 (see [this file](https://github.com/leanprover/lean2/blob/master/hott/book.md))
- pointed types, maps, homotopies and equivalences
- [Eilenberg-MacLane spaces](http://ncatlab.org/nlab/show/Eilenberg-Mac+Lane+space) and EM-spectrum
- fiber sequence
  + already have the LES
  + need shift isomorphism
  + Hom'ing into a fiber sequence gives another fiber sequence.
- long exact sequence of homotopy groups of spectra, indexed on ℤ
- exact couple of a tower of spectra
  + need to splice together LES's

## Usage and Contributing
- To compile this repository you can run `linja` (or `path/to/lean2/bin/linja`) in the main directory.
  + You will need a working version of Lean 2. Installation instructions for Lean 2 can be found [here](https://github.com/leanprover/lean2).
  + We will try to make sure that this repository compiles with the newest version of Lean 2.
- The preferred editor for Lean 2 is Emacs. Notes on the Emacs mode can be found [here](https://github.com/leanprover/lean2/blob/master/src/emacs/README.md) (for example if some unicode characters don't show up, or increase the spacing between lines by a lot).
- We try to separate the repository into the folders `algebra`, `homotopy`, `homology`, `cohomology`, `spectrum` and `colimit`. Homotopy theotic properties of types which do not explicitly mention homotopy, homology or cohomology groups (such as `A ∧ B ≃* B ∧ A`) are part of `homotopy`.
- If you contribute, please use rebase instead of merge (e.g. `git pull -r`).
