# Spectral Sequences

Formalization project of the CMU HoTT group towards formalizing the Serre spectral sequence.

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

These projects are mostly done

- Given a sequence of spectra and maps, indexed over `ℤ`, we get an exact couple, indexed over `ℤ × ℤ`.
- We can derive an exact couple.
- If the exact couple is bounded, we repeat this process to get a convergent spectral sequence.
- We construct the Atiyah-Hirzebruch and Serre spectral sequences for cohomology.

### Future directions
- Hurewicz Theorem and Hurewicz theorem modulo a Serre class.
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
- Cup product on cohomology groups
- Parametrized and unreduced homology
- Steenrod squares
- ...

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
- Most things in the HoTT Book up to Section 8.9 (see [this file](https://github.com/leanprover/lean/blob/master/hott/book.md))
- pointed types, maps, homotopies and equivalences
- [Eilenberg-MacLane spaces](http://ncatlab.org/nlab/show/Eilenberg-Mac+Lane+space) and EM-spectrum
- fiber sequence
  + already have the LES
  + need shift isomorphism
  + Hom'ing into a fiber sequence gives another fiber sequence.
- long exact sequence of homotopy groups of spectra, indexed on ℤ
- exact couple of a tower of spectra
  + need to splice together LES's
