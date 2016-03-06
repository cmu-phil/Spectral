# Spectral Sequences

Formalization project of the CMU HoTT group towards formalizing the Serre spectral sequence.

#### Participants
Jeremy Avigad, Steve Awodey, Ulrik Buchholtz, Floris van Doorn, Clive Newstead, Egbert Rijke, Mike Shulman.

## Resources
- [Mike's blog post](http://homotopytypetheory.org/2013/08/08/spectral-sequences/) at the HoTT blog.
- [Mike's blog post](https://golem.ph.utexas.edu/category/2013/08/what_is_a_spectral_sequence.html) at the n-category café.
- The [Licata-Finster article](http://dlicata.web.wesleyan.edu/pubs/lf14em/lf14em.pdf) about Eilenberg-Mac Lane spaces.
- We learned about the Serre spectral sequence from [Hatcher's chapter about spectral sequences](https://www.math.cornell.edu/~hatcher/SSAT/SSATpage.html).
- Lang's algebra (revised 3rd edition) contains a chapter on general homology theory, with a section on spectral sequences. Thus, we can use this book at least as an outline for the algebraic part of the project.
- Mac Lane's Homology contains a lot of homological algebra and a chapter on spectral sequences, including exact couples.

## Things to do for Lean spectral sequences project

### Algebra To Do:
- [R-modules](http://ncatlab.org/nlab/show/module), [vector spaces](http://ncatlab.org/nlab/show/vector+space),
- some basic theory: product, tensor, hom, projective,
- categories of algebras, [abelian categories](http://ncatlab.org/nlab/show/abelian+category),
- exact sequences, short and long
- [snake lemma](http://ncatlab.org/nlab/show/snake+lemma)
- [5-lemma](http://ncatlab.org/nlab/show/five+lemma)
- [chain complexes](http://ncatlab.org/nlab/show/chain+complex) and [homology](http://ncatlab.org/nlab/show/homology)
- [exact couples](http://ncatlab.org/nlab/show/exact+couple), probably just of Z-graded objects, and derived exact couples
- spectral sequence of an exact couple
- [convergence of spectral sequences](http://ncatlab.org/nlab/show/spectral+sequence#ConvergenceOfSpectralSequences)

### Topology To Do:
- HoTT Book sections 8.7, 8.8.
- cofiber sequences
- [prespectra](http://ncatlab.org/nlab/show/spectrum+object) and [spectra](http://ncatlab.org/nlab/show/spectrum), suspension
- [spectrification](http://ncatlab.org/nlab/show/higher+inductive+type#spectrification)
- [parametrized spectra](http://ncatlab.org/nlab/show/parametrized+spectrum), parametrized smash and hom between types and spectra
- fiber and cofiber sequences of spectra, stability
- long exact sequences from (co)fiber sequences of spectra
- [Eilenberg-MacLane spaces](http://ncatlab.org/nlab/show/Eilenberg-Mac+Lane+space) and spectra
- Postnikov towers of spectra
- exact couple of a tower of spectra

### Already Done:
- Most things in the HoTT Book up to Section 8.6 (see [this file](https://github.com/leanprover/lean/blob/master/hott/book.md))
- pointed types, maps, homotopies and equivalences
- definition of algebraic structures such as groups, rings, fields
- some algebra: quotient, product, free groups.