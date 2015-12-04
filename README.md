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

## Things to do for Lean spectral sequences project

### Algebra To Do:
- R-modules, vector spaces,
- some basic theory: product, tensor, hom, projective,
- categories of algebras, abelian categories,
- exact sequences, short and long
- snake lemma (Jeremy) 
- 5-lemma
- chain complexes and homology
- exact couples, probably just of Z-graded objects
- derived exact couples
- spectral sequence of an exact couple
- convergence of spectral sequences

### Topology To Do:
- pointed types, fiber and cofiber sequences (is this in the library already?)
- prespectra and spectra, suspension
- spectrification
- parametrized smash and hom between types and spectra
- fiber and cofiber sequences of spectra, stability
- long exact sequences from (co)fiber sequences of spectra
- Eilenberg-MacLane spaces and spectra
- Postnikov towers of spectra
- exact couple of a tower of spectra

### Already Done:
- definition of algebraic structures such as groups, rings, fields, 
- some algebra: quotient, product, free.
