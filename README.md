# A Logical Relation for Martin-Löf Type Theory in Agda #

Formalized proof of the decidability of conversion of a dependently typed language in Agda.

The source code for the [POPL 2018
paper](http://www.cse.chalmers.se/~abela/popl18.pdf) can be browsed in
HTML [here](https://mr-ohman.github.io/logrel-mltt/decofconv/).
The original code was mostly written by Joakim Öhman (@mr-ohman) in 2016
as Master's thesis supervised by Andrea Vezzosi (@Saizan) and
Andreas Abel (@andreasabel).

Since then, the project has been extended in the following ways:

  - The empty type added by Gaëtan Gilbert (@SkySkimmer, 2018).

  - Unit and Σ types added by Wojciech Nawrocki (@Vtec234, 2021).

  - Refactored to use well-scoped syntax by Oskar Eriksson (@fhklfy, 2021).

  - An proof that consistent axioms preserve canonicity by Andreas Abel (@andreasabel, 2021).

... and extensions available separately in their own branches:

  - Stream of natural numbers type added by Kenji Maillard, available in branch [`stream-nat`](/../../tree/stream-nat) (@kyoDralliam, 2022).


### Dependencies ###

This project is written in Agda.
It is compatible with Agda version ≥ 2.6.1 and the
[matching standard library](https://wiki.portal.chalmers.se/agda/Libraries/StandardLibrary).
The full list of tested Agda versions can be found in the
[continuous integration script](.github/workflows/agda-ci.yml).


## Forks

This formalization has been used as basis of further formalization projects, including the following:

### Decidability of typechecking in a dependently-typed programming language with sigma types

Wojciech Nawrocki (2020), MPhil thesis at the University of Cambridge.

- Code: https://github.com/Vtec234/logrel-mltt
- [Thesis PDF](https://voidma.in/assets/papers/2020nawrocki_decidability_typechecking_dependently_typed_programming_language_sigma_types.pdf)

### A type theory with definitional proof-irrelevance

Gaëtan Gilbert (2019), PhD thesis at Mines ParisTech.

- Code: https://github.com/SkySkimmer/logrel-tt (vanished, probably moved to https://github.com/CoqHott/logrel-mltt/tree/sprop)
- [Thesis](https://theses.hal.science/tel-03236271)

### Observational Equality: Now For Good

Loïc Pujet, Nicolas Tabareau, POPL 2022

- Code: [A Logical Relation for Observational Type Theory in Agda](https://github.com/CoqHott/logrel-mltt)
- [Paper](https://hal.inria.fr/hal-03367052)

### Impredicative Observational Equality

Loïc Pujet, Nicolas Tabareau, POPL 2023

- Code: https://github.com/CoqHott/logrel-mltt/tree/impredicativity-SProp-POPL
- [Paper](https://dl.acm.org/doi/pdf/10.1145/3571739)

### A Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized

Andreas Abel, Nils Anders Danielsson, Oskar Eriksson, ICFP 2023.

- Code: https://github.com/graded-type-theory/graded-type-theory/releases/tag/icfp23
- [Paper](https://dl.acm.org/doi/10.1145/3607862)

### Graded Modal Type Theory, Formalized

Oskar Eriksson (2025), Licentiate Thesis at Gothenburg University.

- Code:  https://github.com/graded-type-theory/graded-type-theory/releases/tag/lic2025
- [Thesis](https://gupea.ub.gu.se/handle/2077/86472)
