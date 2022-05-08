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
It has been tested to be working with Agda version 2.6.2 and its standard library.
