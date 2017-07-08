
This document will provide instructions how to browse the supplementary code,
verify the code with Agda or how to make the links from the paper work.


=============
BROWSING CODE
=============

The code can be browsed in HTML from the folder "html". We recommend to start
browsing from "README.html". From there, you can click on the imports
to access the other parts of the code. You can also click on objects
of definitions or proofs to access the objects definition.

To rebuild the HTML files (should not be necessary) run "make html" in the
"code" folder with the latest development version of Agda.

To browse the code in its native format, see folder "code". We recommend that
you have at least Agda version 2.5.2 installed and browse the code in Emacs
to get colored and clickable objects. From there we recommend starting from
file "README.agda".


==============
VERIFYING CODE
==============

To type check the code, run "make check" in folder "code" with at least
Agda version 2.5.2.


===============
FIX PAPER LINKS
===============

To make the links from the paper work, extract the zip-archive this README
was in, in the same folder as the PDF file of the paper, such that it has
direct access to the "html" folder.
