Code and LaTeX sources for Constructing Inductive-Inductive types in Cubical Type Theory.
==========

Conference version of the paper is in `paper/current.tex`. There is an unpolished draft
containing a proof sketch that the contruction generalizes to a large class of
inductive-inductive types in `paper/longversion.tex`.

Code can be found in the `code` directory. The files `UIP_from_Forsberg_II.{v,agda}` formalize
the argument that Nordvall Forsberg's construction essentially requires UIP in Coq and Agda.
The file `RunningExample.agda` formalizes our construction in cubical type theory for the
example used in the paper. TODO: add constructions of various other examples, demonstrating
general applicability.

The code was checked using Coq 8.8.0 and Agda 2.6.0 commit bd338484d.

