Code and LaTeX sources for Constructing Inductive-Inductive types in Cubical Type Theory.
==========

Conference version of the paper is in `paper/current.tex`. There is an unpolished draft
containing a proof sketch that the contruction generalizes to a large class of
inductive-inductive types in `paper/longversion.tex`.

Code can be found in the `code` directory. The files `UIP_from_Forsberg_II.{v,agda}` formalize
the argument that Nordvall Forsberg's construction essentially requires UIP in Coq and Agda.
We also formalize the construction in cubical type theory of a number of inductive-inductive types:
* `RunningExample.agda`: The example used in the paper
* `ConTy.agda`: The example with contexts and types from the introduction
* `InfinitaryII.agda`: An example with infinitary constructors
* `EvilII.agda` : This example has infinitary constructors and indices, and constructors in other constructors and sorts

This code has been checked using Coq 8.8.0 and Agda 2.6.0.1.

The tag `FoSSaCS2019-camera-ready` refers to the code for FoSSaCS 2019 after revision based on reviewer feedback.

The tag `FoSSaCS2019` refers to the code at the time of submission to FoSSaCS 2019.

Check README.md in each of the tags for applicable versions of Coq and Agda.

