/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Problem393

#doc (Manual) "Irreducible representations and Ext^1 for path algebras" =>

# Irreducible representations and Ext^1 for path algebras
%%%
tag := "Chapter3/Problem3.9.3"
number := false
%%%
**Problem 3.9.3.** Let $`Q` be a quiver without oriented cycles, and let $`P_Q` be the path algebra of $`Q`. Find irreducible representations of $`P_Q` and compute $`\operatorname{Ext}^1` between them. Classify 2-dimensional representations of $`P_Q`.

## Formalization
%%%
tag := "Chapter3/Problem3.9.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryConstructions.auxiliaryRelation_iff_isEmpty_hom}

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryConstructions.exists_vertex_nonempty_auxiliaryObject}

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryConstructions.finrank_homObject}

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryConstructions.hasAuxiliaryProperty_vertex}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.exists_equiv_twoVertexRepresentation_of_totalDimension_eq_two}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.zeroTwoVertexAuxiliaryEquiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryConstructions.not_auxiliaryProperty_or_exists_bijective_map}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryTwoVertexEquiv}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact10}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact13}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact20}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact3}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.not_auxiliaryProperty_or_exists_bijectiveArrow_of_totalDimension_eq_two}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.not_auxiliaryProperty_twoVertexRepresentation_zero}

{Manual.docstring RepresentationTheory.Quiver.TwoDimensionalRepresentations.twoVertexRepresentation}
