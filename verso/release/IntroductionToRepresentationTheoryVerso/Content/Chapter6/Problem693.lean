/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Problem693

#doc (Manual) "Problem 6.9.3: Ext and Jordan-Holder for Dynkin quiver representations" =>

# Problem 6.9.3: Ext and Jordan-Holder for Dynkin quiver representations
%%%
tag := "Chapter6/Problem6.9.3"
number := false
%%%

*Problem 6.9.3.* Let $`V_\alpha` be the indecomposable representation of a Dynkin quiver $`Q` which corresponds to a positive root $`\alpha`. For instance,
if $`\alpha_i` is a simple root, then $`V_{\alpha_i}` has a 1-dimensional space at $`i` and is 0 everywhere else.

(a) Show that if $`i` is a source, then $`\operatorname{Ext}^1(V, V_{\alpha_i}) = 0` for any representation $`V` of $`Q`, and if $`i` is a sink, then $`\operatorname{Ext}^1(V_{\alpha_i}, V) = 0`.

(b) Given an orientation of the quiver, find a Jordan-Hölder series of $`V_\alpha` for that orientation.

## Formalization
%%%
tag := "Chapter6/Problem6.9.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.Auxiliary.any_relates_to_auxiliaryObjectAtVertex}

{Manual.docstring RepresentationTheory.Quiver.Auxiliary.auxiliaryObjectAtVertex_relates_to_any}

{Manual.docstring RepresentationTheory.Quiver.Auxiliary.existsAuxiliaryDataWithVertexValues}

{Manual.docstring RepresentationTheory.Quiver.VertexOrder.Quiver.exists_witness_with_prescribed_values}

{Manual.docstring RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.IsElementaryExtensionAt}

{Manual.docstring RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.VertexCompositionSeries}

{Manual.docstring RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.exists_vertexCompositionSeries_with_multiplicity}
