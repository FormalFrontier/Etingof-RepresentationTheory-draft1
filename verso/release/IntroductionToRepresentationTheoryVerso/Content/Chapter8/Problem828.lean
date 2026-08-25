/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Problem828

#doc (Manual) "Tor and Ext for tensor products of algebras" =>

# Tor and Ext for tensor products of algebras
%%%
tag := "Chapter8/Problem8.2.8"
number := false
%%%

*Problem 8.2.8.* Show that if $`A_1, A_2` are algebras over a field $`k` and $`M_i, N_i` are left $`A_i`-modules, then

$$`\operatorname{Tor}_i^{A_1 \otimes A_2}(M_1 \otimes M_2, N_1 \otimes N_2) = \bigoplus_{j+m=i} \operatorname{Tor}_j^{A_1}(M_1, N_1) \otimes \operatorname{Tor}_m^{A_2}(M_2, N_2).`

Similarly,

$$`\operatorname{Ext}^i_{A_1 \otimes A_2}(M_1 \otimes M_2, N_1 \otimes N_2) = \bigoplus_{j+m=i} \operatorname{Ext}^j_{A_1}(M_1, N_1) \otimes \operatorname{Ext}^m_{A_2}(M_2, N_2),`

if $`N_i` are finite dimensional.

## Formalization
%%%
tag := "Chapter8/Problem8.2.8/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Auxiliary.TensorProductGradedComparisons.Auxiliary.nonempty_projectiveResolutionTensorProductObjectIsoSigma}

{Manual.docstring RepresentationTheory.Auxiliary.TensorProductGradedComparisons.Auxiliary.nonempty_rightModuleTensorProductObjectIsoSigma}

{Manual.docstring RepresentationTheory.Auxiliary.TensorProductGradedComparisons.Auxiliary.nonempty_tensorProductGradedPieceLinearEquivDirectSum}

{Manual.docstring RepresentationTheory.FinsuppDualTensor.dualDistrib_finsuppNat_not_surjective}
