/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionTensorProductMaps

#doc (Manual) "Tensor product of linear maps" =>
# Tensor product of linear maps
%%%
tag := "Chapter2/Discussion_tensor_product_maps"
number := false
%%%
One can also define the tensor product of linear maps. Namely, if $`A : V \to V'` and $`B : W \to W'` are linear maps, then one can define the linear map $`A \otimes B : V \otimes W \to V' \otimes W'` given by the formula $`(A \otimes B)(v \otimes w) = Av \otimes Bw` (check that this is well defined!). The
most important properties of tensor products are summarized in the following problem.
