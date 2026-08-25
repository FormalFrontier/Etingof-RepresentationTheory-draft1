/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.DiscussionAfterRemark774

#doc (Manual) "k-linear abelian categories" =>

# k-linear abelian categories
%%%
tag := "Chapter7/Discussion_after_Remark7.7.4"
number := false
%%%

Let $`k` be a field. We say that an abelian category $`\mathcal{C}` is $`k`-*linear* if the groups $`\operatorname{Hom}_\mathcal{C}(X, Y)` are equipped with a structure of a vector space over $`k` and composition maps are $`k`-linear in each argument. In particular, the categories in Example 7.7.2 are $`k`-linear.

## Formalization
%%%
tag := "Chapter7/Discussion_after_Remark7.7.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.CategoryTheory.ModuleCategories.fgModuleCatAbelian}

{Manual.docstring RepresentationTheory.CategoryTheory.ModuleCategories.fgModuleCatLinear}

{Manual.docstring RepresentationTheory.CategoryTheory.ModuleCategories.moduleCatAbelian}

{Manual.docstring RepresentationTheory.CategoryTheory.ModuleCategories.moduleCatLinear}
