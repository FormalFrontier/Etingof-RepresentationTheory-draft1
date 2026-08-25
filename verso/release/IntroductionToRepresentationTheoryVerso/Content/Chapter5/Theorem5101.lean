/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5101

#doc (Manual) "Frobenius reciprocity: Hom\\_G(V, Ind W) \u2245 Hom\\_H(Res V, W)" =>

# Frobenius reciprocity: Hom\_G(V, Ind W) ≅ Hom\_H(Res V, W)
%%%
tag := "Chapter5/Theorem5.10.1"
number := false
%%%

**Theorem 5.10.1** (Frobenius reciprocity). _Let $`H \subset G` be groups, $`V` a representation of $`G` and $`W` a representation of $`H`. Then the space $`\operatorname{Hom}_G(V, \operatorname{Ind}_H^G W)` is naturally isomorphic to $`\operatorname{Hom}_H(\operatorname{Res}_H^G V, W)`._

**Proof.** Let $`E = \operatorname{Hom}_G(V, \operatorname{Ind}_H^G W)` and $`E' = \operatorname{Hom}_H(\operatorname{Res}_H^G V, W)`. Define $`F : E \to E'` and $`F' : E' \to E` as follows: $`F(\alpha)v = (\alpha v)(e)` for any $`\alpha \in E` and $`(F'(\beta)v)(x) = \beta(xv)` for any $`\beta \in E'`.

In order to check that $`F` and $`F'` are well defined and inverse to each other, we need to check the following five statements.

Let $`\alpha \in E`, $`\beta \in E'`, $`v \in V`, and $`x, g \in G`.

(a) $`F(\alpha)` is an $`H`-homomorphism; i.e., $`F(\alpha)hv = hF(\alpha)v`.

Indeed, $`F(\alpha)hv = (\alpha hv)(e) = (h\alpha v)(e) = (\alpha v)(he) = (\alpha v)(eh) = h \cdot (\alpha v)(e) = hF(\alpha)v`.

(b) $`F'(\beta)v \in \operatorname{Ind}_H^G W`; i.e., $`(F'(\beta)v)(hx) = h(F'(\beta)v)(x)`.

Indeed, $`(F'(\beta)v)(hx) = \beta(hxv) = h\beta(xv) = h(F'(\beta)v)(x)`.

(c) $`F'(\beta)` is a $`G`-homomorphism; i.e. $`F'(\beta)gv = g(F'(\beta)v)`.

Indeed, $`(F'(\beta)gv)(x) = \beta(xgv) = (F'(\beta)v)(xg) = (g(F'(\beta)v))(x)`.

(d) $`F \circ F' = \operatorname{Id}_{E'}`.

This holds since $`F(F'(\beta))v = (F'(\beta)v)(e) = \beta(v)`.

(e) $`F' \circ F = \operatorname{Id}_E`; i.e., $`(F'(F(\alpha))v)(x) = (\alpha v)(x)`.

Indeed, $`(F'(F(\alpha))v)(x) = F(\alpha xv) = (\alpha xv)(e) = (x\alpha v)(e) = (\alpha v)(x)`, and we are done. $`\square`

## Formalization
%%%
tag := "Chapter5/Theorem5.10.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Subgroup.HomAdjunction.ambientSubgroupAdjunction}

{Manual.docstring RepresentationTheory.Subgroup.HomAdjunction.ambientSubgroupHomEquiv}

{Manual.docstring RepresentationTheory.Subgroup.HomAdjunction.ambientSubgroupHomEquiv_apply}

{Manual.docstring RepresentationTheory.Subgroup.HomAdjunction.ambientSubgroupHomFunctorIso}

### Supporting declarations

{Manual.docstring RepresentationTheory.Subgroup.HomAdjunction.ambientSubgroupHomFunctorIso_app_apply}
