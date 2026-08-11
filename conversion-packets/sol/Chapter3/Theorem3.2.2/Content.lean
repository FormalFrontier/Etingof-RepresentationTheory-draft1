import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Theorem322

#doc (Manual) "The density theorem" =>
# The density theorem
%%%
tag := "Chapter3/Theorem3.2.2"
number := false
%%%
**Theorem 3.2.2** (The density theorem). _(i) Let $`V` be an irreducible finite dimensional representation of $`A`. Then the map $`\rho : A \to \operatorname{End} V` is surjective._

_(ii) Let $`V = V_1 \oplus \cdots \oplus V_r`, where $`V_i` are irreducible pairwise nonisomorphic finite dimensional representations of $`A`. Then the map $`\bigoplus_{i=1}^r \rho_i : A \to \bigoplus_{i=1}^r \operatorname{End}(V_i)` is surjective._[^Chapter3/Theorem3.2.2/footnote-3]

**Proof.** (i) Let $`B` be the image of $`A` in $`\operatorname{End}(V)`. We want to show that $`B = \operatorname{End}(V)`. Let $`c \in \operatorname{End}(V)`, let $`v_1, \ldots, v_n` be a basis of $`V`, and let $`w_i = cv_i`. By Corollary 3.2.1, there exists $`a \in A` such that $`av_i = w_i`. Then $`a` maps to $`c`, so $`c \in B`, and we are done.

(ii) Let $`B_i` be the image of $`A` in $`\operatorname{End}(V_i)`, and let $`B` be the image of $`A` in $`\bigoplus_{i=1}^r \operatorname{End}(V_i)`. Recall that as a representation of $`A`, $`\bigoplus_{i=1}^r \operatorname{End}(V_i)` is semisimple: it is isomorphic to $`\bigoplus_{i=1}^r d_i V_i`, where $`d_i = \dim V_i`. Then by Proposition 3.1.4, $`B = \bigoplus_i B_i`. On the other hand, (i) implies that $`B_i = \operatorname{End}(V_i)`. Thus (ii) follows. $`\square`

[^Chapter3/Theorem3.2.2/footnote-3]: In general, it is better to consider direct products rather than direct sums of algebras; for example, the direct product of any collection of unital algebras is unital, while the direct sum is not if the collection is infinite. However, we will only consider finite direct sums, in which case this distinction is immaterial.
