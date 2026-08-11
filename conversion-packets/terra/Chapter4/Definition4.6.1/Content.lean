import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Definition461

#doc (Manual) "Unitary representation" =>

# Unitary representation
%%%
tag := "Chapter4/Definition4.6.1"
number := false
%%%

**Definition 4.6.1.** A **unitary** finite dimensional representation of a group $`G` is a representation of $`G` on a complex finite dimensional vector space $`V` over $`\mathbb{C}` equipped with a $`G`-invariant positive definite Hermitian form[^Chapter4/Definition4.6.1/footnote-1] $`( \, , \, )`, i.e., such that $`\rho_V(g)` are unitary operators: $`(\rho_V(g)v, \rho_V(g)w) = (v, w)`.

[^Chapter4/Definition4.6.1/footnote-1]: Recall that a sesquilinear form on a complex vector space $`V` is an $`\mathbb{R}`-bilinear map $`(,) : V \times V \to \mathbb{C}` such that $`(zv, w) = (v, \bar{z}w) = z(v, w)` for $`z \in \mathbb{C}`, and a sesquilinear form $`(,)` is Hermitian if $`(v, w) = \overline{(w, v)}`. Recall also that a Hermitian form $`(,)` is positive definite if $`(v, v) > 0` for all nonzero $`v \in V`.
