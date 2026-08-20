/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Theorem354

#doc (Manual) "Structure of finite dimensional algebras modulo radical" =>
# Structure of finite dimensional algebras modulo radical
%%%
tag := "Chapter3/Theorem3.5.4"
number := false
%%%
**Theorem 3.5.4.** _A finite dimensional algebra $`A` has only finitely many irreducible representations $`V_i` up to an isomorphism. These representations are finite dimensional, and_

$$`A / \operatorname{Rad}(A) \cong \bigoplus_i \operatorname{End} V_i.`

**Proof.** First, for any irreducible representation $`V` of $`A` and for any nonzero $`v \in V`, $`Av \subseteq V` is a finite dimensional subrepresentation of $`V`. (It is finite dimensional as $`A` is finite dimensional.) As $`V` is irreducible and $`Av \neq 0`, $`V = Av` and $`V` is finite dimensional.

Next, suppose we have nonisomorphic irreducible representations $`V_1, V_2, \ldots, V_r`. By Theorem 3.2.2, the homomorphism

$$`\bigoplus_i \rho_i : A \longrightarrow \bigoplus_i \operatorname{End} V_i`

is surjective. So $`r \leq \sum_i \dim \operatorname{End} V_i \leq \dim A`. Thus, $`A` has only finitely many nonisomorphic irreducible representations (not more than $`\dim A`).

Now, let $`V_1, V_2, \ldots, V_r` be all nonisomorphic irreducible finite dimensional representations of $`A`. By Theorem 3.2.2, the homomorphism

$$`\bigoplus_i \rho_i : A \longrightarrow \bigoplus_i \operatorname{End} V_i`

is surjective. The kernel of this map, by definition, is exactly $`\operatorname{Rad}(A)`. $`\square`

## Formalization
%%%
tag := "Chapter3/Theorem3.5.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.Simple.FiniteDimensional.finiteDimensional_of_isSimpleModule}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.family_algebra_smul_surjective}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct.nonempty_algEquiv_quotient_endProduct}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients.exists_coatom_quotient_equiv}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients.exists_finite_coatomFamily}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.Simple.FiniteDimensional.card_le_finrank_of_pairwise_nonisomorphic}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients.exists_finite_coatomFamily_algEquiv_quotient}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients.exists_finite_coatomFamily_of_coatoms}
