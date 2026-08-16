/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter9.Problem965

#doc (Manual) "Proof of Theorem 9.6.4 via quasi-inverse functors" =>

# Proof of Theorem 9.6.4 via quasi-inverse functors
%%%
tag := "Chapter9/Problem9.6.5"
number := false
%%%

*Problem 9.6.5.* Let $`G : B\text{-fmod} \to \mathcal{C}` be the functor defined by $`G(X) := P \otimes_B X`, where $`P \otimes_B X` is the cokernel of the morphism $`\psi : P \otimes B \otimes X \to P \otimes X` given by $`\psi = a_P \otimes \operatorname{Id} - \operatorname{Id} \otimes a_X` (where $`a_P : P \otimes B \to P`, $`a_X : B \otimes X \to X` are the morphisms representing the actions of $`B` on $`P` and $`X`).

(i) Show that $`F \circ G \cong \operatorname{Id}`. That is, for every $`X \in B\text{-fmod}`, show that $`X` is naturally isomorphic to $`\operatorname{Hom}(P, P \otimes_B X)`. (For this you should only need that $`P` is a nonzero projective object.)

(ii) For any $`X \in \mathcal{C}`, construct a natural morphism

$$`\xi : P \otimes_B \operatorname{Hom}(P, X) \to X,`

and show that it is surjective.

(iii) Show that $`G \circ F \cong \operatorname{Id}`. To this end, consider the short exact sequence

$$`0 \to K \to P \otimes_B \operatorname{Hom}(P, X) \to X \to 0,`

where the third map is $`\xi`. Apply the functor $`F` to this sequence and use (i) to conclude that $`K = 0` and hence $`\xi` is an isomorphism. Conclude that the functors $`G` and $`F` are quasi-inverse to each other and hence are equivalences of categories.

## Formalization
%%%
tag := "Chapter9/Problem9.6.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.modulePresentationRelation}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.moduleThenPresentationHom}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.moduleThenPresentationHom_app_epi}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.moduleThenPresentationHom_isIso}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.presentationThenModuleIso}

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.finiteCopowerHomEquiv}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.finiteModuleEquivalence}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.kernel_presentationEvaluation_isZero}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.modulePresentationFunctor}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.modulePresentationObject}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.oppositeEndEvaluation}

{Manual.docstring RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence.tensorScalarAction}
