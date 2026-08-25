/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Remark294

#doc (Manual) "Derivations as infinitesimal automorphisms; motivation for Lie algebras" =>
# Derivations as infinitesimal automorphisms; motivation for Lie algebras
%%%
tag := "Chapter2/Remark2.9.4"
number := false
%%%
**Remark 2.9.4.** Derivations are important because they are the "infinitesimal version" of automorphisms (i.e., isomorphisms onto itself). For example, assume that $`g(t)` is a differentiable family of automorphisms of a finite dimensional algebra $`A` over $`\mathbb{R}` or $`\mathbb{C}` parametrized by $`t \in (-\epsilon, \epsilon)` such that $`g(0) = \mathrm{Id}`. Then $`D := g'(0) : A \to A` is a derivation (check it!). Conversely, if $`D : A \to A` is a derivation, then $`e^{tD}` is a 1-parameter family of automorphisms (give a proof!).

This provides a motivation for the notion of a Lie algebra. Namely, we see that Lie algebras arise as spaces of infinitesimal automorphisms (= derivations) of associative algebras. In fact, they similarly arise as spaces of derivations of any kind of linear algebraic structures, such as Lie algebras, Hopf algebras, etc., and for this reason play a very important role in algebra.

## Formalization
%%%
tag := "Chapter2/Remark2.9.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Analysis.Algebra.DerivationExponential.derivation_of_hasDerivAt_multiplicativeCurve}

### Supporting declarations

{Manual.docstring RepresentationTheory.Analysis.Algebra.DerivationExponential.derivationExponentialEquiv}

{Manual.docstring RepresentationTheory.Analysis.Algebra.DerivationExponential.exp_add_smul}

{Manual.docstring RepresentationTheory.Analysis.Algebra.DerivationExponential.exp_smul_apply_one}

{Manual.docstring RepresentationTheory.Analysis.Algebra.DerivationExponential.exp_smul_map_mul}

{Manual.docstring RepresentationTheory.Analysis.Algebra.DerivationExponential.exp_zero_smul}
