# Stage 3.2 review — Chapter 4, §4.2

## Scope and result

This pass covers the exact contiguous catalog scope from `Chapter4/Introduction_4.2` through
`Chapter4/Corollary4.2.4`: the section introduction, Theorem 4.2.1, Corollary 4.2.2,
Exercise 4.2.3, and Corollary 4.2.4. Every source line and every attached provider was checked.
The exercise record retains the more detailed final-exercise-audit inventory introduced by
PR #8115; this review does not replace or weaken it.

All mathematical endpoints are formalized. The old Theorem 4.2.1 and Exercise 4.2.3 regression
notes were stale: the current providers rebuild, and the exercise's strict modular count is
covered by the assembled theorem audited in PR #8115. The only omitted source claim is a proof-
route identification of `(k[G]/[k[G],k[G]])*` with the class-function space. The Lean proof uses
an equivalent direct Wedderburn/orthogonality argument and now exposes the same endpoint as an
equality of submodules.

## Claim inventory

The section introduction contributes five definitions or assertions:

- `Etingof.FunctionSpace` names `F(G,k) = G → k`;
- `Etingof.classFunctionSubmodule` names `F_c(G,k)` and
  `mem_classFunctionSubmodule_iff` exposes its conjugacy-invariance predicate;
- `FDRep.character` is the trace definition `χ_V(g) = Tr(ρ(g))`;
- `Etingof.FDRep.character_eq_algebraCharacter` proves that this is the restriction to
  `G ⊆ k[G]` of the associated algebra-module character;
- `Etingof.FDRep.character_mem_classFunctionSubmodule`, using `FDRep.char_conj`, proves that
  every character is a class function.

Theorem 4.2.1 is represented by four complementary declarations. `Etingof.Theorem4_2_1`
proves spanning, `Etingof.Theorem4_2_1_linearIndependent` proves linear independence,
`Etingof.Theorem4_2_1_span_eq_classFunctionSubmodule` identifies the span with the named
class-function submodule, and `Etingof.classFunction_eq_zero_of_orthogonal_simples` exposes the
completeness core. Together these state exactly that the distinct irreducible characters form a
basis of `F_c(G,k)`. Maschke's theorem and the semisimple-algebra character basis invoked by the
book's proof are covered elsewhere by `Etingof.Theorem4_1_1_semisimple` and
`Etingof.characters_basis_semisimple`. The book's particular quotient-dual isomorphism is an
intentional proof-route omission; no endpoint depends on assuming it.

Corollary 4.2.2 is formalized by `Etingof.Corollary4_2_2`, which constructs a finite, simple,
pairwise non-isomorphic, exhaustive family and proves that its cardinality is the number of
conjugacy classes. Exercise 4.2.3 is formalized by `Etingof.Exercise4_2_3` and
`Etingof.natCard_irrepClasses_lt_conjClasses_of_isAlgClosed`, as recorded by the final exercise
audit. Corollary 4.2.4 is formalized over the chapter's arbitrary algebraically closed
characteristic-zero field by `Etingof.Corollary4_2_4`; `Etingof.Corollary4_2_4_complex` records
the classical complex specialization.

## Fidelity and nonvacuity

`[Invertible (Fintype.card G : k)]` is precisely non-modular characteristic over a field.
`[IsAlgClosed k]` records the chapter's inherited splitting-field hypothesis and is necessary:
over a nonsplitting field irreducible characters need not span all class functions. Simplicity is
the categorical `Simple` predicate on genuine finite-dimensional representations, not a
dimension-only proxy. The irreducible-character index is an image set, so equal characters are
deduplicated before linear independence is asserted.

The theorem proof is substantive. It maps a class function to a central group-algebra element,
uses the Wedderburn decomposition to show each block is scalar, applies trace orthogonality to
force every scalar to vanish, and then constructs Fourier coefficients. Corollary 4.2.2 compares
the centers of the group algebra and the product of matrix blocks. Corollary 4.2.4 derives equal
simple multiplicities from equal characters and recursively assembles an actual `FDRep`
isomorphism. The hypotheses are jointly inhabited, for example by `k = ℂ` and any finite group.

## Verification

- `lake build EtingofRepresentationTheory.Chapter4.Introduction_4_2`: 2,257 jobs passed with no
  scoped warning;
- Theorem 4.2.1 and its downstream signature-lock test: 8,587 jobs passed;
- the section providers, including both corollaries and the exercise assembly, rebuild on the
  current toolchain;
- `#print axioms` on the twelve public theorem endpoints reports only `propext`,
  `Classical.choice`, and `Quot.sound` (the definitional membership theorem needs only the first
  and third), with no `sorryAx` or project axiom;
- the pre-existing detailed Theorem 4.2.1 fidelity review was rechecked and remains valid;
- no source placeholder is introduced, and the new declarations are theorem-kernel checked.
