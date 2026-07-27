# Stage 3.2 review: Chapter 2 §2.3

Date: 2026-07-27

Scope: the 24 catalog items from `Chapter2/Definition2.3.1` through
`Chapter2/Problem2.3.18`, excluding `Chapter2/Discussion_2.4_heading`.

## Coverage and fidelity audit

- Read every scoped blob sentence by sentence and recorded durable `claim_coverage` for every
  item in `progress/items.json` using the Stage 3.2 schema.
- Checked every hypothesis, conclusion, named concept, construction, equivalence, example, and
  exercise part against its Lean declaration. Motivational or organizational prose is explicitly
  recorded as `non_formalizable` with a reason.
- Checked nonvacuity semantically, including nonzeroness in irreducible/indecomposable statements,
  nonempty direct-sum factors, finite-dimensional and algebraic-closedness hypotheses, the full
  Jordan classification, the irreducible-subrepresentation clause in Problem 2.3.16(b), and the
  countable-rank hypothesis in Dixmier's lemma.
- Checked definition integrity: no definition or other data construction contains `sorry`.

## Scaffolding repairs

- `Definition2_3_1.lean`: added the right-representation/opposite-ring declaration, its
  antihomomorphism presentation, and both action-associativity formulas.
- `Example2_3_3.lean`: named the zero, left-regular, and right-regular module structures and stated
  the right-regular action formula.
- `Definition2_3_4.lean`, `Definition2_3_6.lean`, `Definition2_3_7.lean`: exposed the zero/full
  subrepresentations, representation equivalences/isomorphism predicate, and componentwise direct
  sum action.
- `Definition2_3_8.lean`: added the literal nontrivial-direct-sum data from the book and an explicit
  bridge theorem to the internal complementary-submodule definition.
- `Proposition2_3_9.lean`: added the omitted concluding bijectivity/isomorphism clause.
- `Example2_3_14.lean`: removed the duplicate local indecomposability predicate in favor of
  `Etingof.IsIndecomposable`, and added exact statements for uniqueness of the irreducible and
  indecomposable `k`-representation and for general finite-dimensional Jordan decomposition.
- `Problem2_3_16.lean`: added the omitted clause that the unique central eigenvalue is the scalar
  action on an irreducible subrepresentation.

## Stage 3.3 follow-up exposed by this review

The new statements `Etingof.isIndecomposable_iff_asDirectSum`,
`Etingof.Example_2_3_14_field_irreducible_unique`,
`Etingof.Example_2_3_14_field_indecomposable_unique`,
`Etingof.Example_2_3_14.exists_equiv_pi_jordanRep`, and
`Etingof.exists_irreducibleSubrepresentation_centralCharacter` have theorem-level `sorry`
placeholders. Their data and statements are complete and faithful; proving them belongs to a
separate Stage 3.3 PR. The corresponding three catalog items are therefore left at
`definition_verified`; previously advanced statuses are preserved on all items whose proofs remain
complete.

## Validation

- `progress/items.json` parses with `jq`; exactly all 24 scoped items have complete Stage 3.2
  coverage records, and no out-of-scope tracker object changed.
- Targeted Lean build and repository-wide `lake build` results are recorded in the PR body.
