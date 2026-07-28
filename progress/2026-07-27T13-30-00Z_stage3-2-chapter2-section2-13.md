# Stage 3.2 claim audit — Chapter 2 §2.13

## Scope

This audit covers exactly the two reading-order items from
`Chapter2/Discussion_2.13_heading` through `Chapter2/Problem2.13.1`, stopping before
`Chapter2/Discussion_2.14_heading`. The source contains ten claim units: one heading claim and
nine claims or proof prompts in Problem 2.13.1.

## Result

- Part (b), `Irrational (arccos (1 / 3) / π)`, is faithfully and nonvacuously formalized by
  `Etingof.Problem2_13_1.irrational_arccos_third_div_pi`.
- Its proof implements the book's denominator contradiction through the equivalent integral
  Chebyshev recurrence `b_k = 3^k cos(kθ)` and the invariant `3 ∤ b_k`.
- The Dehn-invariant definition, cut additivity, polygon/polyhedron scissors-congruence
  infrastructure, and the cube-versus-tetrahedron conclusion are explicit intentional omissions
  under `skipped-exercises.md`; no placeholder declaration disguises those omissions.
- Historical attributions and the section heading are recorded as non-formalizable rather than
  silently ignored.

There are no accidental or unclassified coverage gaps in the §2.13 scope. The item status is
`sorry_free`: the only executable in-scope theorem is proved, while the geometric material remains
an explicit project-scope omission rather than a pending Lean proof.

## Validation

- targeted build of `EtingofRepresentationTheory.Chapter2.Problem2_13_1`
- scoped source scan for `sorry`, `admit`, and project `axiom` declarations
- `#print axioms Etingof.Problem2_13_1.irrational_arccos_third_div_pi`
- `jq empty progress/items.json`
- exact boundary/item-count check and `git diff --check`
