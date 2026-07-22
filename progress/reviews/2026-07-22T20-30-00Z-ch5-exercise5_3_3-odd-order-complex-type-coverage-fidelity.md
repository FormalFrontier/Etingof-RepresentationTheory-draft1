# Stage 3.7 coverage-arm audit — Exercise 5.3.3 (odd-order nontrivial irreducibles are complex type)

- Issue: #7346
- Session: agent `e58e3a7c`, review
- Base commit: `a473eb63` (= `origin/main`)
- File audited: `EtingofRepresentationTheory/Chapter5/Exercise5_3_3.lean` (290 lines, sorry-free)
- Judge model: Opus 4.8 (distinct from whatever model formalized the file).

## Book statement

**Exercise 5.3.3.** Strengthen Exercise 5.1.7: all nontrivial irreducible
representations of a group of odd order are of **complex type**. (Use that any
representation of quaternionic type is even-dimensional.)

## Build & axiom cleanliness

`lake build …Chapter5.Exercise5_3_3` succeeds (8589 jobs). File is sorry-free.
`#print axioms` (via the olean-import method — a scratch file that imports the
built module, avoiding the false `sorryAx` that appending to source can trigger)
on the headline and all five supporting decls yields
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. Non-vacuous at the
axiom level.

Axiom-checked decls: `isComplexType_of_odd_order_of_nontrivial_irreducible`,
`not_isRealType_of_odd_order_of_nontrivial_irreducible`,
`not_isQuaternionicType_of_odd_order_of_irreducible`,
`isRealType_or_isQuaternionicType_of_selfDual`, `sum_char_sq_eq_zero`,
`sum_char_sq_eq_card_of_isRealType`.

## Type predicates are genuine (Definition5_1_1.lean)

- `IsComplexType ρ` := `¬ ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V` that is G-equivariant
  (`∀ g v, e (ρ g v) = ρ.dual g (e v)`), i.e. `V ≇ V*` as G-reps. This is the
  honest Definition 5.1.1 predicate, not a surrogate (not `End_{ℂ[G]} = ℂ`, not
  a character-only condition).
- `IsRealType` / `IsQuaternionicType` := ∃ G-invariant nondegenerate
  symmetric / skew-symmetric ℂ-bilinear form. Genuine Definition 5.1.1 predicates.

## Exercise 5.3.3 — verdict `covered_full`

`isComplexType_of_odd_order_of_nontrivial_irreducible` (line 276), under
`[Group G] [Fintype G]`, `(hodd : Odd (Fintype.card G))`,
`(ρ : Representation ℂ G V)`,
`(hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)`, and
`(hnontriv : ∃ g, ρ g ≠ 1)`, concludes `Etingof.IsComplexType ρ`. This is exactly
the book claim: for odd `|G|`, every nontrivial irreducible complex rep is not
self-dual (complex type).

- **Conclusion is the genuine "complex type"**, not a weaker surrogate, and is
  strictly stronger than Exercise 5.1.7's "has a non-real irrep" — 5.1.7 asserts
  existence of a non-real-type irrep, whereas 5.3.3 classifies **every** nontrivial
  irreducible as fully complex type (neither real nor quaternionic). No overlap of
  claims.
- **Both hypotheses genuinely used, neither vacuous:**
  - `hodd`: feeds both arms. In `not_isRealType_…` via `sum_char_sq_eq_zero` →
    `sqEquivOfOdd` (the `g ↦ g²` bijection needs oddness), and in
    `not_isQuaternionicType_…` via the parity contradiction
    `finrank ∣ (odd |G|)` vs `Even finrank`. Removing it is fatal: Z/2's sign rep
    is a nontrivial irreducible of **real** type (self-dual), a counterexample.
  - `hnontriv` (`∃ g, ρ g ≠ 1`): used in the real-type arm via
    `invariants_eq_bot_of_nontrivial_irreducible` (the vanishing
    `∑ χ(g²) = |G|·dim invariants = 0`). Genuinely required and **not**
    over-constraining: the trivial 1-dim rep is real type (self-dual), hence NOT
    complex type, so the theorem is false without excluding it. The statement does
    not vacuously hold for the trivial rep.
- **Quaternionic-exclusion arm rests on the book hint.**
  `not_isQuaternionicType_of_odd_order_of_irreducible` (247) combines
  `even_finrank_of_isQuaternionicType` (a nondegenerate skew form ⇒ even dimension —
  the book's "quaternionic type is even-dimensional") with
  `Theorem5_3_1` (`finrank ∣ |G|`, dimension of an irreducible divides the order),
  then omega on parity. Non-tautological.
- **Real-type-exclusion arm rests on the odd-order Frobenius–Schur sum.**
  `not_isRealType_of_odd_order_of_nontrivial_irreducible` (228) contradicts
  `sum_char_sq_eq_card_of_isRealType` (`∑ χ(g²) = |G| ≠ 0`, from the reverse
  FS-indicator identity `frobeniusSchurIndicator_eq_one_of_isRealType`, #6242)
  against `sum_char_sq_eq_zero` (`∑ χ(g²) = 0`). Non-tautological.
- **Schur dichotomy real ∨ quaternionic** for self-dual irreducibles supplied by
  `isRealType_or_isQuaternionicType_of_selfDual` (203), routing through the
  character-level `isRealType_or_isQuaternionicType_of_self_dual`.

## Non-vacuity of the theorem itself

Odd-order groups with nontrivial irreducibles exist (e.g. Z/3, whose two
nontrivial characters `g ↦ ω^k` are of complex type — self-duality would force a
real character). The hypotheses do not over-constrain to make the claim trivially
true; both arms carry real mathematical content.

## Minor note (not a gap)

`V : Type` (universe 0) rather than `Type*`. Not a mathematical weakening: the
proof routes through `FDRep.of ρ` (for `Theorem5_3_1`), which lives over `Type`,
and every finite-dimensional ℂ-rep is realizable in `Type 0`. Consistent with the
FDRep-based §5 audits. Does **not** warrant `covered_partial`.

## items.json changes

- `Chapter5/Exercise5.3.3`: added `coverage: covered_full`,
  `coverage_arm: audited`, `fidelity: verified`, `fidelity_note`,
  `lean_file` (list), `lean_decl`, `last_updated: 2026-07-22`. Normalized
  `status` `proved` → `sorry_free` (matches the sibling §5.1 items and the
  verified sorry-free build).

No follow-up `feature` issue is warranted: the Lean statement is not strictly
weaker than the book's claim (no gap). No Lean was modified.
