# Stage 3.7 coverage-arm audit — Problem 5.1.2 & Exercise 5.1.7 (§5.1 real/complex/quaternionic type)

- Issue: #7344
- Session: agent `b3673acd`, review
- Base commit: `b38bc433` (= `origin/main`)
- Files audited:
  - `EtingofRepresentationTheory/Chapter5/Problem5_1_2.lean` (1205 lines, sorry-free)
  - `EtingofRepresentationTheory/Chapter5/Exercise5_1_7.lean` (93 lines, sorry-free)
- Judge model: Opus 4.8 (distinct from whatever model formalized the files).

## Build & axiom cleanliness

`lake build …Problem5_1_2 …Exercise5_1_7` succeeds (8592 jobs). No `sorry`
in either file (`rg sorry` hits only the English word "admits" and doc text).
`#print axioms` on all five headline decls yields
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, so the statements are
non-vacuous at the axiom level.

## Type-predicate non-vacuity (Definition5_1_1.lean)

The three type predicates are the honest Definition 5.1.1 predicates, not
placeholders, and are **not** defined via the endomorphism algebra or via a
real form — so the theorems below are non-circular content:

- `IsRealType ρ`  := ∃ G-invariant nondegenerate **symmetric** ℂ-bilinear form.
- `IsQuaternionicType ρ` := ∃ G-invariant nondegenerate **skew-symmetric** form.
- `IsComplexType ρ` := `¬ ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V` that is G-equivariant
  (i.e. `V ≇ V*` as G-reps).

`realGEndAlgebra ρ` := `Subalgebra.centralizer ℝ (Set.range (g ↦ (ρ g).restrictScalars ℝ))`,
an ℝ-subalgebra of `Module.End ℝ V` — a faithful rendering of `End_{ℝ[G]} V`.

## Problem 5.1.2 — verdict `covered_full` (min over 4 sub-parts, all `covered_full`)

Book (a): `End_{ℝ[G]} V` is `ℂ` (complex type) / `Mat₂(ℝ)` (real) / `ℍ`
(quaternionic). Book (b): `V` is real type ⟺ `V` is the complexification of a
real representation.

| sub-part | lean_decl (line) | conclusion | verdict |
|---|---|---|---|
| (a)-complex | `realGEndAlgebra_equiv_complex_of_isComplexType` (656) | `Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] ℂ)` | covered_full |
| (a)-real | `realGEndAlgebra_equiv_matrix_of_isRealType` (755) | `Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)` | covered_full |
| (a)-quaternionic | `realGEndAlgebra_equiv_quaternion_of_isQuaternionicType` (832) | `Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] Quaternion ℝ)` | covered_full |
| (b) | `isRealType_iff_exists_real_form` (1193) | see below | covered_full |

- **(a), all three cases.** The conclusion is a genuine **ℝ-algebra**
  isomorphism `≃ₐ[ℝ]` (not `≃ₗ[ℝ]`, not a bare `≃`, not a dimension equality)
  onto exactly `ℂ` / `Matrix (Fin 2) (Fin 2) ℝ` / `Quaternion ℝ`. Each carries
  `hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule` (the §5.1 setting is
  irreducible V, matching Def 5.1.1) plus the corresponding genuine type
  predicate. The `Nonempty (… ≃ₐ[ℝ] …)` wrapper is exactly "the ℝ-algebra
  `End_{ℝ[G]} V` **is** ℂ/Mat₂(ℝ)/ℍ". The book's hint machinery (the
  antilinear `j` with `j² = ±1`, `V_ℂ ≅ V ⊕ V*`) is the *proof method* and is
  present in-file (`realJ`, `exists_antilinear_j_of_invariant_nondegenerate`,
  the `ConjDecomp` section); the *claim* is the three algebra identifications,
  all captured.

- **(b).** `isRealType_iff_exists_real_form` is a real biconditional
  `IsRealType ρ ↔ ∃ W : Submodule ℝ V, (G-stable) ∧ (Submodule.span ℂ W = ⊤) ∧
  (finrank ℝ W = finrank ℂ V)`, both directions proved
  (`exists_real_form_of_isRealType` at 923, `isRealType_of_exists_real_form` at
  1059). The "real form" side is a genuine real subspace `W`: G-stability
  `∀ g v, v ∈ W → ρ g v ∈ W` makes `W` a real subrepresentation, and
  `span_ℂ W = ⊤` together with `finrank_ℝ W = finrank_ℂ V` force the canonical
  map `ℂ ⊗_ℝ W → V` to be an equivariant iso (surjective from span, and
  `finrank_ℝ (ℂ ⊗_ℝ W) = 2·finrank_ℝ W = 2·finrank_ℂ V = finrank_ℝ V`), i.e. V
  is the complexification of W. This is an **equivalent unbundled** encoding of
  "V is the complexification of a real representation" — it does not exhibit a
  standalone `Representation ℝ G W` object or a literal `ℂ ⊗_ℝ W ≃ V`, but the
  membership + span + dimension conditions determine both. Accepted as faithful
  under the same project convention used for the character-/multiplicity-level
  isos in §5.16 / §5.24. Non-vacuous: the forward direction manufactures real
  data (the `+1`-eigenspace of the normalized antilinear `j`), and the `iff` is
  a true two-way implication, not a one-directional shim.

## Exercise 5.1.7 — verdict `covered_full`

Book: any nontrivial finite group of odd order has an irreducible
representation not defined over ℝ (not realizable by real matrices).

`exists_irreducible_not_realType_of_odd_order` (line 49), under
`[Nontrivial G] [Fintype G]` and `(hodd : Odd (Fintype.card G))`, concludes
`∃ V … (ρ : Representation ℂ G V), IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule
∧ (∃ g, ρ g ≠ 1) ∧ ¬ Etingof.IsRealType ρ`.

- **Irreducible**: `IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule` — a genuine
  simplicity assertion, not "some non-real rep".
- **Not defined over ℝ**: `¬ IsRealType ρ`. For an irreducible complex rep this
  is exactly "not realizable by real matrices": by Problem 5.1.2(b) (audited
  above, same project) an irreducible is real type ⟺ it is the complexification
  of a real rep ⟺ defined over ℝ. `¬ IsRealType` on an irrep means complex or
  quaternionic type — both not definable over ℝ. Faithful and internally
  consistent.
- The extra `(∃ g, ρ g ≠ 1)` conjunct only *strengthens* the statement (rules
  out the trivial rep, which is real type anyway).
- **Both hypotheses used.** `Nontrivial G` drives `exists_ne (1 : G)` (line 65)
  for the nontrivial-action witness; `hodd` is passed into the reduction lemma
  `not_isRealType_of_odd_order_of_nontrivial_irreducible` (Exercise 5.3.3, line
  88). Neither is vacuous.

## items.json changes

- `Chapter5/Problem5.1.2`: added `coverage: covered_full`,
  `coverage_arm: audited`, `fidelity: verified`, `fidelity_note`, `lean_file`,
  and a 4-entry `derived` array (a-complex / a-real / a-quaternionic / b).
  Replaced the stale `coverage_note` ("No Lean formalization on origin/main …
  prior 'sorry_free' was vacuous") — a 1205-line sorry-free file is now on
  `origin/main`.
- `Chapter5/Exercise5.1.7`: added `coverage: covered_full`,
  `coverage_arm: audited`, `fidelity: verified`, `fidelity_note`, `lean_file`,
  `lean_decl`. Replaced the stale `coverage_note` ("sorry proof") — the file is
  sorry-free on `origin/main`.

No follow-up `feature` issue is warranted: no sub-part is strictly weaker than
the book. No Lean was modified.
