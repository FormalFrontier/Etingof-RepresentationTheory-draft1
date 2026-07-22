# Stage 3.7 coverage-arm audit — Chapter 3 standalone items (#7371)

Coverage-arm audit of three sorry-free, fidelity-verified standalone Chapter 3
items that lacked a `coverage` field in `progress/items.json`:
**Problem 3.3.3**, **Exercise 3.6.1**, **Exercise 3.10.1**.

Judged by a different model than formalized them. The prior `fidelity: verified`
markings stand and are reused; this audit adds the honest `coverage` field (at
sub-part granularity for the multi-part 3.3.3) and reconciles notes. No full
fidelity re-sweep was performed — only the deliverable-2 spot checks (the two
statements flagged as potentially weaker than the book claim).

## Build / axiom verification

All three modules build sorry-free (`lake build`, 0 sorries each; only style
linter warnings — deprecated `push_neg`, `show`-changes-goal). `#print axioms`
on every headline decl shows only `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`):

- `Etingof.Problem3_3_3.simpleModule_prod_iff`
- `Etingof.Problem3_3_3.std_isSimpleModule`
- `Etingof.Problem3_3_3.simpleModule_iso_std`
- `Etingof.Problem3_3_3.finite_iso_std_pow`
- `Etingof.character_eq_character_add_character_quotient`
- `Etingof.matrix_tensorProduct_matrix`

## Coverage assignments

### Problem 3.3.3 — `covered_full` (roll-up over formalizable sub-parts)

Multi-part alternative proof of Theorem 3.3.1. Recorded at sub-part granularity
via a `derived` array; roll-up = min over the *formalizable* sub-parts (non_formalizable
(c) excluded).

- **(a) `covered_full`** — `simpleModule_prod_iff`. For the product ring
  `A = ∀ i, 𝒜 i` and an arbitrary `A`-module `V`,
  `IsSimpleModule A V ↔ ∃ i, IsSimpleModule A (range (idemProj i)) ∧ ∀ j ≠ i, range (idemProj j) = ⊥`.
  Faithful to "V irreducible iff `1ᵢV` irreducible over `Aᵢ` for exactly one `i`,
  `1ⱼV = 0` otherwise": `1ᵢV` is the honest central-idempotent range
  (`idemProj i : v ↦ 1ᵢ • v`, `A`-linear because `1ᵢ` is central), and a simple
  module is nonzero so the `∃ i` with the `∀ j ≠ i` vanishing pins the "exactly
  one". Pure ring/module theory — no base field needed, correctly reflecting the
  book.

- **(b) `covered_full`** — `std_isSimpleModule` + `simpleModule_iso_std` +
  `finite_iso_std_pow`. Both book claims are present: the first two give "the
  only irreducible representation of `Mat_d(k)` is `k^d`" (`k^d = Fin d → k` is
  simple; any f.d. simple `≃ₗ[Mat_d(k)] k^d`), the third gives "every f.d.
  representation is a direct sum of copies of `k^d`" (any f.d. rep
  `≃ₗ[Mat_d(k)] (Fin n → (Fin d → k))`). Proved via the book's elementary
  matrix-unit argument (the `psi` map `w ↦ ∑ₐ wₐ • (E_{a0} • v)`), deliberately
  not Wedderburn–Artin. `NeZero d` present; equivalences are genuine
  `Mat_d(k)`-linear (`≃ₗ[Matrix (Fin d) (Fin d) k]`).

- **(c) `non_formalizable`** — "Deduce Theorem 3.3.1." No distinct decl in
  `Problem3_3_3.lean`. The statement to be deduced is recorded and proved
  independently as `Etingof.irreducible_reps_of_matrix_algebra`
  (`Theorem3_3_1.lean:239`, via Wedderburn–Artin). The problem's pedagogical
  "deduce it from (a),(b)" wiring is expository and not separately formalized as
  a deduction, so it carries no distinct Lean decl. Marked `non_formalizable`
  (with reason), excluded from the roll-up min. The mathematical content of (c)
  is not lost — it exists as `irreducible_reps_of_matrix_algebra`.

### Exercise 3.6.1 — `covered_full`

`character_eq_character_add_character_quotient`:
`Etingof.character k A V = Etingof.character k A W + Etingof.character k A (V ⧸ W)`
for a finite dimensional representation `V` of an algebra `A` and an **arbitrary**
subrepresentation `W : Submodule A V`. Deliverable-2 spot check confirmed: `W` is
genuinely universally quantified (not a fixed hand-picked submodule), and the
quotient character is over the honest `V ⧸ W` representation. Equality holds in
`Dual k A`. This is exactly the book's `χ_V = χ_W + χ_{V/W}`.

### Exercise 3.10.1 — `covered_full`

`matrix_tensorProduct_matrix`:
`Nonempty ((Mat_m(k) ⊗[k] Mat_n(k)) ≃ₐ[k] Mat_{mn}(k))`. Deliverable-2 spot check
confirmed the iso is a genuine `k`-**algebra** isomorphism (`≃ₐ[k]`), not merely
`k`-linear or a ring iso: it is `kroneckerTMulAlgEquiv` composed with
`Algebra.TensorProduct.rid` (via `mapMatrix`) and `reindexAlgEquiv` along
`finProdFinEquiv`. Faithful to the book's `Mat_m(k) ⊗ Mat_n(k) ≅ Mat_{mn}(k)`,
and in fact strengthened from the book's field `k` to an arbitrary `CommRing k`.

## Outcome

All three items assigned honest `coverage` fields; `progress/items.json` parses.
Status/`coverage_note`/`coverage` are internally consistent. No sub-part's Lean
statement is strictly weaker than the book's claim (3.6.1 and 3.10.1 are, if
anything, more general), so **no follow-up `feature` issue is needed**.
