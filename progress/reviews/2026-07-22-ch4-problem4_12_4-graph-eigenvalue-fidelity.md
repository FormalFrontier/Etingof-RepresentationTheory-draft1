# Stage 3.7 audit — Problem 4.12.4 (nonabelian graph automorphism ⇒ repeated adjacency eigenvalue)

**Issue:** #7265 (statement-fidelity & non-vacuity audit; report-only).
**File:** `EtingofRepresentationTheory/Chapter4/Problem4_12_4.lean`.
**Blob:** `blobs/Chapter4/Problem4.12.4.md`.
**HEAD:** `8dcc00ae` (`origin/main`).
**Verdict:** **VERIFIED** — statement-faithful and non-vacuous.

## Build / axiom check

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_4` exits 0 (8580 jobs,
  no warnings).
- `#print axioms Etingof.Problem4_12_4` returns exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, axiom-clean. The file is
  `sorry`-free (headline theorem plus four supporting lemmas
  `injective_of_squarefree_prod`, `eq_diagonal_of_commute`,
  `commute_of_commute_isHermitian`, `adjMatrix_commute`).

## Book text

> Recall that the adjacency matrix of a graph `Γ` (without multiple edges) is the matrix
> in which the `ij`th entry is 1 if the vertices `i` and `j` are connected with an edge,
> and zero otherwise. Let `Γ` be a finite graph whose automorphism group is nonabelian.
> Show that the adjacency matrix of `Γ` must have repeated eigenvalues.

## Formal statement

```lean
theorem Etingof.Problem4_12_4 {W : Type*} [Fintype W] [DecidableEq W]
    (Γ : SimpleGraph W) [DecidableRel Γ.Adj]
    (hAut : ∃ σ τ : Γ ≃g Γ, σ * τ ≠ τ * σ) :
    ¬ Squarefree (Γ.adjMatrix ℝ).charpoly
```

## Hypothesis faithfulness — `∃ σ τ : Γ ≃g Γ, σ * τ ≠ τ * σ`

- **The automorphism-group object.** `Γ ≃g Γ` is `SimpleGraph.Iso Γ Γ =
  RelIso Γ.Adj Γ.Adj` (Mathlib `Mathlib/Combinatorics/SimpleGraph/Maps.lean:306`,
  notation `≃g` at line 311): adjacency-preserving bijections of the vertex set with
  themselves. This is exactly the graph automorphism group. It carries a `Group`
  instance (confirmed `Group (Γ ≃g Γ) := inferInstance`); there is no separate
  `SimpleGraph.Aut` constant in this Mathlib (v4.32.0-rc1) — `Γ ≃g Γ` *is* the object.
  Correct and not over/under-specified. ✓
- **Multiplication convention.** Confirmed `(σ * τ) x = σ (τ x)` (via `RelIso.mul_apply`).
  The group operation is genuine automorphism composition. ✓
- **"Nonabelian" encoding.** A group is nonabelian iff it is not commutative iff there
  exist two elements that do not commute. `∃ σ τ, σ * τ ≠ τ * σ` is precisely the
  negation of `∀ σ τ, σ * τ = τ * σ` (commutativity). This is the faithful, exact
  rendering of "the automorphism group is nonabelian" — neither a vacuous stand-in nor
  an over-strong strengthening (it does not, e.g., demand a specific nonabelian
  subgroup or a bound on the group). ✓

## Conclusion faithfulness — `¬ Squarefree (Γ.adjMatrix ℝ).charpoly`

The claim to validate: over `ℝ`, because `Γ.adjMatrix ℝ` is real symmetric,
`¬ Squarefree charpoly` ⟺ the matrix has a repeated (real) eigenvalue.

- **The adjacency matrix is Hermitian.** `Γ.adjMatrix ℝ` is symmetric
  (`adj_comm` / the in-proof `hA : (Γ.adjMatrix ℝ).IsHermitian`), so the spectral
  theorem applies.
- **Charpoly splits into real linear factors.** `Matrix.IsHermitian.charpoly_eq` gives
  `A.charpoly = ∏ i, (X - C ↑(hA.eigenvalues i))` with `hA.eigenvalues : W → ℝ` **real**.
  So the characteristic polynomial, taken in `ℝ[X]`, fully factors over `ℝ` as a product
  of monic linear factors indexed by the (real) eigenvalues. There are no residual
  irreducible-quadratic factors that could make "squarefree over `ℝ[X]`" diverge from
  "distinct real roots" — the concern that squarefreeness of a real polynomial need not
  track distinct real eigenvalues is dissolved for exactly this symmetric case.
- **Squarefree ⟺ distinct eigenvalues.**
  - (⇐) distinct eigenvalues ⇒ squarefree: a product of pairwise-distinct monic linear
    factors over a field is squarefree.
  - (⇒) squarefree ⇒ distinct: the file's own `injective_of_squarefree_prod` proves that
    `Squarefree (∏ i, (X - C (d i)))` forces `d` injective (a repeat plants
    `(X - C (d i))²` as a non-unit square factor).
  Hence `¬ Squarefree charpoly` ⟺ `hA.eigenvalues` is **not** injective ⟺ some eigenvalue
  occurs with multiplicity ≥ 2 ⟺ "the adjacency matrix has repeated eigenvalues". The
  encoding neither over- nor under-states the book claim. ✓
- **Real eigenvalues are the right notion.** A real symmetric matrix has only real
  eigenvalues, so "repeated eigenvalue" in the book is unambiguously a repeated real
  eigenvalue — matching `hA.eigenvalues` exactly. ✓

## Non-vacuity

- **Hypothesis satisfiable.** A graph with nonabelian automorphism group exists, e.g. the
  complete graph `K₃` on three vertices, whose automorphism group is the full symmetric
  group `S₃` (order 6, nonabelian). So there is a genuine instance
  `(W, Γ, hAut)` making the antecedent true; the theorem is **not** vacuously true.
- **`W` forced nonempty (and in fact ≥ 3-ish) on any satisfying instance.** If `W` were
  empty (or a singleton), `Γ ≃g Γ` would be trivial (one element), forcing all
  automorphisms equal and hence commuting, so `∃ σ τ, σ * τ ≠ τ * σ` would be false. Thus
  wherever the hypothesis holds, the vertex set is genuinely populated; the statement has
  real content on those instances.
- **No trivially-dischargeable / `True`-typed hypothesis.** `σ * τ ≠ τ * σ` is a genuine
  non-commutativity proposition on real group elements, not `True` and not automatically
  satisfied. The conclusion `¬ Squarefree …` is likewise a real polynomial-theoretic
  statement, not a stub. ✓

## Proof-shape sanity (not a re-verification, but corroborates fidelity)

The proof realizes the intended representation-theoretic argument at matrix level: each
automorphism gives a permutation matrix commuting with `Γ.adjMatrix ℝ`
(`adjMatrix_commute`); if the charpoly were squarefree, the commutant lemma
(`commute_of_commute_isHermitian`, via simultaneous diagonalization by the eigenvector
unitary + `eq_diagonal_of_commute`) forces all such permutation matrices to commute,
hence the two automorphisms commute — contradicting `hAut`. This is the contrapositive of
"nonabelian ⇒ repeated eigenvalue", and it confirms the hypothesis and conclusion are
wired to each other in the intended way (no short-circuit that would render either side
inert).

## Verdict

**VERIFIED.** `Etingof.Problem4_12_4` faithfully formalizes Problem 4.12.4:
`∃ σ τ : Γ ≃g Γ, σ * τ ≠ τ * σ` is exactly "automorphism group nonabelian",
`¬ Squarefree (Γ.adjMatrix ℝ).charpoly` is exactly "the (real symmetric) adjacency matrix
has a repeated eigenvalue", the hypothesis is satisfiable (`K₃`/`S₃`) so the theorem is
non-vacuous, and the declaration is `sorry`-free and axiom-clean. No fidelity gap; no
follow-up issue needed; no Lean edits.
