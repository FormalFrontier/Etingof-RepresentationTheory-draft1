# Review — Ch6 Theorem: Classification of Dynkin diagrams

- **Issue:** #7136 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/0e8d31f8`
- **Target:** `Etingof.Theorem_Dynkin_classification`
  (`EtingofRepresentationTheory/Chapter6/Theorem_Dynkin_classification.lean:1549`, file 1560 lines),
  supporting `Etingof.DynkinType` / `.rank` / `.adj` and `Etingof.isDynkinDiagram_of_type`
  in `EtingofRepresentationTheory/Chapter6/DynkinTypes.lean` (1143 lines),
  `Etingof.IsDynkinDiagram` in `EtingofRepresentationTheory/Chapter6/Definition6_1_4.lean:25`.
- **Fidelity reference:** `blobs/Chapter6/Theorem_Dynkin_classification.md` (+ `.refs.md`),
  `blobs/Chapter6/Definition6.1.4.md`, `blobs/Chapter6/Problem6.1.3.md`
  (the setup that defines Γ, R, A), `blobs/Chapter6/Discussion_after_Definition6.1.4.md`.
- **Focus areas:** statement fidelity (definition of Dynkin diagram; the ADE enumeration;
  the graph-isomorphism `iff` framing; the `1 ≤ n` scope) and non-vacuity (axiom-cleanliness,
  both directions genuinely witnessed). Report-only — no `.lean` file was modified.
- **Overall verdict:** **FAITHFUL** (with one documented scope nuance — simple vs multi-edge
  graphs — that does **not** change the classified set and is **not** a defect; §3).
  `IsDynkinDiagram` is the book's Definition 6.1.4 (positive-definite Cartan form `A = 2I − R`)
  bundled with the Problem 6.1.3 standing hypotheses (finite, connected, no self-loop). The
  `DynkinType` enumeration is **exactly** the book's list — Aₙ (n ≥ 1), Dₙ (n ≥ 4), E₆, E₇, E₈,
  with the correct branch structure and no spurious B/C/F/G types. The `∃ σ : Fin t.rank ≃ Fin n`
  framing faithfully renders "is one of the following graphs up to relabelling", and `1 ≤ n`
  correctly excludes the vacuous empty-graph case. Both directions are genuine content: the
  forward direction is a ~1500-line proof (degree bound → branch/path case split → Dₙ/E vs Aₙ),
  the backward direction is witnessed by the sorry-free realizability lemma `isDynkinDiagram_of_type`
  covering all five families. The theorem and the realizability lemma are both axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no custom axiom). **No defect filed.**

---

## 0. Build and axiom-cleanliness audit

`lake build EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification` exits 0
(8583 jobs; only `linter.style.show` and a `push_neg`-deprecation warning, no errors).
`#print axioms` on the two load-bearing declarations:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.Theorem_Dynkin_classification` | `Theorem_Dynkin_classification.lean:1549` | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.isDynkinDiagram_of_type` | `DynkinTypes.lean:1132` | `[propext, Classical.choice, Quot.sound]` |

Both are exactly the three standard axioms — **no `sorryAx`, no stray custom axiom.** A
word-boundary grep for `sorry`/`admit`/`axiom` over `Definition6_1_4.lean`, `DynkinTypes.lean`,
`Theorem_Dynkin_classification.lean`, and `Problem6_1_3_continued_E7_E8.lean` returns nothing.
Since `isDynkinDiagram_of_type` is axiom-clean and case-splits into `An_isDynkin`, `Dn_isDynkin`,
`E6_isDynkin`, `E7_isDynkin`, `E8_isDynkin`, all five per-family realizability proofs are
transitively sorry-free.

---

## 1. Statement fidelity

**Book (Theorem, §6.1, following Problem 6.1.3 / Definition 6.1.4).**
*"Γ is a Dynkin diagram if and only if it is one of the following graphs: Aₙ, Dₙ, E₆, E₇, E₈."*
The book's `.refs.md` confirms the intended list is exactly the simply-laced family
(Aₙ, Dₙ, E₆, E₇, E₈) — **no B/C/F/G**. The setup (Problem 6.1.3) fixes Γ as a finite, connected,
self-loop-free graph on vertices `1..n` with adjacency matrix `R = (r_ij)` and Cartan matrix
`A = 2I − R`; Definition 6.1.4 declares Γ a Dynkin diagram iff the quadratic form of `A` is
positive definite.

**Lean statement.**
```
theorem Theorem_Dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsDynkinDiagram n adj ↔
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n, ∀ i j, adj (σ i) (σ j) = t.adj i j
```

- **`IsDynkinDiagram` (Definition6_1_4.lean:25) is a faithful, non-vacuous predicate.** It is the
  conjunction: `adj` symmetric, zero diagonal (`∀ i, adj i i = 0`), 0/1 entries, connected
  (path of adjacency-1 edges between any two vertices), **and** positive-definiteness of the
  Cartan form `∀ x ≠ 0, 0 < xᵀ(2·Id − adj)x`. The final clause is precisely book Definition 6.1.4
  (quadratic form of `A = 2I − R` positive definite). The symmetry / zero-diagonal / connectivity
  clauses are the Problem 6.1.3 standing hypotheses on Γ (finite connected self-loop-free graph),
  moved from the ambient setup into the predicate — a legitimate encoding, since the book's domain
  of discourse is exactly such graphs. This is not an unrelated or vacuously-true predicate: the
  positive-definiteness clause is a genuine constraint (e.g. a 4-cycle or a double edge fails it),
  and the realizability lemmas of §2 exhibit matrices that satisfy the whole conjunction.

- **`DynkinType` enumerates exactly the book's list.** `inductive DynkinType | A (n) (hn : 1 ≤ n)
  | D (n) (hn : 4 ≤ n) | E6 | E7 | E8` (DynkinTypes.lean:27). Five constructors, matching
  Aₙ/Dₙ/E₆/E₇/E₈ — **no missing type and no extra B/C/F/G**, consistent with `.refs.md`. Rank is
  correct (`.A n`/`.D n` → `n`; `.E6/E7/E8` → `6/7/8`). The `.adj` matrices (DynkinTypes.lean:49)
  encode the correct graphs:
  - **Aₙ**: path `0—1—…—(n-1)` (edge iff `|i−j| = 1`). Book Aₙ. ✓
  - **Dₙ**: path `0—…—(n-2)` with fork edge `(n-3)—(n-1)`, so vertex `n-3` is trivalent (neighbours
    `n-4`, `n-2`, `n-1`) — the book's "path with a branch at the second-to-last vertex". Requires
    `4 ≤ n`, matching the book (Dₙ starts at D₄). ✓
  - **E₆/E₇/E₈**: linear chain with a single length-1 branch at vertex 2. Arm lengths from the
    trivalent node are `(1,2,2)` for E₆, `(1,2,3)` for E₇, `(1,2,4)` for E₈ — exactly the standard
    exceptional Dynkin diagrams. ✓

- **The `∃ σ : Fin t.rank ≃ Fin n, ∀ i j, adj (σ i) (σ j) = t.adj i j` framing is faithful.**
  An `Equiv` between `Fin t.rank` and `Fin n` forces `t.rank = n` (vertex counts agree) and is a
  vertex relabelling; the condition says `adj` is the pushforward of `t.adj` under σ. This is
  precisely "Γ is isomorphic as a graph to one of the standard types", i.e. "is one of the
  following graphs up to relabelling". ✓

- **The `1 ≤ n` hypothesis is correct and necessary.** For `n = 0` every clause of
  `IsDynkinDiagram` quantifies over the empty `Fin 0` and is vacuously true, yet no `DynkinType`
  has rank 0, so the `iff` would fail without `hn`. The book's Γ is a nonempty graph on `1..n`,
  so the empty graph is correctly out of scope; the smallest diagram is A₁. The file's own
  docstring documents this exact point. ✓

---

## 2. Non-vacuity — both directions genuinely witnessed

- **Backward (`⇐`, realizability).** `rintro ⟨t, σ, hiso⟩; exact isDynkinDiagram_of_type σ hiso
  (isDynkinDiagram_of_type t)` via `isDynkinDiagram_of_graph_iso`. The lemma
  `isDynkinDiagram_of_type (t : DynkinType) : IsDynkinDiagram t.rank t.adj` (DynkinTypes.lean:1132)
  is sorry-free and case-splits into `An_isDynkin`, `Dn_isDynkin`, `E6_isDynkin`, `E7_isDynkin`,
  `E8_isDynkin`. Each proves the full conjunction, including positive-definiteness via explicit
  sum-of-squares / recurrence arguments (`pathQF` for Aₙ, `DnQF` for Dₙ, direct `nlinarith`
  SOS decompositions for the E-types). So the enumeration is genuinely inhabited and each standard
  type genuinely satisfies `IsDynkinDiagram` — the `iff` is not vacuously true on the right.
  (These are the same facts re-exported as `isDynkinDiagram_A/D/E` in
  `Problem6_1_3_continued_E7_E8.lean:306-350`.)

- **Forward (`⇒`, classification).** `dynkin_classification_forward`
  (`Theorem_Dynkin_classification.lean:1521`) is real content, not a placeholder: it establishes
  every vertex has degree ≤ 3 (`dynkin_degree_le_three`), then case-splits on the existence of a
  degree-3 vertex — branch case → `branch_classification` (Dₙ or an E-type), path case →
  `path_iso_An` (Aₙ). The supporting file `Problem6_1_3_continued_E7_E8.lean` supplies the
  structural lemmas (tree-ness, degree ≤ 3, unique branch vertex) the classification rests on.
  The ~1500 lines of proof are the genuine mathematical heart (bounding arm lengths to rule out
  affine/indefinite diagrams), confirmed sorry-free by §0.

---

## 3. The one fidelity nuance — simple vs multi-edge graphs (NOT a defect)

Problem 6.1.3's setup says *"we allow multiple edges"*: `R = (r_ij)` counts edges, so a priori
`r_ij ≥ 0` may exceed 1. The Lean `IsDynkinDiagram` restricts to **simple** graphs via the clause
`∀ i j, adj i j = 0 ∨ adj i j = 1`. So the Lean theorem is stated over 0/1 adjacency matrices,
whereas the book nominally admits multigraphs.

**Why this does not change the theorem's content and is not a defect:**

- The book's *answer* is the ADE list — all of which are simple graphs. No multigraph appears
  in the classification.
- Any multi-edge already fails positive-definiteness: a double edge between `i, j` gives the
  principal `2×2` minor `[[2,−2],[−2,2]]` (determinant 0, only positive *semi*-definite); a triple
  edge gives `[[2,−3],[−3,2]]` (determinant −5). By Sylvester's criterion the full Cartan form is
  then not positive definite, so no multigraph is a Dynkin diagram in the book's sense.
- Hence the set of Dynkin diagrams is identical whether or not one restricts to simple graphs, and
  the Lean statement classifies exactly the same objects the book does.

What the Lean formalization *omits* is only the trivial auxiliary observation "a positive-definite
connected loopless multigraph must in fact be simple" — it assumes simplicity rather than deriving
it. This is a scope narrowing of the hypothesis, not a weakening of the classification's
substantive content (the hard forward direction over simple graphs, and the realizability of all
five families, are both fully formalized). The prior Gabriel audit
(`2026-07-21-ch6-theorem6_5_2-gabriel-fidelity.md`) already treats "positive-definite simple graph"
as the faithful encoding of "ADE type". I record the nuance here for completeness; it warrants no
DEFECT issue and no edit.

---

## 4. Verdict

**FAITHFUL.** The statement is a correct, non-vacuous rendering of the book's classification:
the definition of "Dynkin diagram" is Definition 6.1.4 (positive-definite Cartan form) with the
Problem 6.1.3 graph hypotheses; the enumeration is exactly Aₙ/Dₙ/E₆/E₇/E₈ with correct rank
bounds and branch structure; the `iff` and the `Equiv`-based graph-isomorphism framing are
accurate; `1 ≤ n` correctly scopes out the empty graph. Both directions are genuine, sorry-free
content, and the two load-bearing declarations are axiom-clean. The sole nuance — the simple-graph
(0/1) restriction versus the book's "we allow multiple edges" — leaves the classified set
unchanged (no multigraph is positive definite) and is a standard, accepted formalization choice,
not a defect. No DEFECT issue filed; no Lean file modified (report-only audit).
