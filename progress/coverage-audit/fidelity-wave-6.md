# Fidelity sweep — Wave 6 (Chapter 6, issue #5343)

Judge: Opus 4.8 (four parallel Opus sub-auditors + Opus adjudication), distinct
from the Sonnet/other authors and the Codex wave-4 verdict pass of the items
below.
Scope: all 36 Chapter 6 claim-bearing done items (types theorem / proposition /
lemma / corollary / definition / example / remark).
Method: PLAN.md Stage 3.2 steps 6–7 — anti-vacuity decision test, then
conjunct-by-conjunct fidelity of the Lean statement against the book blob.
Calibrated on confirmed examples #5322, #5323, #5326.

## Outcome

After this wave every Chapter 6 claim-bearing done item (36 total) is
**`verified` (36)**; **0 gaps** remain. The four items that entered this wave
marked `gap` were re-audited against the *current* (post-repair) Lean; all four
repairs have merged, and all four are now `verified` with their stale
`fidelity_issue` dropped. Only `progress/items.json` and this file were
touched — no Lean changes.

### Gap → verified reconciliations

- **Definition6.5.1** (`Etingof.dimensionVector`) — was `gap` with **no
  `fidelity_issue`** (a `[structural]` note only). The `def` genuinely
  constructs `d(V) = fun v => Module.finrank k (spaces v)`, the tuple of vertex
  dimensions. The note observed only that the input is a bare space-family
  `spaces : V → Type*` rather than a bundled `QuiverRepresentation`; the
  dimension vector depends only on the vertex spaces, so this is a faithful
  (slightly more general) rendering, not a fidelity defect. → **verified**.
- **Definition6.7.1** (`Etingof.coxeterElement`) — was `gap` (`fidelity_issue
  #5625`, **closed/merged**). The current def folds the genuine root-lattice
  `simpleReflection`s of the Cartan matrix, `c = s_1 s_2 ⋯ s_n` acting on the
  root lattice ℤⁿ — no longer an abstract list-product in an arbitrary group.
  #5625's defect is resolved. → **verified**, `fidelity_issue` dropped.
- **Corollary6.8.2** (`Etingof.Corollary6_8_2`, in `CoxeterInfrastructure.lean`)
  — was `gap` (`fidelity_issue #5624`, **closed/merged**). The current statement
  quantifies over an *arbitrary* indecomposable representation `ρ` of an
  orientation `Q` of the Dynkin diagram and concludes
  `IsPositiveRoot n adj d(V)`; the reflection chain reducing `d(V)` to a simple
  root is *produced* internally (via `indecomposable_reduces_to_simpleRoot` /
  Theorem 6.8.1), not taken as a hypothesis. #5624's "hard existential as a
  hypothesis" defect is resolved. → **verified**, `fidelity_issue` dropped.
- **Example6.8.5** (`Etingof.Example6_8_5_part1 / _part2 /
  _maximal_indecomposable`) — was `gap` (`fidelity_issue #5639`,
  **closed/merged**). Parts 1/2 apply the genuine D₄ root-lattice
  `simpleReflection`s (built from `cartanMatrix 4 D₄_adj` + `simpleRoot`) to
  `α₄`, giving `(1,1,1,1)` then `(1,1,1,2)`; part 3 confirms `(2,1,1,1) ∈
  D₄_indecomposable_dimVectors`. The statements are dimension-vector-level, but
  that is the book's checkable content and the functor↔reflection bridge
  `d(F_i^± V) = s_i(d(V))` is the separately-proved Proposition 6.6.8.
  #5639's "disconnected shadow object" defect is resolved. → **verified**,
  `fidelity_issue` dropped.

### Re-confirmed headline items (spot-checked directly, not just via sub-auditor)

- **Theorem6.5.2** (`Etingof.Theorem_6_5_2_Gabriels_theorem`) — the combined
  Gabriel's theorem now genuinely asserts all three parts as a non-vacuous
  conjunction: (a) `Set.Finite {d | IsPositiveRoot n adj d}`; (b) a real
  implication `ρ.IsIndecomposable → IsPositiveRoot n adj (finrank ∘ ρ.obj)`,
  discharging the `B(d,d)=2` obligation via
  `indecomposable_bilinearForm_eq_two`; (c) existence **and**
  uniqueness-up-to-iso of an indecomposable per positive root. The wave-4
  concern (#5670, merged) that the combined decl "only re-exported finiteness"
  is resolved. → **verified**.
- **Theorem_Dynkin_classification** / **Problem6.1.5_theorem** — full `↔`
  statements with genuinely constructed A/D/E adjacency matrices (all of
  A_n, D_n, E6, E7, E8 present even where the blob is truncated), both
  directions proved. → **verified**.

## Verdicts (all 36 — verified)

§6.1–6.3: Definition6.1.4, Theorem_Dynkin_classification, Problem6.1.5_theorem,
Remark6.2.1 (pure notational convention, no Lean decl needed), Example6.2.2,
Example6.2.3, Example6.2.4, Example6.3.1 — all **verified**. The A₁/A₂/A₃/D₄
indecomposable-classification examples state ∀-over-indecomposables with the
injectivity conjuncts preserved and the dimension-vector sets carded exactly.

§6.4: Definition6.4.1 (`cartanMatrix = 2·Id − adj`), Lemma6.4.2 (pos-def +
even), Definition6.4.3 (`IsRoot`: x≠0 ∧ B(x,x)=2), Remark6.4.4 (finiteness,
covered by 6.5.2a), Definition6.4.5 (`simpleRoot = Pi.single i 1`), Lemma6.4.6
(every root all-nonneg or all-nonpos), Definition6.4.7
(`IsPositiveRoot`/`IsNegativeRoot`), Remark6.4.8 (= Lemma6.4.6), Example6.4.9
(positive-root counts A_n=n(n+1)/2, D_n=n(n−1), E6=36, E7=63, E8=120, each with
a finiteness conjunct), Definition6.4.10 (`rootReflection`/`simpleReflection`),
Remark6.4.11 (B-preservation, formalized) — all **verified**.

§6.5–6.6: Definition6.5.1, Theorem6.5.2, Definition6.6.1 (`IsSink`/`IsSource`),
Definition6.6.2 (`reversedAtVertex`), Definition6.6.3 (`reflectionFunctorPlus`,
ker φ), Definition6.6.4 (`reflectionFunctorMinus`, coker ψ), Proposition6.6.5
(simple-at-i ∨ φ surjective / ψ injective), Proposition6.6.6 (double-reversal
iso), Proposition6.6.7 (F_i^± indecomposable or 0), Proposition6.6.8
(`d(F_i^± V) = s_i(d(V))`) — all **verified**. All reflection-functor `def`s are
sorry-free and genuinely construct their objects and arrow maps.

§6.7–6.8: Definition6.7.1, Lemma6.7.2, Theorem6.8.1
(`indecomposable_reduces_to_simpleRoot`, dimension-vector core), Corollary6.8.2,
Corollary6.8.3 (equal finranks ⇒ iso), Corollary6.8.4 (each positive root has
an indecomposable realizer), Example6.8.5 — all **verified**.

## Notes / caveats recorded (not gaps)

- Several examples (6.2.x, 6.3.1, 6.8.5) formalize one representative orientation
  of the quiver; the book's remark that the indecomposable count is
  orientation-independent is itself captured by Gabriel's theorem (dimension
  vectors = positive roots, orientation-free). Accepted as faithful.
- Theorem6.8.1 / Example6.8.5 are stated at the dimension-vector level; the
  representation-level functor content is carried by Proposition 6.6.8 (proved).
  This mirrors the book's own proof, which argues via dimension vectors.
