# Review — Ch6 Theorem 6.5.2: Gabriel's Theorem

- **Issue:** #7106 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/e5614688`
- **Target:** `EtingofRepresentationTheory/Chapter6/Theorem6_5_2.lean` (302 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter6/Theorem6.5.2.md`, `blobs/Chapter6/Discussion_before_Theorem6.5.2.md`
- **Focus areas:** statement fidelity per book part (a)/(b)/(c); non-vacuity / hidden-hypothesis audit (the crux); docstring-correspondence accuracy (report-only, no `.lean` edits)
- **Overall verdict:** **FAITHFUL.** All three book parts are formalized with the correct
  quantifiers and hypotheses; part (c)'s "exactly one … up to isomorphism" is split into
  genuine existence AND uniqueness; the combined theorem states part (b) as a real
  `indecomposable ⇒ positive root` implication and genuinely discharges the standalone
  version's `B(d,d) = 2` hypothesis via a proved lemma (not an assumption). All four
  audited declarations build and are axiom-clean (`[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`). Every hypothesis is jointly satisfiable, and both universally-quantified
  parts range over genuinely nonempty classes (simple representations witness indecomposables;
  simple roots witness positive roots), so **no part is vacuously true.** **No defect filed.**
  One fidelity nuance worth recording (part (a) encodes the book's headline
  "finitely many indecomposable representations" as finiteness of the *positive-root set* —
  equivalent given (b)+(c), and framed that way in the file's own formalization note) is
  documented below. It is not a defect.

---

## 0. Build and axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter6.Theorem6_5_2` (`lake build`, exit 0, 8606 jobs)
and ran `#print axioms` on all four declarations named in the issue. **Every** result is
exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no stray custom axiom:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.Theorem_6_5_2a_finiteness` | 159 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem_6_5_2b_dimvec_is_positive_root` | 190 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem_6_5_2c_bijection` | 208 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem_6_5_2_Gabriels_theorem` | 257 | `[propext, Classical.choice, Quot.sound]` |

A word-boundary `sorry` grep over the target file and its Chapter 6 dependency files
(`CoxeterInfrastructure.lean`, `Corollary6_8_3.lean`, `Corollary6_8_4.lean`) returns nothing
(excluding "sorry-free" prose). The proof chain for the crux — part (b) — is real content,
not a placeholder (traced in §2).

---

## 1. Statement fidelity, per part

**Book (Theorem 6.5.2, Gabriel's theorem).** *"Let Q be a quiver of type Aₙ, Dₙ, E₆, E₇, E₈.
Then Q has finitely many indecomposable representations. Namely, the dimension vector of any
indecomposable representation is a positive root (with respect to B_Γ) and for any positive
root α there is exactly one indecomposable representation with dimension vector α."*

The book packs three claims into that sentence; the file states them as three declarations
and re-assembles them. Underlying definitions all check out against the blobs:

- `IsDynkinDiagram n adj` (Def 6.1.4): symmetric 0/1 adjacency, zero diagonal, connected,
  **positive-definite Cartan form**. This is the book's *definition* of a Dynkin diagram
  (Def 6.1.4), which by the classification is exactly the ADE list of the theorem statement.
  Encoding "type Aₙ/Dₙ/E₆₋₈" as "positive-definite simple graph" is the book's own
  characterization — faithful, not a narrowing.
- `IsPositiveRoot n adj d` (Def 6.4.7 ∘ 6.4.3): `d ≠ 0 ∧ B(d,d) = 2 ∧ ∀ i, 0 ≤ d i`, with
  `B(x,y) = xᵀ(2·Id − adj)y` (Def 6.4.1). Faithful transcription of "positive root w.r.t. B_Γ".
- `cartanMatrix n adj := 2 • 1 − adj` (Def 6.4.1) — matches, and is definitionally the matrix
  used throughout part (a)/(b).

### Part (a) — `Theorem_6_5_2a_finiteness` (line 159)

States `Set.Finite {d : Fin n → ℤ | IsPositiveRoot n adj d}`: for a Dynkin diagram the set of
positive roots is finite. The proof is genuine (Cauchy–Schwarz-style bound: `d ↦ Cd` is
injective by positive-definiteness and lands in the finite box `[-2,2]ⁿ`). **Faithful, with a
recorded nuance:** the book's *headline* first sentence is "Q has finitely many indecomposable
representations," whereas the Lean conjunct is finiteness of the positive-root *set*. These are
equivalent **given** parts (b)+(c) — dimension-vector is a well-defined map from iso-classes of
indecomposables (b) that is injective (c-uniqueness) into the finite positive-root set (a) — and
the module docstring / formalization note frames the three parts exactly this way. This is a
faithful re-expression, not an over- or under-statement. See §4 for why it is not a defect.

### Part (b) — `Theorem_6_5_2b_dimvec_is_positive_root` (line 190) and the combined (b)

Book claim: "the dimension vector of any indecomposable representation is a positive root."

The **standalone** declaration is deliberately a repackaging: given `d` nonneg (`hd_pos`),
nonzero (`hd_nonzero`), and satisfying `B(d,d) = 2` (`hd_root`), it concludes
`IsPositiveRoot n adj d`. It takes `B(d,d) = 2` as a *hypothesis* rather than deriving it — so
on its own it carries none of the theorem's mathematical content (the docstring is honest about
this; see §3). The real content lives in the **combined** theorem's part (b), audited in §2.

### Part (c) — `Theorem_6_5_2c_bijection` (line 208) and combined (c)

Book claim: "for any positive root α there is exactly one indecomposable representation with
dimension vector α." The Lean statement splits "exactly one … up to isomorphism" into:

- **Existence** — `∃ ρ`, free and finite over `k` at every vertex, `ρ.IsIndecomposable`, with
  `∀ v, α v = finrank k (ρ.obj v)` (dimension vector = α). Discharged by `Corollary6_8_4`
  (every positive root is realized).
- **Uniqueness** — any two such (indecomposable, free+finite, both with dimension vector α) admit
  `Nonempty (QuiverRepresentation.Iso ρ₁ ρ₂)`. Discharged by `Corollary6_8_3` (dimension vector
  determines the indecomposable up to iso).

Both halves are genuine (not `True`, not one-directional). "Up to isomorphism" is correctly
rendered as `Nonempty (…Iso…)`. **Faithful.**

---

## 2. Non-vacuity / hidden-hypothesis audit (the crux)

**(i) Combined (b) is a real `indecomposable ⇒ positive root` implication, and the `B(d,d)=2`
hypothesis is genuinely discharged.** In `Theorem_6_5_2_Gabriels_theorem` the (b) conjunct
(lines 267–270) quantifies over an arbitrary indecomposable, finite-dimensional `ρ` and concludes
`IsPositiveRoot n adj (fun v => finrank k (ρ.obj v))`. The proof (lines 284–298) calls the
standalone (b) and must supply its three inputs:

- nonneg — `Int.natCast_nonneg` (finranks are ≥ 0);
- nonzero — derived from indecomposability: `hρ.1` yields a vertex `v` with `Nontrivial (ρ.obj v)`,
  and `finrank = 0 → Subsingleton` contradicts it (lines 288–296);
- `B(d,d) = 2` — **`Etingof.indecomposable_bilinearForm_eq_two hDynkin hQ ρ hρ`** (line 298).

Tracing that lemma (`CoxeterInfrastructure.lean:1731`): it is `(Corollary6_8_2 …).1.2`, and
`Corollary6_8_2` (`CoxeterInfrastructure.lean:1696`) is a **proved** theorem — it *produces* a
reflection sequence from the representation via `indecomposable_reduces_to_simpleRoot`
(rep-level Theorem 6.8.1) and feeds it to the combinatorial core
`isPositiveRoot_of_iteratedReflection_eq_simpleRoot`. So `B(d,d) = 2` is *derived from
indecomposability*, not assumed. The docstring's claim (lines 246–248) is accurate.

**(ii) No hypothesis is unsatisfiable; the theorem is not vacuous.**

- `IsDynkinDiagram n adj` — satisfiable (e.g. A₁: `n = 1`, `adj = 0`; positive-definite since
  `B(x,x) = 2x₀²`).
- `IsOrientationOf Q adj` together with `[∀ a b, Subsingleton (Q.Hom a b)]` — jointly satisfiable:
  `standardOrientation adj` is proved to be an orientation (`standardOrientation_isOrientationOf`)
  and carries a `Subsingleton` `Hom` instance (`standardOrientation_subsingleton`). The
  `Subsingleton (Hom a b)` instance faithfully encodes "at most one arrow per ordered pair" —
  natural for an orientation of a *simple* (0/1) graph, and `IsOrientationOf` already forbids
  arrows in both directions of an edge. It does **not** narrow the theorem below the book's
  Dynkin quivers.
- `Module.Free k` / `Module.Finite k` at each vertex — the faithful encoding of
  "finite-dimensional representation" over a field (`Free` is automatic over a field; stated for
  universe/generality hygiene). No narrowing.
- The field `k` is **arbitrary** — at least as general as the book. No under-statement.

**(iii) Both universal parts range over nonempty classes (quantifiers not vacuous).**

- Part (b)'s `∀ ρ indecomposable`: indecomposables exist — `simpleRepresentation_indecomposable`
  (`Corollary6_8_4.lean:120`) proves the simple representation at each vertex is indecomposable.
- Part (c)'s `∀ α positive root`: positive roots exist — every simple root is one, realized by an
  indecomposable (`Corollary6_8_4_simpleRoot`, `Corollary6_8_4.lean:174`).

So neither `∀` is over an empty domain, and the existence half of (c) is a real production of an
object. **Non-vacuity verdict: the combined theorem is non-vacuous and all its parts carry
content.**

---

## 3. Docstring-correspondence accuracy

- **"Gabriel's theorem is NOT in Mathlib"** (module docstring, lines 22–25) — correct. Mathlib
  has quiver and root-system scaffolding but no Gabriel correspondence.
- **Standalone (b) docstring** (lines 184–189) — honestly describes the declaration as: *given* a
  nonneg nonzero `d` with `B(d,d) = 2`, conclude positive root. It does not claim to derive
  `B(d,d)=2`. Accurate (the derivation is explicitly the combined theorem's job).
- **Combined (b) docstring** (lines 245–248) — claims (b) is stated "as a genuine implication
  `indecomposable ⇒ positive root`, discharging the `B(d,d) = 2` hypothesis … via
  `indecomposable_bilinearForm_eq_two`." Verified accurate against the proof (line 298) and the
  lemma's proof chain (§2(i)).
- **"faithful canonical statement … the three parts … assembled here"** (lines 252–255) — accurate:
  the combined theorem's three conjuncts match `Theorem_6_5_2a_finiteness` verbatim (a),
  the discharged form of the standalone (b), and the existence+uniqueness of
  `Theorem_6_5_2c_bijection` (c). No drift.

---

## 4. Why the part-(a) nuance is not a defect

The only place the Lean is a *re-expression* rather than a literal transcription is part (a):
the book's first clause reads "Q has finitely many indecomposable representations," while the Lean
conjunct is `Set.Finite {d | IsPositiveRoot n adj d}`. This is faithful because:

1. The dimension-vector map from iso-classes of finite-dimensional indecomposables to positive
   roots is well-defined by (b) and injective by (c)-uniqueness, and its codomain is finite by (a);
   hence there are finitely many iso-classes of indecomposables. This is the standard reading of
   Gabriel's theorem and the intended meaning of "finitely many indecomposable representations"
   (up to isomorphism).
2. The file's own module docstring and formalization note (lines 29–38) explicitly present the
   three parts in this decomposed form, so the encoding is disclosed, not silent.

A stricter formalization could add a fourth conjunct asserting `Set.Finite` of the set of
iso-classes of indecomposables directly, but that would be a derived convenience, not a
correction — the mathematical content is already fully present and axiom-clean. **Not filed as a
defect.** (If a future planner wants the literal headline as a stated corollary, that is a
`feature` enhancement, not a fidelity fix.)

---

## Verdict

**FAITHFUL — no defect, nothing filed.**

- Part (a): FAITHFUL (finiteness of positive roots; headline "finitely many indecomposables"
  faithfully encoded via (b)+(c), disclosed in-file).
- Part (b): FAITHFUL — combined theorem is a genuine `indecomposable ⇒ positive root`, with the
  `B(d,d)=2` hypothesis of the standalone version genuinely discharged by a proved lemma.
- Part (c): FAITHFUL — "exactly one up to iso" split into genuine existence AND uniqueness.
- Non-vacuity: CONFIRMED — hypotheses jointly satisfiable, both `∀` parts over nonempty classes,
  existence half of (c) a real construction, all four declarations axiom-clean (no `sorryAx`).
- Docstrings: accurate; no drift from what is proved.
