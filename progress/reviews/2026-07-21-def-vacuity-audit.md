# Review: whole-tree def-body-sorry & `True`-placeholder vacuity audit

**Issue:** #7094
**Date:** 2026-07-21 (UTC)
**Type:** read-and-report (no `.lean` edits)
**Invariant under test:** *Definitions must be constructed* — no `def` /
`noncomputable def` / `instance` / `abbrev` may carry a `sorry` in its **body**
(a sorry'd definition means the object does not exist, silently making every
downstream theorem vacuous), and no proposition may be stated as `True` (which
hides the real requirement).

---

## Verdict (up front)

**The codebase upholds the "definitions must be constructed" invariant
tree-wide.** Zero defects found.

- **0** `sorry` tokens in any `def` / `noncomputable def` / `instance` /
  `abbrev` body, `where`-clause data position, or structure-field value.
- The tree contains **exactly 1** genuine `sorry` in total, and it sits in a
  `theorem` body (a proof obligation, allowed) — `finrank_g_three`, owned by the
  claimed feature issue #7084.
- **0** propositions stated as `True` / `= True` / `↔ True` placeholders; the 3
  incidental `True` tokens in code are all legitimate.
- The 20+ most-referenced central definitions (representations, characters, the
  Schur/Specht/Young family) are all genuine constructed objects, not stubs.

No follow-up `feature` or `blocked` issue is required.

---

## Method

Naive `grep -rn sorry` matches **170** lines across 100 files — almost all of
these are prose ("sorry-free", proof-strategy notes) inside `/- … -/` and `--`
comments. A naive grep therefore cannot answer this question. I used an
**authoritative comment-stripped depth-counter** (`/tmp/sorry_audit.py`) that:

1. Strips Lean **nested** block comments `/- … -/` (tracking depth) and `--`
   line comments, replacing them with spaces so line numbers are preserved, and
   skips string literals.
2. Matches `sorry` as a standalone token (`(?<![\w.])sorry(?![\w])`, so
   `sorryAx`, `mysorry`, and `Sorry` do not match).
3. For every hit, walks backward to the nearest enclosing declaration keyword
   (`def` / `instance` / `abbrev` / `theorem` / `lemma` / `example` /
   `structure` / `inductive` / `class`) and reports the decl kind.

Scope: every `*.lean` under `EtingofRepresentationTheory/` **plus** the root
aggregator `EtingofRepresentationTheory.lean` (the only build-relevant `.lean`
outside the tree; it has 0 sorries). No `.lake/` dependency files.

This audit is **static** (read-only), matching the read-and-report mandate. A
`lake build` would not add signal here: a vacuous definition compiles fine, so
building cannot detect def-body vacuity — the static sorry-in-def-body check is
the decisive test.

---

## Deliverable 1 — sorry-in-definition-body sweep

**Result: exactly 1 genuine `sorry` tree-wide, and it is a proof obligation.**

```
TOTAL comment-stripped sorry tokens: 1

EtingofRepresentationTheory/Chapter2/Problem2_16_3.lean:1051
    enclosing decl: theorem finrank_g_three (@ line 1050)
    sorry line: sorry
```

Context (`Problem2_16_3.lean:1050-1051`):

```lean
/-- **(a)** `𝔤₃` is finite dimensional of dimension `6` (type `G₂` positive part). -/
theorem finrank_g_three (k : Type*) [Field k] : Module.finrank k (g k 3) = 6 :=
  sorry
```

**Classification: ALLOWED.** The sorry discharges the *proof* of a `theorem`
(`finrank_g_three` states an equation `Module.finrank k (g k 3) = 6`). It is a
normal proof deferral, not data. It is owned by the claimed feature issue #7084
(Problem 2.16.3(a), G₂ positive-nilpotent dimension = 6). No downstream `def`
depends on it for its existence.

**Cross-checks (all clean):**

- Per-file comment-stripped scan of all 100 naive-hit files: only
  `Problem2_16_3.lean` has a non-zero count (= 1). Every other "sorry" match is
  comment/docstring prose.
- No `sorryAx` anywhere.
- No `admit` **tactic** — the 4 `admit` grep hits are all English prose
  ("admit a unitary structure", "admit a lift"), not the tactic.
- No `:= by admit`, `:= admit`, or `by stop` in any definition body.
- Because the total genuine sorry count is **1** (a theorem), there can be **no**
  sorry in any `where`-clause data position, structure-field value, or
  `def`/`instance`/`abbrev` body anywhere in the tree — this is exhaustive, not
  a sample.

**Def-body / instance / abbrev genuine-sorry count: 0.** Invariant holds.

---

## Deliverable 2 — `True`-placeholder / vacuity spot-check

### 2a. `True` token scan (comment-stripped, whole tree)

Only **3** `True` tokens appear in code; **none** is a proposition stated as a
placeholder or a `def` returning `True`/`trivial`:

| Location | Use | Verdict |
|---|---|---|
| `Chapter5/ExteriorIrreducible.lean:178` | `(fun _ _ => True)` passed as the **total connectivity relation** argument to `DiagonalCoordinate.eq_bot_or_eq_top_of_connected`, with a real `Relation.ReflTransGen` witness | **legitimate** — a genuine mathematical argument (the total relation is trivially connected), not a masked requirement |
| `Chapter6/DynkinTypes.lean:341` | `simp only [show (i < m + 4) = True from by simp; omega, dite_true]` | **legitimate** — rewrites a decidable prop to `True` to fire `dite_true` inside a tactic proof |
| `Chapter6/DynkinTypes.lean:565` | `show (i < m + 1) = True from by simp; omega` | **legitimate** — same `dite_true` rewrite pattern |

No `: True`, `= True`, or `↔ True` appears as a **theorem statement** or **def
return type**. No `def` returns `True`/`trivial` as a stand-in for a real Prop.

### 2b. `Classical.choice` / `default` in definition bodies

Scanned for `default` / `Classical.choice` / `Classical.arbitrary` in code (a
def defined via arbitrary choice of a *possibly-empty* type would be vacuous).
All hits are backed by a **proved** `Nonempty` / `Unique` / `Subsingleton`
instance, so each yields a real object:

- `Chapter5/AlgIrrepDualPairing.lean:121,129` — `algIrrepGLDualIso` draws
  `Classical.choice (algIrrepGLDual_iso_linearDual n lam k)`. The source
  `algIrrepGLDual_iso_linearDual` is a **theorem** (sorry-free per the sweep),
  so the `Nonempty (iso)` is genuinely discharged. The def's own docstring
  documents this: *"Real data: the `Nonempty` is discharged, not sorried."*
- `Chapter5/SchurWeylPartition.lean` (multiple), `Chapter5/Theorem5_4_3.lean:98`
  (`Sylow` default), `Chapter6/Corollary6_8_4.lean:398`,
  `Chapter6/CoxeterInfrastructure.lean:1340`, `Chapter9/Theorem9_2_1.lean:2446`
  — all pick the element of a proved `Unique`/`Subsingleton` type or
  `Classical.choice` of a proved `Nonempty`. Legitimate.

### 2c. Central-definition sample (~20 load-bearing objects)

Sampled the most cross-referenced definitions (centrality by file-reference
count: `formalCharacter` 35, `SpechtModule` 33, `YoungSymmetrizer` 27,
`SchurModule`/`schurModule` 25, `spechtModuleCharacter` 12) and read each body.
**Every one constructs genuine mathematical content — no `⊤`/`⊥`/`0`/`trivial`
stubs, no `sorry`, no trivial structure fields.**

**Schur / Specht / Young family** (the foundation):
- `YoungSymmetrizer` (`Chapter5/Definition5_12_1.lean:129`) =
  `ColumnAntisymmetrizer * RowSymmetrizer`, both explicit group-algebra sums.
- `YoungSymmetrizerK` / `YoungSymmetrizerZ` (`Theorem5_22_1.lean:50,62`) —
  explicit sign-weighted sum-of-products over general `k` / universal `ℤ`.
- `youngSymEndomorphism` (`Theorem5_22_1.lean:208`) — symmetrizer acting on the
  tensor power via `symGroupAlgHom`.
- `SpechtModule` / `SpechtModuleK` (`Theorem5_12_2_Irreducible.lean:26`,
  `Infrastructure/SpechtModuleSimple.lean:28`) — the left ideal
  `Submodule.span {YoungSymmetrizer …}`.
- `SchurModuleSubmodule` (`Theorem5_22_1.lean:282`) =
  `LinearMap.range (youngSymEndomorphism …)`.

**Representation constructions** (all carry proved `map_one'`/`map_mul'`/module
axioms — not `sorry`, not trivial):
- `glTensorRep` (`Theorem5_22_1.lean:218`) — diagonal `g ↦ g^{⊗n}` action.
- `schurModuleRep` (`Theorem5_22_1.lean:289`) — `glTensorRep` restricted to the
  GL-stable Schur submodule.
- `SchurModule` (`Theorem5_22_1.lean:321`) — `FDRep.of (schurModuleRep …)`.
- `spechtModuleAction` / `spechtModuleRep` / `spechtModuleFDRep`
  (`Theorem5_15_1.lean:76,96,109`) — left-multiplication operator bundle.
- `DualRepresentation` (`Chapter3/Definition3_3_2.lean:44`) — `abbrev` for
  `Module.Dual k V`; the substance is two real `Module Aᵐᵒᵖ` instances with all
  module axioms proved.
- `diagUnit` (`Theorem5_22_1.lean:329`) — torus embedding with proved inverse.

**Character definitions**:
- `formalCharacter` (`Theorem5_22_1.lean:495`, most-referenced) =
  `∑_μ (finrank M_μ) • monomial μ 1` over the finite weight-space support.
- `glWeightSpace` (`Theorem5_22_1.lean:349`) — genuine eigenspace intersection
  `⨅ i t, ker (M.ρ (diagUnit …) - t^{μ i} • id)`.
- `spechtModuleCharacter` / `…K` (`Theorem5_15_1.lean:85`,
  `SpechtCharacterGeneral.lean:48`) — `LinearMap.trace` of the action operator.
- `VirtualRepresentation` + `character` (`Definition5_7_1.lean:27,46`) — real
  structure (`coeffs`, `finite_support`, `support_simple`) and its virtual
  character sum.
- `classFunctions` / `IsClassFunction` (`Remark4_5_3.lean:97,92`) — the algebra
  center and the genuine class-function predicate.

**Note (not a defect):** `DualRepresentation` and `SymGroupAlgebra` are `abbrev`s
that unfold to `Module.Dual k V` and `MonoidAlgebra ℂ (Equiv.Perm (Fin n))`; the
mathematical content lives in the wrapped objects / accompanying instances, not
the abbrev. `Infrastructure/RegularCharacter.lean` and
`Infrastructure/FrobeniusCharacterBridge.lean` are theorem-only bridge files
(no `def`/`instance`/`abbrev`), so there is no data definition to audit there.

---

## Conclusion

As the repository approaches zero genuine sorries, this audit confirms the
apparent sorry count means what it appears to mean: the single remaining `sorry`
is a `theorem` proof obligation (#7084), and **no definition anywhere in the
tree is vacuous** — neither by a sorry'd body, nor by a `True`/`trivial`
placeholder, nor by choice from an unproved-nonempty type. The
"definitions must be constructed" invariant holds tree-wide. No inline edits and
no follow-up issue are needed.

### Reproduction

- Comment-stripped sorry sweep: `/tmp/sorry_audit.py` (in this session) — walks
  `EtingofRepresentationTheory/`, strips nested comments, reports each `sorry`
  with its enclosing decl kind. Output: 1 hit, a theorem.
- `True` scan: comment-strip each file, `grep '\bTrue\b'` — 3 hits, all
  incidental (table in §2a).
