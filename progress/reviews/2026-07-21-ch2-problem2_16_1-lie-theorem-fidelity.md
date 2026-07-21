# Review — Ch2 Problem 2.16.1: Lie's theorem (solvable ⇒ irreducible reps are 1-dimensional)

- **Issue:** #7198 (review, report-only)
- **Reviewer session:** `/work` → `/review` worker, branch `agent/6315c354`
- **Target:** `EtingofRepresentationTheory/Chapter2/Problem2_16_1.lean` (59 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter2/Problem2.16.1.md`
- **Focus areas:** ground-field fidelity (`ℂ` fixed, no over-general `[IsAlgClosed]`/`[CharZero]`); irreducibility rendering (`IsSimpleOrder (LieSubmodule ℂ L V)` + `Nontrivial V`); solvability rendering (`LieAlgebra.IsSolvable` vs the book's `Kⁿ(𝔤) = 0` commutant series); `LieModule` = genuine `𝔤`-representation; conclusion `finrank ℂ V = 1`; non-vacuity; axiom cleanliness (report-only, no proof edits)
- **Overall verdict:** **FAITHFUL.** The single headline
  `Etingof.Problem2_16_1.finrank_eq_one_of_isSolvable` is axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`), non-vacuous, and faithfully
  renders Lie's theorem in its classical char-0 form. The ground field is `ℂ` throughout —
  **not** an over-general algebraically-closed/char-0 field that would prove a different
  theorem. `IsSimpleOrder (LieSubmodule ℂ L V)` is the genuine "only subrepresentations are
  `0` and `V`, and `V ≠ 0`" irreducibility condition; the extra `[Nontrivial V]` is
  **implied** by `IsSimpleOrder` (so it is redundant, not an extra restrictive hypothesis
  that weakens the claim). `LieAlgebra.IsSolvable` is Mathlib's derived-series definition,
  which is exactly the book's commutant-series `Kⁿ(𝔤) = 0`. The `LieRingModule` + `LieModule`
  pair is the genuine Lie action, and `finrank ℂ V = 1` faithfully renders "`V` is
  1-dimensional." **No follow-up issue filed.** `progress/items.json` updated: `fidelity:
  verified`.

---

## 0. Build and axiom-cleanliness audit

`lake exe cache get` (cache hit, no downloads) then
`lake build EtingofRepresentationTheory.Chapter2.Problem2_16_1` — **exit 0, 8580 jobs**
(Mathlib cached). `#print axioms` via a scratch importer on the single public declaration:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.Problem2_16_1.finrank_eq_one_of_isSolvable` | 34 | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no custom axiom. `grep` for `sorry|admit|proof_wanted` over the file returns
nothing. The only intermediate object built in the proof is the `LieSubmodule` `N` (the line
`ℂ ∙ v`), which is a real `LieSubmodule` value with a genuine `lie_mem` proof — no sorried
data. The proof wraps the upstream Mathlib theorem
`LieModule.exists_nontrivial_weightSpace_of_isSolvable`, which is itself sorry-free.

---

## 1. Book statement and the Lean rendering

**Book (Problem 2.16.1, verbatim):** *The **commutant** `K(𝔤)` of a Lie algebra `𝔤` is the
linear span of elements `[x, y]`. … A finite dimensional Lie algebra `𝔤` over a field `k` is
said to be **solvable** if there exists `n` such that `Kⁿ(𝔤) = 0`. Prove the Lie theorem: if
`k = ℂ` and `V` is a finite dimensional irreducible representation of a solvable Lie algebra
`𝔤`, then `V` is 1-dimensional.*

**Lean:**
```lean
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

theorem finrank_eq_one_of_isSolvable [LieAlgebra.IsSolvable L]
    [FiniteDimensional ℂ V] [Nontrivial V] (hirr : IsSimpleOrder (LieSubmodule ℂ L V)) :
    finrank ℂ V = 1
```

The book's implication `(𝔤 solvable, V fin-dim irreducible) ⇒ dim V = 1` maps hypothesis-for-
hypothesis onto the Lean statement. Each conjunct is adjudicated below.

---

## 2. Ground field: `ℂ` fixed, not over-generalized — FAITHFUL

The book explicitly restricts to `k = ℂ` (Lie's theorem is false in positive characteristic —
see the sibling Problem 2.16.2 counterexample). The Lean fixes `ℂ` **literally** in every
carrier typeclass: `LieAlgebra ℂ L`, `Module ℂ V`, `LieModule ℂ L V`, `LieSubmodule ℂ L V`,
`finrank ℂ V`. There is **no** `[IsAlgClosed k]`/`[CharZero k]` abstraction that would state a
strictly stronger (hence different) theorem, and no weakening. The two properties of `ℂ`
actually consumed by the proof — `CharZero ℂ` and triangularizability (`IsTriangularizable ℂ L
V`, an instance available because `ℂ` is algebraically closed) — are discharged *as instances*
for the concrete field `ℂ`; they are **not** hypotheses of the theorem statement, so the
statement's hypothesis surface is exactly the book's. **FAITHFUL.**

---

## 3. Irreducibility: `IsSimpleOrder (LieSubmodule ℂ L V)` + `Nontrivial V` — FAITHFUL

"Irreducible representation" = the representation is nonzero and its only subrepresentations
are `0` and `V`. The lattice of subrepresentations of the `𝔤`-module `V` is exactly
`LieSubmodule ℂ L V` (`L`-invariant `ℂ`-submodules). `IsSimpleOrder (LieSubmodule ℂ L V)`
asserts this lattice has **exactly** two elements `⊥ ≠ ⊤`, i.e. the only subrepresentations
are `0` and `V` and they are distinct — precisely irreducibility. This is a genuine order-
theoretic condition on the actual submodule lattice, not a surrogate.

`IsSimpleOrder` extends `Nontrivial` of the order (`⊥ ≠ ⊤`), and for `LieSubmodule ℂ L V`,
`⊥ = ⊤` holds iff `V = 0`. Hence `IsSimpleOrder (LieSubmodule ℂ L V)` **already implies**
`Nontrivial V`. The separately-listed `[Nontrivial V]` instance argument is therefore
**redundant**, not an added restriction: it does not shrink the class of models beyond what
irreducibility already forces, and "`V` is nonzero" is part of the definition of an
irreducible representation. So `[Nontrivial V]` is a faithful (indeed automatic) rendering of
the implicit non-vacuity of a representation, **not** a hidden extra hypothesis that changes
the claim. **FAITHFUL.**

---

## 4. Solvability and the module structure — FAITHFUL

**Solvable:** the book defines solvable by `Kⁿ(𝔤) = 0` for some `n`, where `K(𝔤) = span{[x,y]}`
is the commutant (derived subalgebra). Mathlib's `LieAlgebra.IsSolvable L` is
`∃ k, LieAlgebra.derivedSeries ℤ L k = ⊥`, and `derivedSeries` is defined by iterating the
derived ideal `⁅L, L⁆` (the linear span of brackets) — i.e. `derivedSeries … k = Kᵏ(𝔤)`. The
base ring on the derived series is a normalization detail (the derived ideal of a Lie ring is
the bracket span, independent of the coefficient ring); over `ℂ` it agrees with `K^k`. So
`LieAlgebra.IsSolvable L` is precisely the book's `Kⁿ(𝔤) = 0`. **FAITHFUL.**

**Representation:** a `𝔤`-representation is a Lie action of `L` on `V`, rendered by the pair
`[LieRingModule L V]` (the additive bracket action `⁅x, v⁆`) + `[LieModule ℂ L V]`
(`ℂ`-bilinearity/compatibility). This is Mathlib's genuine Lie-module structure — the same one
`LieSubmodule`, `weightSpace`, and `exists_nontrivial_weightSpace_of_isSolvable` are stated
against — not a weaker surrogate (e.g. a bare `Module` with no bracket). The proof's use of
`⁅x, v⁆ = χ x • v` (`mem_weightSpace`) exercises the actual Lie action. **FAITHFUL.**

**Conclusion:** `finrank ℂ V = 1` is the standard rendering of "`V` is 1-dimensional" over
`ℂ`. **FAITHFUL.**

---

## 5. Proof sanity (backs non-vacuity of the statement, not a proof audit)

The proof is the book's argument specialized through Mathlib's packaged Lie's theorem: obtain
a common eigenvector `v ≠ 0` with weight `χ` (`⁅x, v⁆ = χ x • v` for all `x`), form the
`L`-invariant line `ℂ ∙ v` as a `LieSubmodule` `N` (invariance is exactly `χ`-scaling), note
`N ≠ ⊥` since `v ∈ N` and `v ≠ 0`, and use `IsSimpleOrder` to force `N = ⊤`; then
`finrank ℂ V = finrank ℂ (ℂ ∙ v) = 1`. This confirms the hypotheses genuinely drive the stated
conclusion (no vacuous discharge).

---

## 6. Non-vacuity — CONFIRMED

The hypothesis bundle `IsSolvable L`, `FiniteDimensional ℂ V`, `Nontrivial V`,
`IsSimpleOrder (LieSubmodule ℂ L V)` is simultaneously satisfiable. Concrete witness: take any
1-dimensional `ℂ`-vector space `V = ℂ` and any solvable `L` (e.g. the abelian 1-dim Lie
algebra `ℂ`, or even `L = 0`) acting on `V` (the trivial action `⁅x, v⁆ = 0` works). Then:

- `IsSolvable L` holds (abelian ⇒ `K(𝔤) = 0`, so `K¹ = 0`).
- `FiniteDimensional ℂ V` and `Nontrivial V` hold (`dim = 1`).
- `IsSimpleOrder (LieSubmodule ℂ L V)`: the `ℂ`-subspaces of a 1-dimensional space are exactly
  `0` and `V`, both automatically `L`-invariant, so the `LieSubmodule` lattice is exactly
  `{⊥, ⊤}` with `⊥ ≠ ⊤`.

The conclusion `finrank ℂ V = 1` is consistent with this witness, so the theorem is **not
vacuously true**, and `IsSimpleOrder (LieSubmodule ℂ L V)` is inhabitable alongside
`IsSolvable L` and `Nontrivial V`. **CONFIRMED.**

---

## Verdict

**FAITHFUL** on all four adjudicated axes (field, irreducibility, solvability + module
structure, conclusion) and **non-vacuous**. The single headline
`Etingof.Problem2_16_1.finrank_eq_one_of_isSolvable` is axiom-clean and faithfully renders the
book's Lie's theorem. No defect; **no follow-up issue filed.** `progress/items.json` set to
`fidelity: verified`.
