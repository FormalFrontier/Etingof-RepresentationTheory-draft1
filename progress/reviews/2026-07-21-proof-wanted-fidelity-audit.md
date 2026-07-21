# Review: fidelity audit of the two book-disavowed `proof_wanted` statements

**Issue:** #7098
**Date (UTC):** 2026-07-21
**Type:** review / read-and-report (no `.lean` edits)
**Scope:** the entire *unproved* surface of the formalization besides the single
owned genuine sorry `finrank_g_three` (#7084): the two `proof_wanted`
declarations. Verifies that each faithfully transcribes the book's assertion and
is correctly recorded (no `sorry`, no `axiom`, no vacuous `theorem … : True`).

---

## Method

- Read each `proof_wanted` declaration, its module docstring, its decl docstring,
  and its blob (`blobs/Chapter2/Remark2.9.3.md`, `blobs/Chapter5/Remark5.23.3.md`).
- Re-ran the tree-wide sweep
  `grep -rn 'proof_wanted\|^axiom\|\badmit\b' EtingofRepresentationTheory/ --include=*.lean`
  and classified every hit.
- Built both modules to confirm the signatures elaborate (a `proof_wanted`
  still elaborates its *statement*, so a malformed one would fail to build):
  `lake build EtingofRepresentationTheory.Chapter2.Remark2_9_3
  EtingofRepresentationTheory.Chapter5.Remark5_23_3` → **Build completed
  successfully (8666 jobs)**, only unrelated style-linter warnings in
  `Proposition5_22_2.lean`, no errors.

---

## 1. `Etingof.ado` — Ado's theorem

**Location:** `EtingofRepresentationTheory/Chapter2/Remark2_9_3.lean:47`

```lean
variable (k : Type u) [Field k] [CharZero k]
variable (L : Type u) [LieRing L] [LieAlgebra k L]

proof_wanted ado [FiniteDimensional k L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ
```

**Book (blob `Remark2.9.3.md`):** "**Ado's theorem** says that any finite
dimensional Lie algebra is a Lie subalgebra of `𝔤𝔩(V)` for a suitable finite
dimensional vector space `V`."

**Fidelity verdict: FAITHFUL.**

- *Conclusion.* "Lie subalgebra of `𝔤𝔩(V)`" ⇔ an injective Lie-algebra
  homomorphism into `𝔤𝔩(V) = End(V)`. The Lean conclusion
  `∃ V, … ρ : L →ₗ⁅k⁆ Module.End k V, Function.Injective ρ` says exactly this:
  `L →ₗ⁅k⁆ Module.End k V` is a `k`-Lie-algebra hom into `End(V)` with its
  commutator bracket (the `LieRing.ofAssociativeRing` local instance realises
  `𝔤𝔩(V)`, matching the adjoint-representation idiom cited in the docstring),
  and `Injective ρ` is "subalgebra" (faithful representation). Correct
  direction, correct strength.
- *`V` unconstrained.* `V` is existentially quantified with `FiniteDimensional
  k V` as its only constraint — "for a suitable finite dimensional vector
  space", matching "suitable finite dimensional `V`". Not over-constrained.
- *`FiniteDimensional k L` hypothesis.* Matches "any **finite dimensional** Lie
  algebra". Present as an explicit hypothesis on the decl. Correct.
- *`CharZero k` hypothesis (the one addition over the bare blob sentence).* The
  blob states Ado's theorem unqualified, but the classical theorem named "Ado"
  holds precisely over characteristic-zero fields; the positive-characteristic
  analogue is Iwasawa's theorem, proved by different means. The module docstring
  (lines 20-21) states this scoping decision explicitly. Adding `CharZero`
  therefore (a) does not over-claim — it makes the recorded obligation *narrower*
  than a naive reading of the blob, not broader — and (b) records the
  mathematically correct content of "Ado's theorem" proper. This is a documented,
  defensible faithful scoping, not a fidelity defect.
- *Universe.* `V : Type u` shares `L`/`k`'s universe. Harmless: `V` is
  finite-dimensional, so no universe generality is lost.

**Recording:** genuine `proof_wanted` — no `sorry`, no `axiom`, no proof term,
not a `theorem … : True`. Signature elaborates (build green).

---

## 2. `Etingof.sl_finiteDimensional_completely_reducible` — complete reducibility of finite-dim `𝔰𝔩_N`-modules

**Location:** `EtingofRepresentationTheory/Chapter5/Remark5_23_3.lean:209`

```lean
proof_wanted sl_finiteDimensional_completely_reducible
    {n : ℕ} {k : Type*} [Field k] [CharZero k]
    {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule (SpecialLinear.sl (Fin n) k) M]
    [LieModule k (SpecialLinear.sl (Fin n) k) M]
    (N : LieSubmodule k (SpecialLinear.sl (Fin n) k) M) :
    ∃ N' : LieSubmodule k (SpecialLinear.sl (Fin n) k) M, IsCompl N N'
```

**Book (blob `Remark5.23.3.md`, second paragraph):** "In particular, one can show
that any finite dimensional representation of `𝔰𝔩(V)` is completely reducible and
any irreducible representation is of the form `L_λ` (we will not do this here)."

**Fidelity verdict: FAITHFUL (with a documented, accurate scoping caveat).**

- *Conclusion.* "Completely reducible" for a finite-dimensional module is
  standardly equivalent to "every submodule is a direct summand", i.e. every
  submodule has a complement. The Lean conclusion `∀ N, ∃ N', IsCompl N N'`
  encodes exactly that. This is the *same* formulation used for the proved
  `𝔰𝔩(2)` case: `Etingof.Sl2Irrep.complete_reducibility`
  (`Chapter2/Problem2_15_1_complete_reducibility.lean:411`) is
  `(N : LieSubmodule ℂ sl2 M) : ∃ N' : LieSubmodule ℂ sl2 M, IsCompl N N'`
  under the identical `FiniteDimensional` + `LieRingModule` + `LieModule`
  instance context. The docstring's "same form as the `𝔰𝔩(2)` case … to which
  this specializes for `N = 2`" is accurate.
- *`𝔰𝔩(V)` = `SpecialLinear.sl (Fin n) k`.* Mathlib's traceless-matrix Lie
  algebra, the same object realising `𝔰𝔩(2)` elsewhere in the tree
  (`LieAlgebra.SpecialLinear.sl (Fin 2) ℂ`). Correct object.
- *Hypotheses not over-/under-strong.* `[Field k] [CharZero k]` +
  `[FiniteDimensional k M]`. Weyl's complete-reducibility theorem holds for
  finite-dimensional modules over semisimple Lie algebras over any
  characteristic-zero field, so requiring only a char-zero field (rather than
  algebraically closed, as the surrounding Schur-Weyl chapter does) yields a
  *true* — and if anything slightly more general — obligation; it does not
  over-claim into falsity. For the degenerate `n ≤ 1` (where `𝔰𝔩_n = 0`) the
  statement reduces to "every `k`-subspace of a finite-dim space has a
  complement", which is true, so the family is non-vacuous and true for all `n`.
  Faithful.
- *Scoping caveat is accurate.* The book pairs complete reducibility with the
  companion "every irreducible is `L_λ`" (the highest-weight classification). The
  Lean statement deliberately records only the complete-reducibility half; the
  docstring (lines 44-45, 204-207) states explicitly that the companion
  classification is *not* stated because it would require an `𝔰𝔩_N`-action on the
  `L_λ` that the development does not build, and points at the honest parameter
  set `SLWeightParam N` (dominant weights up to simultaneous constant shift) that
  the same file *does* construct. This is an accurate, documented partial
  transcription: the recorded obligation is a true sub-claim of the book's
  sentence, and the omitted half is disclosed, not silently dropped.

**Recording:** genuine `proof_wanted` — no `sorry`, no `axiom`, no proof term,
not a `theorem … : True`. Signature elaborates (build green). The load-bearing
provable content of the remark (the constant-shift parametrization
`SLWeightParam`, and the dimension-shadow `theorem algIrrepGL_finrank_constShift`)
is proved in the same file as real `theorem`s, so the `proof_wanted` is confined
to precisely the piece the book disavows.

---

## 3. Recording correctness — tree-wide classification

Sweep: `grep -rn 'proof_wanted\|^axiom\|\badmit\b' EtingofRepresentationTheory/ --include=*.lean`

| file:line | token | classification |
|---|---|---|
| `Chapter2/Remark2_9_3.lean:23` | `axiom` | **prose** — docstring "no proof term, `sorry`, or axiom is introduced". Held harmless. |
| `Chapter2/Remark2_9_3.lean:25` | `axiom` | **prose** — continuation of same docstring sentence. Held harmless. |
| `Chapter2/Remark2_9_3.lean:46` | `proof_wanted` | **prose** — docstring "We record it via `proof_wanted`". (The real decl is line 47.) |
| `Chapter2/Remark2_9_3.lean:47` | `proof_wanted` | **REAL** — `proof_wanted ado …`. Audited §1. |
| `Chapter4/Remark4_6_4.lean:9,182` | `admit` | **prose** — English "admit a unitary structure". Held harmless. |
| `Chapter5/Problem5_12_5.lean:11` | `admit` | **prose** — English "admit a …". Held harmless. |
| `Chapter5/Remark5_23_3.lean:32` | `axiom` | **prose** — docstring "no `sorry`, no axiom". Held harmless. |
| `Chapter5/Remark5_23_3.lean:204` | `axiom`, `proof_wanted` | **prose** — docstring "recorded via `proof_wanted` — no `sorry`, no axiom". |
| `Chapter5/Remark5_23_3.lean:209` | `proof_wanted` | **REAL** — `proof_wanted sl_finiteDimensional_completely_reducible …`. Audited §2. |
| `Chapter8/Problem8_2_5.lean:46` | `admit` | **prose** — English "admit a *morphism of …*". Held harmless. |
| `Chapter8/Exercise8_2_9.lean:36` | `admit` | **prose** — English "admit a lift". Held harmless. |

**Real declarations: exactly two `proof_wanted`, zero `axiom`, zero `admit`.**
Every other hit is English prose inside a docstring or comment. This matches the
issue's expectation and the summarize snapshots.

---

## Verdict

**Both `proof_wanted` statements are faithful transcriptions of the book and are
correctly recorded.**

- `Etingof.ado` faithfully states Ado's theorem (faithful finite-dimensional
  representation of a finite-dimensional Lie algebra), correctly scoped to
  characteristic zero with that scoping documented.
- `Etingof.sl_finiteDimensional_completely_reducible` faithfully states the
  complete-reducibility half of Remark 5.23.3's disavowed sentence, in the same
  `IsCompl` form as the proved `𝔰𝔩(2)` case, with the deliberately-omitted
  highest-weight-classification companion accurately disclosed in the docstring.
- Both are genuine `proof_wanted` (no `sorry`, no `axiom`, no `admit`, no vacuous
  `: True`), and both signatures elaborate (build green).

**No fidelity defects found. No follow-up `feature` issue required.**

The unproved surface of the formalization is therefore fully accounted for and
faithful end-to-end:

> **1 owned genuine sorry** (`finrank_g_three`, #7084)
> **+ 2 faithful, book-disavowed `proof_wanted`** (`ado`;
>   `sl_finiteDimensional_completely_reducible`)
> **+ 0 axioms + 0 admits + 0 vacuous `: True` statements.**

Every downstream "proof-complete / not project debt" claim that rests on these
two `proof_wanted` being honest book transcriptions is verified.
