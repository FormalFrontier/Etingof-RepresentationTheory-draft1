# Statement-fidelity & non-vacuity audit — Theorem 5.4.3 (Burnside's p^a q^b solvability theorem)

**Issue:** #7116
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session dc783bda)
**Scope:** report-only fidelity + non-vacuity audit of `Etingof.Theorem5_4_3`
**Verdict: FAITHFUL — axiom-clean, no defect. Nothing filed.**

## Sources compared

- **Book statement** (`blobs/Chapter5/Theorem5.4.3.md`):
  > **Theorem 5.4.3** (Burnside). *Any group $G$ of order $p^a q^b$, where $p$ and
  > $q$ are primes and $a, b \geq 0$, is solvable.*
- **Book proof** (`blobs/Chapter5/Discussion_proof_of_Theorem5.4.3.md`): smallest
  counterexample $G$ is simple; by Theorem 5.4.6 it has no conjugacy class of
  order $p^k$ or $q^k$ ($k \geq 1$); the class equation then forces a nontrivial
  center, contradicting simplicity.
- **Lean statement** (`EtingofRepresentationTheory/Chapter5/Theorem5_4_3.lean:17`):

```lean
theorem Etingof.Theorem5_4_3
    (G : Type) [Group G] [Fintype G]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (a b : ℕ) (hord : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G
```

## Fidelity checks (per issue deliverable 1)

### Hypothesis is exactly "order = p^a·q^b with p, q prime", and a, b ≥ 0 admitted
- `hp : Nat.Prime p`, `hq : Nat.Prime q` — both primality hypotheses present, no
  more. ✓
- `hord : Fintype.card G = p ^ a * q ^ b` — the order equals `p^a * q^b` on the
  nose, no auxiliary factor or coprimality clause. ✓
- `a b : ℕ` are **arbitrary** naturals. Since `ℕ` includes `0`, the edge cases the
  book explicitly allows (`a, b ≥ 0`) are genuinely admitted, **not** excluded by
  a hidden positivity assumption:
  - `a = b = 0` ⟹ order `= 1`: handled by the `n ≤ 1` branch
    (`Subsingleton H`, `isSolvable_of_subsingleton`), lines 39–41.
  - `b = 0` (or `a = 0`) ⟹ a prime power order `p^a`: no branch special-cases
    it away; the general induction covers it (a `p`-group is nilpotent, hence
    solvable — obtained here through the center / normal-subgroup extension). ✓

### p and q not required distinct; conclusion is Mathlib's real solvability
- There is **no** `p ≠ q` hypothesis. The book says "where $p$ and $q$ are primes"
  without requiring distinctness, so the Lean statement matches (and if `p = q`
  the order is a prime power `p^{a+b}`, still correctly handled). ✓
- The conclusion is `IsSolvable G`, Mathlib's genuine solvability predicate
  (existence of a derived series reaching `⊥`), not a bespoke or weaker
  placeholder. Confirmed it is the standard `Mathlib` class — the proof discharges
  it via real infrastructure: `isSolvable_of_subsingleton`, `isSolvable_of_comm`,
  and `solvable_of_ker_le_range` for the normal-subgroup extension step. ✓

### No silent specialization of field/characteristic or of the group
- Burnside's theorem here is characteristic-free finite group theory; the statement
  carries **no** field, module, characteristic, or algebraic-closure hypothesis.
  (Representation theory over `ℂ` is used only *internally*, inside the proof of the
  dependency Theorem 5.4.6, and is invisible at the interface.) ✓
- `G` is an arbitrary `[Group G] [Fintype G]`; the only carried instances are
  `Group` and `Fintype`, exactly the abstract-finite-group setting of the book.
  `DecidableEq` is introduced locally inside the induction (`classical`/`intro`),
  not imposed on the caller. No stray hypothesis. ✓

### Minor observations (not defects)
- `G : Type` fixes the group to universe `Type 0` rather than a universe-polymorphic
  `{G : Type u}`. This is a standard, content-neutral formalization convention: every
  finite group is isomorphic to one in `Type`, so no generality relevant to the book
  is lost. Recorded for completeness, not a weakening.
- The Lean proof uses **direct strong induction on `|G|`** (find a proper nontrivial
  normal subgroup `N`; both `N` and `H/N` are solvable by the IH; conclude by the
  extension lemma) instead of the book's contrapositive "smallest counterexample is
  simple" phrasing. These are logically equivalent, and the Lean proof invokes the
  same key input the book uses — Theorem 5.4.6 (a conjugacy class of size `t^k`,
  `k ≥ 1`, forces a proper nontrivial normal subgroup), at line 240. The
  center-nontrivial / center-trivial case split mirrors the book's class-equation
  argument. Statement fidelity is unaffected.

### Dependency sanity (Theorem 5.4.6)
`Etingof.Theorem5_4_6` (`EtingofRepresentationTheory/Chapter5/Theorem5_4_6.lean:342`)
is a genuine theorem with a real proof (regular-character identity + Theorem 5.4.4 +
Proposition 5.2.5 algebraic-integer argument), signature returning
`∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤`. Not a `sorry` or placeholder, so the
appeal at line 240 is sound.

## Non-vacuity check (per issue deliverable 2)

- `lake build EtingofRepresentationTheory.Chapter5.Theorem5_4_3` — **Build completed
  successfully (8586 jobs).** (Only style/deprecation warnings: `push_neg`
  deprecated, one `show`-vs-`change` linter note. No errors.)
- `#print axioms Etingof.Theorem5_4_3`:

```
'Etingof.Theorem5_4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

  This is a subset of the permitted `[propext, Classical.choice, Quot.sound]`.
  **No `sorryAx`, no custom axiom** — the theorem is non-vacuous and proof-complete.
- `progress/items.json` marks `Chapter5/Theorem5.4.3` as `status: sorry_free`,
  `sorry_free: true`, `fidelity: verified` — consistent with the build/axiom result.

## Conclusion

`Etingof.Theorem5_4_3` is a **faithful** formalization of the book's Theorem 5.4.3:
the hypotheses are exactly "finite group of order `p^a·q^b`, `p, q` prime" with the
`a, b ≥ 0` edge cases genuinely admitted, `p` and `q` are not forced distinct, the
conclusion is Mathlib's real `IsSolvable`, and there is no hidden field/character/group
specialization. The axiom set is clean (no `sorry`). **No defect found; nothing filed.**
