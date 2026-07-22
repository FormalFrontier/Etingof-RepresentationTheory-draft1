# Stage 3.7 fidelity audit — Chapter 5 Problem 5.16.3

**Issue:** #7228
**Item:** `Chapter5/Problem5.16.3`
**File:** `EtingofRepresentationTheory/Chapter5/Problem5_16_3.lean` (892 lines, sorry-free)
**Verdict:** **GAP** (part (b) "compute this scalar" sub-part not exposed)
**Follow-up:** #7231

## Book claim (blob `blobs/Chapter5/Problem5.16.3.md`)

(a) For any finite-dimensional rep `V` of `S_n`, `E := (12) + ⋯ + (1n)` is diagonalizable and has
integer eigenvalues on `V` between `1 − n` and `n − 1`. (Hint: `E = C_n − C_{n−1}`.)

(b) `E` acts on `V_λ` by a scalar **if and only if** `λ` is a rectangular Young diagram, **and
compute this scalar**.

## Per-check verdicts

### Check 1 — `sumTranspositionsWith1` is genuinely `E = (12)+⋯+(1n)`. VERIFIED.

`sumTranspositionsWith1 n = ∑_{0 < j} MonoidAlgebra.of ℂ … (Equiv.swap 0 j)` (lines 62–64). In the
0-indexed `Fin n` model the book's point `1` is index `0`, so `(1 j) ↦ swap 0 j` and the index set
`{j : 0 < j}` gives exactly the `n − 1` transpositions through the fixed point — not "all
transpositions" and not "through the wrong point". `sumTranspositionsWith1_eq_sub` (line 109)
confirms the book's hint identity `E = sumTranspositions n − sumTranspositionsStab n`
(`= C_n − C_{n−1}`), with `sumTranspositionsStab` the sum over `0 < i < j`. Genuine.

### Check 2 — Part (a) faithfulness. VERIFIED.

`sumTranspositionsWith1_diagonalizable_integer_eigenvalues` (lines 257–265) is a conjunction:
- (i) `∃ b : Module.Basis (Fin (finrank ℂ V)) ℂ V, ∀ i, ∃ μ, T (b i) = μ • b i` — a genuine basis
  of eigenvectors (diagonalizable, not merely triangularizable). Non-vacuous: it is a real
  `Module.Basis` obtained from the spectral theorem for the self-adjoint `T`.
- (ii) `∀ μ, HasEigenvalue T μ → ∃ m : ℤ, μ = m ∧ (1 − n) ≤ m ∧ m ≤ n − 1` — integer eigenvalues
  with the book's inclusive bounds `1 − n` and `n − 1` (direction and inclusivity match).
`ρ` ranges over an arbitrary finite-dimensional rep (`[Module.Finite ℂ V]`), not a fixed one.
Faithful.

### Check 3 — Part (b) "compute this scalar". **GAP.**

Headline `sumTranspositionsWith1_acts_scalar_iff_rectangular` (lines 862–865) states **only** the
iff:
```
(∃ c : ℂ, ∀ x ∈ SpechtModule n la, sumTranspositionsWith1 n * x = c • x) ↔ IsRectangular la
```
It never asserts the value of `c` for rectangular `λ`. A scan of every top-level declaration in the
file (the 29 defs/lemmas/theorems) confirms no auxiliary lemma exposes the scalar. The value is
present **only as an existential witness inside proof terms**:
- in the iff proof, the E-scalar witness is `content la − c` (lines 872, 883);
- in `content_const_removeSquare_iff_rectangular`'s backward branch, the stab-scalar witness is
  `content la − ((cval − 1) − (r − 1))` (line 835).
Simplifying, the E-scalar on a rectangular `λ` with `r` rows of length `c` is
`(c − 1) − (r − 1) = c − r` = the content of the unique removable corner `(r−1, c−1)`.

The book's part (b) has two deliverables — the iff criterion *and* the computed scalar. The second
is not rendered as any checkable statement. This is the "dropped 'compute' sub-part" failure mode
the sweep exists to catch, and is directly analogous to the confirmed gap #7204/#7211 (part (d)
classification proved-inside-but-not-exposed).

### Check 4 — `IsRectangular` faithfulness and non-vacuity. VERIFIED.

`IsRectangular la := ∃ r c : ℕ, la.parts = Multiset.replicate r c` (line 87). Because
`Nat.Partition` carries `parts_pos` and `parts_sum = n`, for `n ≥ 1` the witnesses are forced to
`r = #rows ≥ 1`, `c = row length ≥ 1`, `r·c = n` — a genuine rectangle (all rows equal length); the
empty partition (`n = 0`, excluded here by `NeZero n`) is vacuously covered by `r = 0`. Faithful.
`SpechtModule n la` is the genuine Specht module `ℂ[S_n]·c_λ`: the proof constructs the nonzero
element `⟨YoungSymmetrizer m ν, …⟩` (line 536) and uses `youngSymmetrizer_identity_coeff`, so the
scalar-action statement is not vacuous, and the fully-proved iff rules out a `⊥`/`⊤` degeneracy.

## Disposition

- `progress/items.json`: set `Chapter5/Problem5.16.3` `fidelity: gap`, added `fidelity_note` and
  `fidelity_issue: 7231`.
- `status` kept `sorry_free`: the two stated theorems are faithful and non-vacuous and the file is
  genuinely sorry-free; the gap is a *missing exposed result*, not a broken/weakened/vacuous
  statement. This mirrors the #7204 disposition for the identical failure mode (there `sorry_free`
  was likewise retained while a follow-up — #7211 — exposed the missing headline).
- Follow-up #7231 filed to expose `sumTranspositionsWith1_scalar_on_rectangular` (scalar `= c − r`),
  after which `fidelity` flips back to `verified`.
- No Lean source edits; `lake build` unaffected.
