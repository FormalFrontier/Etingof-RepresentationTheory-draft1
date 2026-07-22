# Coverage-arm audit: Problems 5.16.2 & 5.16.3 (content c(λ); E diagonalizable, rectangular-iff-scalar)

**Issue:** #7339 (Stage 3.7 coverage-arm audit)
**Date:** 2026-07-22
**Verdict:** both items `covered_full`. No fidelity gaps; no follow-up issues opened.

## Scope

Coupled pair, audited together because 5.16.3 is built directly on 5.16.2's
central element `C` via the bridge `E = C_n − C_{n−1}`:

- **5.16.2** (single claim): `C = ∑_{i<j}(ij)` acts on `V_λ` by the content `c(λ)`.
- **5.16.3(a)**: `E := (12)+…+(1n)` is diagonalizable with integer eigenvalues in `[1−n, n−1]`.
- **5.16.3(b)**: `E` acts by a scalar on `V_λ` iff `λ` is rectangular; the scalar is computed.

Read-only audit + `progress/items.json` bookkeeping. No Lean touched.

## Findings

Both Lean files are sorry-free (`rg -n sorry | rg -v sorry-free` → none) and
`lake build …Problem5_16_2 …Problem5_16_3` succeeds (exit 0). Fidelity was
already verified in prior audits (#7220 for 5.16.2, #7228→#7231 for 5.16.3);
this audit re-confirmed non-vacuity of each headline and assigned coverage.

### 5.16.2 — covered_full
`sumTranspositions_mul_eq_content_smul` (Problem5_16_2.lean:472): for every
`x ∈ SpechtModule n la`, `sumTranspositions n * x = (content la : ℂ) • x`.
- `content` (line 46) is the genuine `∑_{cells (r,c)} (c − r)` over
  `la.toYoungDiagram.cells` — matches book `∑_j∑_{i=1}^{λ_j}(i−j)` with j=row, i=col.
- `sumTranspositions` (line 40) is genuinely `∑_{i<j} of(swap i j)`.
- Quantified over all of `V_λ`, faithfully rendering "C acts on V_λ by c(λ)".

### 5.16.3(a) — covered_full
`sumTranspositionsWith1_diagonalizable_integer_eigenvalues` (line 257) is a
conjunction: (i) an eigenbasis (genuine diagonalizability), AND (ii) every
eigenvalue `μ = m : ℤ` with `(1 − n) ≤ m ∧ m ≤ (n − 1)`. **The `[1−n, n−1]`
bound is actually asserted**, not merely "integer". Holds for arbitrary f.d. `ρ`.
The hint `E = C_n − C_{n−1}` is the exposed bridge `sumTranspositionsWith1_eq_sub`
(line 109); `sumTranspositionsWith1` (line 62) is genuinely `E = (12)+…+(1n)`.

### 5.16.3(b) — covered_full (both clauses)
- Biconditional: `sumTranspositionsWith1_acts_scalar_iff_rectangular` (line 868)
  is a genuine iff `(∃ c, ∀ x ∈ V_λ, E*x = c•x) ↔ IsRectangular la`, proved in
  both directions. `IsRectangular` (line 87) = `∃ r c, la.parts = replicate r c`.
- **Computed scalar**: `sumTranspositionsWith1_scalar_on_rectangular` (line 905)
  pins the scalar as `(c − r)` for `la.parts = replicate r c` (= content of the
  unique removable corner `(r−1, c−1)`). Not left abstract. Endpoint checks match
  part (a)'s bound: trivial `(n)` → `n−1`; sign `(1ⁿ)` → `1−n`.

## items.json changes

Added to both entries: `coverage` (roll-up = min over sub-parts = `covered_full`),
`coverage_arm: audited`, `lean_file`, `fidelity_decl`, `derived` (per-sub-part:
claim / description / source_span / coverage / lean_decl / reason), `last_updated`.
Diff localized (75 insertions, 2 deletions).
