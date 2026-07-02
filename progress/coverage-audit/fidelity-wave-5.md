# Stage 3.7 Fidelity Sweep — Wave 5 (Chapter 4 completion, Opus)

Closing pass for the Chapter 4 fidelity audit (issue #5341, epic #5338). Prior
waves (1–4, various models incl. Sonnet/Codex) had already adjudicated 22 of the
24 claim-bearing Chapter 4 items. This pass resolves the two residual items so
the whole chapter reaches `verified`/`gap`, judged with a different model (Opus)
than the original authors and calibrated on the confirmed examples #5322/#5323/#5326.

## Starting state (claim-bearing types: theorem/proposition/lemma/corollary/definition/example/remark)

24 items: 16 `verified`, 6 `gap` (issues #5632–#5636, #5656), 1 non-standard
`ok`, 1 `unchecked`.

## Resolved this wave

### Chapter4/Remark4.5.3 — `unchecked` → **verified**
`Etingof.Remark4_5_3.*` (`EtingofRepresentationTheory/Chapter4/Remark4_5_3.lean`).
Book Remark 4.5.3 defines characters à la Frobenius without mentioning
representations. Conjunct-by-conjunct against the blob:

- Convolution product `(f*g)(z) = Σ_{xy=z} f(x)g(y)` on `F(G,ℂ)`: `ConvolutionAlgebra`
  (= `MonoidAlgebra ℂ G`) + `convolution_apply` proving `(f*g)(z) = Σ_x f(x) g(x⁻¹z)`. ✓
- Associative algebra with unit `δ_e`: inherited from `MonoidAlgebra`; `one_eq_deltaE`
  pins the unit to `single e 1`. ✓
- Class functions `F_c(G,ℂ)` a commutative subalgebra: `classFunctions = Subalgebra.center`,
  `CommRing` instance, and `mem_classFunctions_iff` proving centre ↔ class function. ✓
- Renormalized characters = primitive idempotents (`f*f=f`, indecomposable):
  `IsPrimitiveIdempotent` matches the book's wording exactly; `renormChar` constructed;
  `renormChar_isPrimitiveIdempotent` proves it (via a genuine Schur absorption lemma). ✓
- Recovery formula `χ_i(g) = √(|G|/χ̃_i(1))·χ̃_i(g)`: `character_recovery` gives `∃ c,
  c² = |G|/χ̃_V(1) ∧ ∀g, χ_V(g) = c·χ̃_V(g)`. ✓

Anti-vacuity: the recovery existential is doubly constrained (`c²=…` *and* the
`∀g` character equation), not a free witness; the idempotency/primitivity theorems
assert real structure, not `Nonempty`/`rfl`. Not vacuous. Sorry-free (last sorry
discharged in #5392); `lake build` of the module succeeds (linter warnings only).
Note: items.json status was stale at `proof_partial` despite zero sorries —
corrected to `sorry_free`.

### Chapter4/Definition4.10.1 — non-standard `ok` → **verified**
`Etingof.FrobeniusDeterminant`. Flagged in wave 2 as a `gap` (issue #5620): the
Lean matrix used entries `x_{g·h⁻¹}` instead of the book's forward product
`x_{g_i g_j}`. That gap was repaired by merged PR #5675 — the current def is
`Matrix.det (Matrix.of fun (g h : G) => MvPolynomial.X (g * h))`, matching the
book's `a_{ij} = x_{g_i g_j}` on the nose. Faithful; normalized the fidelity
value from the non-schema `ok` to `verified` (retaining `fidelity_note` and
`fidelity_issue: 5620` for provenance).

## Repaired-gap re-audit (4 of the 6 gap issues had since merged fix PRs)

Four of the six gap issues were CLOSED with merged repair PRs, so leaving the items
as `gap` understated completion. Each was re-audited conjunct-by-conjunct (parallel
Opus judges, different model than the Sonnet authors) against its blob:

- **Example4.3_S3** (#5633, PR #5707) → **gap → verified.** Three `FDRep ℂ S3`
  genuinely constructed (trivial, sign, and the sum-zero standard rep); `stdRep_simple`
  proved via `FDRep.simple_iff_char_is_norm_one` from a real character computation
  (`χ(g)=#fix(g)−1`); `irreps_dim_sum_of_squares` tied to actual finranks. Faithful.
- **Example4.3_S4** (#5634, PR #5711) → **gap → verified.** Five `FDRep ℂ S4`
  constructed (trivial, sign, 2-dim partition pullback, 3-dim standard, 3-dim rotation
  = sign⊗standard); each proved `Simple` via character norm-one; the two 3-dim reps
  shown distinct via differing character on a transposition; sum-of-squares from real
  dims. Faithful.
- **Theorem4.1.1** (#5656, PR #5712) → **gap → verified.** `Theorem4_1_1_algebra_iso`
  now surfaces `k[G] ≃ₐ[k] Π i, Module.End k (V i)` with the `V i` simple, pairwise
  non-isomorphic, and complete, plus `|G| = Σ (dim V_i)²` tied to actual finranks —
  defeating the near-vacuity of the old sum-of-squares-only existential (which `d≡1`
  satisfies for any group). Faithful.
- **Example4.3_Q8** (#5632, PR #5708) → **stays gap** (new tracking issue **#5831**).
  The repair was *incomplete*: PR #5708 genuinely built the 2-dim Pauli rep (`rep`,
  quaternion relations, `rep_i/j/k`, `rep_neg_one`), but (1) proves no irreducibility
  (`Simple`) for any rep — unlike the S3/S4 siblings; (2) omits the four 1-dim
  pullback reps from Q₈/Z(Q₈)≅ℤ₂×ℤ₂; (3) leaves sum-of-squares as a bare `decide` not
  tied to finranks. Example 4.3 is titled *Irreducible* Representations; irreducibility
  is the dropped conjunct (Stage 3.2 step 7). Issue #5632 was closed prematurely; #5831
  now tracks the residual.

## Ending state

24 claim-bearing Chapter 4 items: **21 `verified`, 3 `gap`**. No `unchecked` remain —
the Chapter 4 worklist for #5341 is complete. The 3 remaining gaps carry open tracking
issues: **#5831** (Example4.3_Q8, residual after partial fix), **#5635** (Example4.8.1),
**#5636** (Example4.9.1).

## Takeaways

- The bulk of a per-chapter fidelity audit can be inherited from earlier waves;
  the closing pass is mostly reconciling residual/non-schema values and the last
  unchecked item. Worth checking for non-standard `fidelity` values (`ok`) — they
  read as "not yet normalized to verified/gap" and can hide a resolved gap.
- Stale `status` (here `proof_partial` on a sorry-free item) is a separate rot
  from `fidelity`; a fidelity pass is a good moment to reconcile it against an
  actual `lake build`.
- **Re-audit `gap` items whose repair issue has since closed with a merged PR** —
  they are the highest-yield targets in a closing pass. Here 4 of 6 had merged
  fixes: 3 were genuinely repaired (→ verified), but 1 (Q8 #5632/#5708) was closed
  *prematurely* — the fix added the object but silently dropped the irreducibility
  conjunct. A closed repair issue is not proof of faithfulness; re-run steps 6–7.
- **Cross-check sibling items formalized in one PR-batch against each other.** The
  three Example 4.3 repairs (Q8/S3/S4) were meant to be parallel, but only S3/S4
  proved `Simple`; the divergence (Q8 lacking it) was the tell that Q8's repair was
  incomplete.
