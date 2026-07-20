# Review — Ch5 Remark 5.2.8: cyclotomic / Frobenius-Galois integrality cluster

- **Issue:** #7014 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/3703a81d`
- **Target:** `EtingofRepresentationTheory/Chapter5/Remark5_2_8.lean` (582 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter5/Remark5.2.8.md`
- **Focus areas:** axiom cleanliness + statement fidelity / non-vacuity (report-only)
- **Overall verdict:** **SOUND.** All 15 headline declarations are axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no custom axiom); the file
  contains only `theorem`s (no `def`/`instance`/`abbrev`, so no data can be sorried); no
  conclusion is weakened to `True`; every statement is genuinely non-vacuous; and all five
  steps of the remark are formalized faithfully to the book. One docstring-only fix was made
  in passing (a stale "blocked infrastructure" phrase). Three non-blocking observations
  (the `χ(g)·χ(g⁻¹)` vs `|χ(g)|²` seam; strengthening of Step 4 to the full Galois group;
  four public lemmas unused by the capstone) are recorded below — none is a defect.

---

## 1. Axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter5.Remark5_2_8` (exit 0, no warnings on this file)
and ran `#print axioms` on every headline declaration listed in the issue plus the file's
public capstone. **Every** result is exactly `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, no stray custom axiom:

| Declaration | `#print axioms` result |
|---|---|
| `pow_coprime_bijective` | `[propext, Classical.choice, Quot.sound]` |
| `pow_eq_one_iff` | `[propext, Classical.choice, Quot.sound]` |
| `prod_ne_one_pow` | `[propext, Classical.choice, Quot.sound]` |
| `not_isIntegral_rat_mem_Ioo` | `[propext, Classical.choice, Quot.sound]` |
| `isIntegral_conj` | `[propext, Classical.choice, Quot.sound]` |
| `isIntegral_normSq_character` | `[propext, Classical.choice, Quot.sound]` |
| `isIntegral_prod_normSq_character` | `[propext, Classical.choice, Quot.sound]` |
| `character_eq_sum_rootsOfUnity` | `[propext, Classical.choice, Quot.sound]` |
| `pow_apply_of_mem_eigenspace` | `[propext, Classical.choice, Quot.sound]` |
| `eigenvalue_pow_eq_one` | `[propext, Classical.choice, Quot.sound]` |
| `trace_pow_eq_sum_eigenvalues` | `[propext, Classical.choice, Quot.sound]` |
| `character_ringHom_pow` | `[propext, Classical.choice, Quot.sound]` |
| `ringHom_prod_char_inv` | `[propext, Classical.choice, Quot.sound]` |
| `character_prod_rat` | `[propext, Classical.choice, Quot.sound]` |
| `beta_rat_not_mem_Ioo` | `[propext, Classical.choice, Quot.sound]` |

The file declares **no** `def`, `noncomputable def`, `instance`, or `abbrev` — every one of the
15 declarations is a `theorem`. There is therefore no data-carrying body that could be sorried;
the clean axiom set on the two final results (`character_prod_rat`, `beta_rat_not_mem_Ioo`) also
transitively certifies that the Mathlib constructions they lean on (`IsCyclotomicExtension`,
`IsGalois`, `IsPrimitiveRoot.autToPow`, `FDRep.character`, `integralClosure`) inject no `sorryAx`.

Comment-stripped `sorry` scan: **0** live `sorry`/`admit`/`stop` tokens; the only `sorry`
substrings remaining are the accurate "`sorry`-free" phrases in the exposition.

## 2. Fidelity to `blobs/Chapter5/Remark5.2.8.md`

The blob is the one-paragraph Remark 5.2.8: with `N = |G|` and `0 < j < N` coprime to `N`,
(1) `g ↦ gʲ` is a bijection `G → G`; (2) deduce `∏_{g≠1} |χ_V(gʲ)|² = β`; (3) `β ∈ K = ℚ(ζ)`,
`ζ = e^{2πi/N}`; (4) `β` is unchanged by `ζ ↦ ζʲ`; (5) deduce `β ∈ ℤ` and derive a contradiction.

| Book step | Lean statement | Verdict |
|---|---|---|
| (1) `g ↦ gʲ` bijective for `gcd(N,j)=1` | `pow_coprime_bijective` (line 88): `(Nat.card G).Coprime j → Function.Bijective (·^j)`; supported by `pow_eq_one_iff` (line 94) | **Faithful.** Direct restatement of `Nat.Coprime.pow_left_bijective`; coprimality genuinely consumed. |
| (2) `∏_{g≠1} f(gʲ) = ∏_{g≠1} f(g)` | `prod_ne_one_pow` (line 104): reindex the product over `univ.filter (·≠1)` along `g ↦ gʲ` | **Faithful.** Proved for a general `CommMonoid`-valued `f` via `Finset.prod_bij`; the `f g = |χ_V(g)|²` (resp. `χ_V(g)·χ_V(g⁻¹)`) instances give exactly the book's `β`-identity. `h : Coprime` is used through `pow_eq_one_iff`/bijectivity. |
| (3) `β ∈ K = ℚ(ζ_N)` (root-of-unity content) | `character_eq_sum_rootsOfUnity` (line 214): `∃ s : Multiset ℂ, (∀ μ ∈ s, μ^N = 1) ∧ χ_V(g) = s.sum`; lifted into `K` inside `character_prod_rat`'s `hmem` block (lines 464–509) | **Faithful.** Each `χ_V(g)` is the trace = sum of charpoly roots, each an `N`-th root of unity (`orderOf g ∣ N`); every such root lies in `K = ℚ⟮ζ⟯` (`hrootK`, line 458). Genuine `∃`, non-vacuous. |
| (4) `β` fixed by `ζ ↦ ζʲ` | `character_ringHom_pow` (line 345) / `ringHom_prod_char_inv` (line 374) as the ℂ-endomorphism form; `character_prod_rat`'s `hfix` (line 517) as the `K`-automorphism form | **Faithful (and strengthened, see Obs. 2).** `σ_j(χ_V(g)) = χ_V(gʲ)` proved by the eigenvalue/trace-power-sum computation (`trace_pow_eq_sum_eigenvalues`, line 306); reindexing via (2) gives `σ_j(β) = β`. |
| (3)+(4) ⟹ `β ∈ ℚ` | `character_prod_rat` (line 422): `∃ q : ℚ, algebraMap ℚ ℂ q = ∏_{g≠1} χ_V(g)·χ_V(g⁻¹)` | **Faithful.** `β_K ∈ K` fixed by all of `Gal(K/ℚ)` ⟹ in the base field, via `IsGalois.mem_range_algebraMap_iff_fixed` (line 536). Genuine existence of a rational value. |
| (5) `β ∈ ℤ`, contradiction | `not_isIntegral_rat_mem_Ioo` (line 135) + `isIntegral_prod_normSq_character` (line 180) + capstone `beta_rat_not_mem_Ioo` (line 569) | **Faithful.** A rational algebraic integer in `(0,1)` is impossible (`Etingof.Proposition5_2_5` + `omega`); `β` is an algebraic integer (product of `FDRep.character_isIntegral` values). The `0 < β < 1` bound is honestly imported as a hypothesis (it is Problem 5.2.7(b)'s deliverable, header lines 75–77). |

`FDRep.character g` is definitionally `LinearMap.trace ℂ V (V.ρ g)` (used as `rfl` at lines 359,
481) — the honest character, not a weakened stand-in. No hypothesis is over-strengthened: the
class assumptions (`[Group G] [Fintype G] [DecidableEq G]`) are the standard finite-group setup,
and coprimality / primitivity hypotheses are each genuinely consumed (checked per lemma above).

## 3. Non-vacuity spot checks

- `beta_rat_not_mem_Ioo` and `not_isIntegral_rat_mem_Ioo` are "derive `False` from hypotheses"
  theorems — this is the remark's contradiction step, not a vacuous conclusion. Their hypotheses
  (`0 < q < 1` with `q` the value of `β`) are exactly the configuration the remark proves cannot
  occur; the statements are the honest content, not `True`-in-disguise.
- `character_prod_rat` / `character_eq_sum_rootsOfUnity` are genuine `∃` claims about specific
  complex numbers (`β`, each `χ_V(g)`); non-trivial for `|G| > 1` and correct in the `|G| = 1`
  edge case (empty product `= 1`, `q = 1`).
- `trace_pow_eq_sum_eigenvalues` takes `hfin : {μ | eigenspace f μ ≠ ⊥}.Finite` as a hypothesis,
  but it is always satisfiable (finite dimension) and supplied at each call site via
  `Module.End.finite_hasEigenvalue` — not an unsatisfiable premise that would trivialize the lemma.
- `character_ringHom_pow` / `ringHom_prod_char_inv` quantify over a ring endomorphism `σ` with the
  root-of-unity powering property; such `σ` genuinely exist (a Galois automorphism of `ℚ(ζ_N)`
  extends to `ℂ`), so these are honest conditionals, not vacuously-satisfied hypotheses.

## 4. Docstring fix made in this PR (docstring-only)

Header line 153 read "The integrality half below needs none of the **blocked** infrastructure."
The cyclotomic-Galois half (`character_prod_rat`) is now fully proved sorry-free, so nothing is
"blocked". Rewrote to "The integrality half below is independent of the cyclotomic Galois argument
(Steps 3-4, `character_prod_rat`)." This is the only source change; it touches a `/-! … -/` block,
so `#print axioms` behaviour is provably identical (rebuild confirmed, exit 0). No other stale
status phrasing was found — lines 75–77 ("`0 < β < 1` … tracked under the parent issue") and the
"remaining half/content/input" narrative lines (198, 255, 551) accurately describe the
mathematical structure, not sorry-status.

## 5. Observations (non-blocking, no follow-up filed)

1. **`χ(g)·χ(g⁻¹)` vs `|χ(g)|²` seam is not formally bridged.** The two final theorems
   (`character_prod_rat`, `beta_rat_not_mem_Ioo`) use the "honest polynomial form"
   `β = ∏_{g≠1} χ_V(g)·χ_V(g⁻¹)`, while `isIntegral_normSq_character` /
   `isIntegral_prod_normSq_character` use the modulus form `∏_{g≠1} Complex.normSq (χ_V(g))`.
   These are the same complex number because `χ_V(g⁻¹) = conj(χ_V(g))` for a finite-group character,
   but that identity is **not** proved in this file, so the two forms are never formally identified.
   Consequences: (a) the modulus-form integrality lemmas are correct but not consumed by the capstone
   (which re-derives integrality directly in polynomial form, lines 575–578); (b) to feed Problem
   5.2.7(b)'s `0 < β < 1` bound (about the real number `∏ |χ_V(g)|²`) into `beta_rat_not_mem_Ioo`,
   a caller would still need `∏ χ_V(g)·χ_V(g⁻¹) = ∏ |χ_V(g)|²`. The docstrings are honest about this
   ("the honest polynomial form of `∏ |χ_V(g)|²`"), so this is a documented seam, not a soundness
   defect — every theorem is true exactly as stated. A one-lemma follow-up proving
   `χ_V(g⁻¹) = conj(χ_V(g))` (readily available from `character_eq_sum_rootsOfUnity`, since `g⁻¹`
   has eigenvalues `μ⁻¹ = conj μ`) would close the seam if a downstream assembly of 5.2.7(b) ever
   needs it. Not filed, as nothing currently consumes this file.

2. **Step 4 is strengthened to the full Galois group (correctly).** The blob says `β` "does not
   change under the automorphism given by `ζ ↦ ζʲ`" (one automorphism, the specific coprime `j` from
   Step 1). `character_prod_rat` instead proves `β_K` fixed by **every** `φ ∈ Gal(K/ℚ)` (line 517)
   and concludes rationality from the fixed-field theorem. This is the mathematically necessary and
   standard rendering — invariance under a single automorphism does not by itself give rationality
   unless it generates the group — and it subsumes the book's statement (each `φ` acts as some
   `ζ ↦ ζʲ`, `j` coprime to `N`). A faithful strengthening, not a deviation.

3. **Four public lemmas are not on the capstone's proof path.** `character_ringHom_pow` and
   `ringHom_prod_char_inv` (the ℂ-endomorphism form of Step 4) and the two `normSq` integrality
   lemmas are not used by `character_prod_rat` / `beta_rat_not_mem_Ioo` (which use the `K`-automorphism
   form and re-derive integrality in polynomial form). They are correct, axiom-clean, and each mirrors
   an explicit step of the book's prose (the `σ_j` narrative; "`β` is a product of algebraic integers"),
   so they read as intentional exposition API rather than dead code. Grep confirms no other file in
   the project consumes any headline lemma from this file (it is a self-contained leaf, an alternative
   proof of 5.2.7(b)). Recorded for traceability; no removal recommended.

## Verification summary

- `#print axioms` quoted for all 15 headline/public declarations — every one exactly
  `[propext, Classical.choice, Quot.sound]` (§1).
- No `def`/`instance`/`abbrev` in the file ⟹ no data-body sorry is possible; comment-stripped
  `sorry` scan is empty (§1).
- Each of the five book steps mapped to its Lean statement with a fidelity verdict; all faithful,
  none weakened to `True`, hypotheses genuinely used (§2).
- Non-vacuity spot-checked on the contradiction lemmas, the existence lemmas, and the
  hypothesis-carrying `trace_pow_eq_sum_eigenvalues` / `character_ringHom_pow` (§3).
- One docstring-only fix (stale "blocked infrastructure" → accurate phrasing); rebuild exit 0 (§4).
- Three non-blocking observations recorded (§5); no `feature` follow-up filed — no fidelity or
  soundness defect found.
