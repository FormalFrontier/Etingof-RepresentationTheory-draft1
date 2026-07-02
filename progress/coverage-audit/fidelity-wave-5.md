# Fidelity sweep — Wave 5 (Chapter 5 residual, issue #5342)

Judge: Opus 4.8 (distinct from the Sonnet/earlier authors of the items below).
Scope: the Chapter 5 claim-bearing worklist items whose `fidelity` field was
still missing or non-conforming (`ok` / `faithful` / `partial`) after waves 1–4.
Method: PLAN.md Stage 3.2 steps 6–7 — anti-vacuity decision test, then
conjunct-by-conjunct fidelity of the Lean statement against the book blob.

After this wave every Chapter 5 claim-bearing done item (68 total) is
`verified` (62) or `gap` (6). All six gaps carry a `fidelity_issue`.

## Verdicts

### Chapter5/Example5.1.3 — VERIFIED
Book: real/complex/quaternionic type classification for ℤ/nℤ, S₃, S₄, A₅, Q₈.
Lean (`Example5_1_3.lean`, code sorry-free; the one "sorry" token is docstring prose):
- `Example5_1_3_ZMod`: a 1-dim ℤ/nℤ character with a value ∉ {±1} is **not** real
  type (the "complex type" direction).
- `Example5_1_3_S3`, `_S4`, `_A5`: **every** simple ℂ[G]-module is of real type
  (universally quantified over simple modules — strong, faithful).
- `Example5_1_3_Q8`: **exhibits** a concrete 2-dimensional simple representation of
  quaternionic type (named `Q8.rho`, FS indicator −1 witnessed by the invariant
  skew form). Not an unconstrained existential — a concrete witness with the exact
  book property.
Anti-vacuity: passes (S-group statements are ∀ over simple modules; the Q₈
existential names a concrete rep with a concrete non-trivial property).
Note (not a gap): the ℤ/nℤ item captures only the complex-type direction (it does
not separately assert the trivial and sign reps are real type), and the Q₈ item
does not separately assert the 1-dim reps are real type. These are sub-claim
coverage matters already handled by the coverage arm; the formalized statements
are faithful, non-vacuous renderings of the example's substance. → **verified**.

### Chapter5/Remark5.2.8 — GAP (fidelity_issue #5654, open)
Book: the modified vanishing argument — for `0<j<N=|G|` coprime to `N`,
`g↦gʲ` is a bijection ⇒ `∏_{g≠1}|χ_V(gʲ)|²=β`; then `β∈K:=ℚ(ζ)`, invariant under
`ζ↦ζʲ`, hence an integer, giving a contradiction.
Lean (`Remark5_2_8.lean`, code sorry-free): Steps 1, 2, 5 and the
algebraic-integer / root-of-unity content are real theorems; Step 4's
representation-theoretic core (`character_ringHom_pow`, via `trace_pow_eq_sum_eigenvalues`)
landed under #5772. **Not yet assembled**: the field-theoretic half of Step 4
(`σ_j` from `Gal(ℚ(ζ_N)/ℚ)≅(ℤ/Nℤ)ˣ`, deducing `β∈ℚ`) and the final
`β∈ℤ ⇒ contradiction` capstone. Tracked by the **open** issue #5654
(`depends-on: #5772`). Status is honestly `proof_partial`. → **gap** (`fidelity_issue: 5654`).
Prior non-standard value `partial` normalized to `gap`.

### Chapter5/Remark5.8.3 — VERIFIED (was `ok`; #5652 resolved & closed)
Book: `dim(Ind_H^G V) = dim V · (G:H)`.
Lean `Remark5_8_3`: `finrank ℂ (IndV H.subtype ρ) = finrank ℂ V * H.index`
(finite index `H`, finite-dimensional `V`) — exact, non-vacuous equality. The
"determined by `{f(x_σ)}`" observation is `coindVEquivPi`. Missing-formalization
issue #5652 is closed; file is present and sorry-free. → **verified**.

### Chapter5/Theorem5.9.1 — VERIFIED (fidelity was unset)
Book Thm 5.9.1 (coset-representative form, no normalization):
`χ(g)=∑_{σ∈H\G : x_σ g x_σ⁻¹∈H} χ_V(x_σ g x_σ⁻¹)`.
Lean `Theorem5_9_1`: the **averaged** form
`χ(g)=(1/|H|)∑_{x∈G : xgx⁻¹∈H} χ_V(xgx⁻¹)` (code sorry-free; the module
docstring's "currently sorry" is stale). This is the book's own Remark 5.9.2
reformulation, mathematically **equivalent** to the coset form over ℂ (each right
coset contributes `|H|` equal terms, cancelled by `1/|H|`), and the file's
docstring is transparent about the substitution and its justification.
Anti-vacuity/fidelity: not vacuous, not *weaker* — an equivalent, documented
reformulation whose statement matches its own docstring. → **verified**.
Recorded caveat: Theorem 5.9.1 and Remark 5.9.2 collapse to the same Lean
statement, so the literal coset-representative equation of Thm 5.9.1 is not
separately formalized; the induced-character content is nonetheless faithful.

### Chapter5/Remark5.9.2 — VERIFIED (was `faithful`; #5653 resolved & closed)
Book: the averaged Frobenius formula
`χ(g)=(1/|H|)∑_{x∈G : xgx⁻¹∈H} χ_V(xgx⁻¹)` when `char k` coprime to `|H|`.
Lean `Remark_5_9_2`: exactly this over `ℂ` (characteristic 0, so the hypothesis
holds and `(|H|:ℂ)⁻¹` is a genuine inverse), defeq to `Theorem5_9_1`. Exact match.
→ **verified**.

### Chapter5/Proposition5.21.1 — VERIFIED (was `faithful`; #5615 resolved & closed)
Book: `∏_m (x₁^m+⋯+x_N^m)^{i_m} = ∑_{λ: ℓ(λ)≤N} χ_λ(C_i) S_λ(x)`, summing over
**all** partitions of `n` with `≤N` parts.
Lean `Proposition5_21_1`: `psumPart = ∑ lam : BoundedPartition N n, charValue • schurPoly`
— the index is `Finset.univ` over **all** bounded partitions, not an unconstrained
existential over "some finset". This is exactly the #5615 fix (canonical decl is
now the `univ` sum, not the weaker `∃ lams` form). Code sorry-free. → **verified**.

### Chapter5/Proposition5.22.2 — VERIFIED (fidelity was unset)
Book: `L_{λ+1^N} ≅ L_λ ⊗ ∧^N V`.
Lean `Proposition5_22_2`:
`Nonempty (SchurModule k N (λ+1) ≅ SchurModule k N λ ⊗ detRep k N)` (code sorry-free).
`detRep` is the 1-dim determinant representation `= ∧^N V` (top exterior power of
the standard N-dim rep), so the interpretation is faithful. `Nonempty (A ≅ B)` here
is a genuine isomorphism assertion between two specific Schur modules — false in
general for mismatched weights, hence non-vacuous. → **verified**.

### Chapter5/Remark5.23.3 — VERIFIED (was `ok`; #5729 resolved & closed)
Book: `𝔤𝔩(V)` results extend to `𝔰𝔩(V)`/`SL(V)`; on `SL` `L_λ≅L_{λ+1^m}`, so
irreps are parametrized by `λ₁≥⋯≥λ_N` up to a simultaneous constant shift;
(book-disavowed) every fin-dim `𝔰𝔩(V)`-rep is completely reducible and every
irreducible is some `L_λ`; `dim V=2` recovers `𝔰𝔩(2)`.
Lean (`Remark5_23_3.lean`, code sorry-free): `constShift` / `ShiftEquiv` /
`SLWeightParam` (= dominant weights modulo constant shift) capture the
parametrization-up-to-shift claim; `algIrrepGL_finrank_constShift` (`proof_wanted`)
records the dimension-level `L_λ≅L_{λ+c·1^N}`; `sl_finiteDimensional_completely_reducible`
(`proof_wanted`) records the **book-disavowed** complete-reducibility claim as
`proof_wanted` (no sorry, no axiom) — the correct rendering of "we will not do
this here". → **verified**.

## Outcome
- Chapter 5 fidelity worklist: 68/68 items now `verified` (62) or `gap` (6).
- New/normalized this wave: 7 → `verified`, 1 (`Remark5.2.8`) → `gap` (#5654).
- No new repair issues opened: the sole gap already has an open tracking issue
  (#5654); the four previously-flagged items (#5615, #5652, #5653, #5729) were
  re-audited against the *current* Lean, confirmed fixed, and closed.
