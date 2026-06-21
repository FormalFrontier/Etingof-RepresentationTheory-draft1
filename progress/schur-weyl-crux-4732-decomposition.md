# Scoping: `schurWeyl_simples_formalCharacter_classification_core` (#4732)

Session decomposing the Tier-4 crux at
`Chapter5/SchurWeylSimplesClassification.lean:106`. The single residual `sorry`
(line 132) is the highest-weight classification: given the equivariant
decomposition `e : V^{⊗n} ≃ ⨁ᵢ Sᵢ ⊗ Lᵢ` with each `Lᵢ` a simple polynomial
`GL_N`-rep, pairwise non-isomorphic, produce an injective antitone-partition
assignment `lam` with `char(Lᵢ) = schurPoly N (lam i)`.

## Why it doesn't fit one session

The crux factors into two genuinely independent pieces, one of which is the same
deep gap that blocks `iso_of_formalCharacter_eq_schurPoly` (#4699):

### Piece α — SchurModule simplicity/character over general `k` (foundation)

`schurModule_isSimple` (`Chapter5/SchurModuleSimple.lean:316`) and its whole
helper chain (`schurModuleSubmodule_isSimple_centralizer` :255,
`schurBlock_imageSubmoduleB_isSimple` :167, `finrank_bound` :141,
`youngSymEndo_mem_restrictScalars` :149, and
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` in
`SchurWeylGLTransfer.lean:553`) are stated and proved **only over `ℂ`**.

But the crux is over a general `k : Field, IsAlgClosed, CharZero`, and the
*hypotheses* it consumes (from `glTensorRep_equivariant_schurWeyl_decomposition`,
`FormalCharacterIso.lean:753`) are over general `k`. To match an abstract `Lᵢ`
(simple over `k`) against a concrete `SchurModule k N λ`, the concrete side must
be known simple **over `k`**.

Good news: the underlying double-centralizer infrastructure is already
general-`k`:
- `Theorem5_18_4_centralizers` (`Theorem5_18_4.lean:268`) — `[Field k] [CharZero k]`.
- `Theorem5_18_4_semisimple` (:292) — same.
- `SchurModuleSubmodule k N lam`, `schurModuleRep k N lam` (`Theorem5_22_1.lean:282,289`) — general `[Field k]`.
- `SchurModuleSimple.lean` already opens `variable (k) [Field k] [IsAlgClosed k] [CharZero k]` (line 24); the first helper `schurModuleSubmodule_smul_mem_aux` is over `k`. The ℂ-pinning is an *unforced* specialization in the later theorems.

So α is a mostly-mechanical `ℂ → k` generalization, but it cascades through
several helpers (`YoungSymmetrizerK_sq_scalar`, `youngSymEndomorphism_sq_scalar`,
the rank-one block lemmas) — verify each is general-`k` or generalize it too.

### Piece β — completeness: every `Lᵢ ≅ SchurModule(λᵢ)` (the deep Tier-4 content)

This is the genuine highest-weight content, shared with #4699. Two viable routes:

1. **Isotypic matching + counting (avoids full highest-weight machinery).**
   - Each `SchurModule k N λ` (λ antitone, |λ|=n, ℓ(λ)≤N) is a simple GL-submodule
     of `V^{⊗n}` (it *is* `SchurModuleSubmodule k N lam ⊆ TensorPower k (Fin N→k) (∑λ)`,
     GL-stable because the Young symmetrizer lives in the `Sₙ`-group-algebra and
     commutes with the diagonal GL action). [needs α for simplicity]
   - By uniqueness of isotypic decomposition of the semisimple `V^{⊗n}` against
     the abstract `e`-decomposition, `SchurModule k N λ ≅ L_{φλ}` for a unique
     index `φλ`; `φ : P ↪ ι` is injective because distinct λ give distinct
     characters (`schurPoly_injective`) hence non-isomorphic SchurModules.
   - **Completeness** = `φ` surjective = `|ι| = |P|`, where `P = {λ antitone :
     |λ|=n, ℓ(λ)≤N}`. By the double-centralizer pairing (`Theorem5_18_4`), the
     number of distinct simple GL-types in `V^{⊗n}` equals the number of distinct
     simple `Sₙ`-types occurring, and the Specht modules occurring in
     `V^{⊗n} = (kᴺ)^{⊗n}` are exactly those with `ℓ(λ) ≤ N`, i.e. `|P|` of them.
     `φ` injective between finite sets of equal size ⟹ bijective ⟹ done.
   - Then `lam := φ⁻¹` (each `i = φλ` ↦ `λ`), giving `char(Lᵢ) = char(SchurModule λ)
     = schurPoly N λ` (`formalCharacter_schurModule_eq_schurPoly`,
     `formalCharacter_eq_of_rep_iso`).

2. **Highest-weight leading-monomial.** Each simple `Lᵢ` has a 1-dimensional
   highest weight space at a dominant `λᵢ`, and a symmetric character with leading
   term `m^{λᵢ}` (coeff 1) equals `schurPoly N λᵢ`. More infrastructure to build;
   route 1 reuses existing double-centralizer work and is preferred.

The hardest, most uncertain step is the **counting equality `|ι| = |P|`** (the
`Sₙ`-side: which Specht modules occur in `(kᴺ)^{⊗n}`). The β worker should expect
to decompose further around that step.

## Assembly (thin, lives in β)

Given α + the completeness bijection `φ : P ≃ ι`, define `lam i := (φ⁻¹ i)` and
discharge `Function.Injective lam` (φ⁻¹ injective) and the character equality.
Available glue: `formalCharacter_schurModule_eq_schurPoly`,
`formalCharacter_eq_of_rep_iso`, `schurPoly_injective`,
`SemisimpleIsotypic.submodule_of_directSum_simple_iso_directSum`
(`Chapter5/SemisimpleIsotypic.lean`).

## Decomposition

- **sub-α** (no in-set deps): generalize SchurModule simplicity off ℂ to general
  `k`, and expose `SchurModule k N λ` as a simple GL-submodule of `V^{⊗(∑λ)}`.
- **sub-β** (depends on α): close the crux via route 1 (isotypic matching +
  counting). May decompose further around the `|ι| = |P|` step.

Parent #4732 is skipped (→ `replan`) with a `Decomposed into #α, #β` breadcrumb.

---

## Update — post-investigation obstruction map (sub-α is a major sub-project)

A deeper read of the ℂ→k cascade for sub-α (#4820) revised the difficulty
sharply. The **top** layers' proof text uses no ℂ-specific API, but the cascade
bottoms out at **Specht-module character orthogonality**, which is genuinely
ℂ-rooted:

- `spechtModuleCharacter` (`Theorem5_15_1.lean:79`) `:= LinearMap.trace ℂ _ (spechtModuleAction …)` — **ℂ-valued by definition**, via an `FDRep ℂ (Perm (Fin n))` bridge that uses Mathlib's `FDRep.char_orthonormal` (complex character inner-product orthonormality — ℂ-specific).
- `SymGroupAlgebra n := MonoidAlgebra ℂ (Perm (Fin n))` (`Theorem5_12_2_Irreducible.lean:22`) — **ℂ-based**.
- The orthogonality heart: `trace_mulLeft_youngSym_eq'` (`Theorem5_22_1.lean:2176`), `mulLeft_youngSym_zero_of_ne'` (:2120), `sum_coeff_char_eq_trace'` (:2093), `youngSym_trace_kronecker'` (:2205), and the casts `youngSymmetrizerK_complex_eq` (:2263), `youngSym_coeff_cast'` (:2040), `youngSym_sq_ℂ'` (:2047) — all `private`, all over ℂ.

By contrast, the **framework** lemmas are *already general-`k`* and need no work:
`trace_youngSymEndomorphism_restrict_eq_sum` (:793, `{k}[Field k]`),
`youngSymEndomorphism_restrict_sq_scalar` (:836, `{k}[Field k]`),
`isIdempotentElem_eq_zero_of_trace_eq_zero` (:2244, `{K}[Field K][CharZero K]`),
`YoungSymmetrizerK_sq_scalar(_ne_zero)` (over ℚ), and the GL transfer
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
(`SchurWeylGLTransfer.lean:553`, general `k`).

So sub-α's real content = **generalize Specht-module character theory and its
orthogonality off ℂ to a general algebraically-closed char-0 field**, replacing
the Mathlib `FDRep.char_orthonormal` (complex inner-product) route with a
field-agnostic one. That is a major sub-project, not a one-session feature.

### Strategic consequence — prefer base change for sub-β, drop sub-α

A **descent from ℂ** likely closes the #4732 crux without generalizing Specht
character theory at all:

- `formalCharacter k N M : MvPolynomial (Fin N) ℚ` is **field-independent data** —
  it records `finrank` of `ℕ`-weight spaces, and for `V^{⊗n}` / `glTensorRep`
  (constructions defined over ℚ) those dimensions are combinatorial, the same for
  every alg-closed char-0 `k`.
- The crux's conclusion (`∃ lam, injective ∧ char(L i) = schurPoly N (lam i)`)
  is a statement about these ℚ-polynomials. Prove it over ℂ (where the Specht /
  SchurModule machinery already exists), then transfer to general `k` via
  base-change invariance of the weight-space dimensions / the decomposition's
  numerical content.
- This needs a base-change-invariance lemma for `formalCharacter` (and possibly
  for the multiplicities in `glTensorRep_equivariant_schurWeyl_decomposition`),
  but **not** SchurModule simplicity over `k`.

**Recommendation:** the planner should decide between (1) the major sub-project of
Specht-character-over-`k` (sub-α #4820 → #4821 route 1), or (2) the base-change
route in sub-β that drops sub-α. Route (2) looks substantially cheaper. Sub-α
(#4820) is skipped back to `replan` pending that decision.

