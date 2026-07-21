# Statement-fidelity & non-vacuity audit — Problem 5.16.1 (branching rule for Sₙ ⊆ Sₙ₊₁)

**Issue:** #7203
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session b09c0287)
**Scope:** report-only fidelity + non-vacuity audit of
`Etingof.res_spechtModule_character` and `Etingof.ind_spechtModule_multiplicity`
in `EtingofRepresentationTheory/Chapter5/Problem5_16_1.lean`
**Verdict: FAITHFUL — axiom-clean, no defect. Nothing filed.**

The character-level rendering of (a) and the multiplicity-level rendering of (b)
are accepted as faithful equivalents of the book's module direct-sum
decompositions, per the char-0 justification below (irreducibility + pairwise
distinctness + completeness of `{V_λ}`).

## Sources compared

- **Book statement** (`blobs/Chapter5/Problem5.16.1.md`): for a Young diagram `μ`,
  with `A(μ)` = diagrams obtained by adding a square and `R(μ)` = diagrams obtained
  by removing a square,
  > (a) `Res_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ R(μ)} V_λ`.
  > (b) `Ind_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ A(μ)} V_λ`.
- **Lean statements** (`EtingofRepresentationTheory/Chapter5/Problem5_16_1.lean`):

```lean
-- (a) restriction, character form (line 501)
theorem res_spechtModule_character (n : ℕ) (μ : Nat.Partition (n + 1))
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter (n + 1) μ (permEmb n σ) =
      ∑ la ∈ removeSquare μ, spechtModuleCharacter n la σ

-- (b) induction, multiplicity form (line 535)
theorem ind_spechtModule_multiplicity (n : ℕ) (μ : Nat.Partition n)
    (la : Nat.Partition (n + 1)) :
    branchingPairing n (spechtModuleCharacter n μ)
        (fun σ => spechtModuleCharacter (n + 1) la (permEmb n σ)) =
      if μ.toYoungDiagram ≤ la.toYoungDiagram then 1 else 0
```

## Build and axioms (issue deliverable 1)

- `lake exe cache get` then
  `lake build EtingofRepresentationTheory.Chapter5.Problem5_16_1` —
  **Build completed successfully (8609 jobs).** Only one style-linter warning
  (`show`-vs-`change` at line 425); no errors.
- `#print axioms`:

```
'Etingof.res_spechtModule_character'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.ind_spechtModule_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

  Both are a subset of the permitted `[propext, Classical.choice, Quot.sound]`.
  **No `sorryAx`, no custom axiom** — both declarations are proof-complete.

## Fidelity of the underlying objects (not surrogates)

- **`spechtModuleCharacter n la σ`** (`Theorem5_15_1.lean:85`) is
  `LinearMap.trace ℂ _ (spechtModuleAction n la σ)` — the genuine character of the
  Specht module `V_λ` (trace of left multiplication by `σ` on `V_λ ⊆ ℂ[Sₙ]`), not a
  surrogate. ✓
- **`permEmb n`** (`Problem5_16_1.lean:49`) is
  `Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb`, the honest monoid embedding
  `Sₙ ↪ Sₙ₊₁` extending a permutation of `Fin n` by the identity on the last point
  (pointwise stabilizer of the top point). `fullCycleType_permEmb` (line 73) confirms
  it adds exactly one fixed point (one extra 1-cycle), so `χ_{V_μ}(permEmb σ)` is
  precisely the restricted character `(Res χ_{V_μ})(σ)`. ✓
- **`removeSquare μ`** (line 55) `= {λ : Nat.Partition n // λ.toYoungDiagram ≤
  μ.toYoungDiagram}`. For `μ ⊢ n+1` and `λ ⊢ n`, containment `λ ⊆ μ` with the size
  gap forced to `1` (`|μ| = |λ| + 1` automatically) means exactly one square is
  removed, and that square is necessarily a removable corner. So
  `removeSquare μ = R(μ)` faithfully. ✓
- **`addSquare μ`** (line 61) `= {λ : Nat.Partition (n+1) // μ.toYoungDiagram ≤
  λ.toYoungDiagram}`; dually `μ ⊆ λ` with `|λ| = |μ|+1` ⇔ one square added, so
  `addSquare μ = A(μ)`. (Used only through the `≤`-guard in (b); the `Finset` itself
  is not referenced by the (b) statement.) ✓
- **`branchingPairing n χ ψ`** (line 67) `= |Sₙ|⁻¹ ∑_σ χ(σ)·ψ(σ⁻¹)` is the genuine
  Frobenius-reciprocity inner product `⟨χ, ψ⟩_{Sₙ}` on class functions. ✓

## (a) Restriction — character form is a faithful rendering

`res_spechtModule_character` proves, for **every** `σ ∈ Sₙ` (`σ` is a free universally
quantified variable), the pointwise identity
`χ_{V_μ}(permEmb σ) = ∑_{λ ∈ R(μ)} χ_{V_λ}(σ)`, i.e. an equality of the full
`Sₙ`-characters `Res χ_{V_μ} = ∑_{λ ∈ R(μ)} χ_{V_λ}`.

Over `ℂ` (characteristic 0) a finite-dimensional `Sₙ`-representation is determined up
to isomorphism by its character, and the group algebra is semisimple, so equality of
characters is equivalent to the module isomorphism
`Res V_μ ≅ ⨁_{λ ∈ R(μ)} V_λ`. The two ingredients that make this equivalence exact are
both established in the project:
- each `V_λ` is **irreducible** (`Theorem5_12_2_irreducible`,
  `Theorem5_12_2_Irreducible.lean:206`), and
- distinct partitions give **non-isomorphic** modules
  (`spechtModuleCharacter_injective`, `Theorem5_15_1.lean:2341`, via
  `specht_char_inner`).

Hence the multiplicities on the right are unambiguous and the character identity
carries the exact content of the direct-sum decomposition. The explicit module
isomorphism `Res V_μ ≅ ⨁ V_λ` is **not** constructed as an object, but the character
identity is a faithful equivalent reformulation in char 0. **PASS.**

## (b) Induction — multiplicity form is a faithful rendering

`ind_spechtModule_multiplicity` proves, for **every** `λ ⊢ n+1`,
`⟨χ_{V_μ}, Res χ_{V_λ}⟩_{Sₙ} = [μ.toYoungDiagram ≤ λ.toYoungDiagram]`.
By Frobenius reciprocity the multiplicity of `V_λ` in `Ind V_μ` equals the
multiplicity of `V_μ` (irreducible) in `Res V_λ`, which is exactly this pairing.

The statement ranges over **all** `λ ⊢ n+1`. Since `{V_λ : λ ⊢ n+1}` is a complete
set of irreducibles of `Sₙ₊₁` (Ch. 5 classification) and `ℂ[Sₙ₊₁]` is semisimple,
knowing the multiplicity of every irreducible determines `Ind V_μ` up to isomorphism.
The multiplicities are the `0/1` indicator of `μ ⊆ λ`, i.e. of `λ ∈ A(μ)`, so
`Ind V_μ ≅ ⨁_{λ ∈ A(μ)} V_λ` — multiplicity-free and indexed exactly by `A(μ)`,
matching the book. The `≤`-guard `μ.toYoungDiagram ≤ λ.toYoungDiagram` with
`|λ| = |μ|+1` is precisely "add one square." As in (a), the induced module is
**characterised by multiplicities**, never built as an object; this is a faithful
equivalent in char 0. **PASS.**

## Non-vacuity (issue deliverable 3)

- The objects are all real (established above): the characters are genuine traces,
  `permEmb` is a genuine embedding, and `removeSquare`/`addSquare` are genuine
  containment filters — none is `True`/`0`/trivial. Both identities therefore have
  genuine content.
- **The `≤`/`if` guard genuinely discriminates** (both branches are reachable), so
  (b) is not vacuously constant:
  - *A `λ` giving pairing `1`:* take `μ ⊢ n`, `λ = μ` with one square added to a new
    or existing legal row; `μ ⊆ λ` holds ⟹ value `1`.
  - *A `λ` giving pairing `0`:* e.g. `n = 2`, `μ = (2)` (single row of length 2).
    `λ = (1,1,1) ⊢ 3` has `μ = (2) ⊄ (1,1,1)` (row 0 of `λ` has length `1 < 2`),
    so the guard is `false` ⟹ value `0`.
- **`R(μ)`/`A(μ)` genuinely have more than one element** in general (so the sum in
  (a) is a real sum, not a singleton): for `μ = (2,1) ⊢ 3`,
  `R((2,1)) = {(1,1), (2)}` (both `⊆ (2,1)`), a two-element sum; while for
  `μ = (3) ⊢ 3`, `R((3)) = {(2)}` only, since `(1,1) ⊄ (3)` — confirming the
  containment filter discriminates rather than admitting all partitions.

## Conclusion

`Etingof.res_spechtModule_character` and `Etingof.ind_spechtModule_multiplicity`
faithfully render Problem 5.16.1(a) and (b). The book's module direct-sum
decompositions are stated in character form (a) and multiplicity form (b); given that
the `V_λ` are irreducible, pairwise non-isomorphic, and complete over `ℂ`, these forms
are equivalent to the module `≅` in characteristic 0, and every constituent object
(`spechtModuleCharacter`, `permEmb`, `removeSquare`, `branchingPairing`) is genuine.
The one structural note — that neither `Res V_μ` nor `Ind V_μ` is built as an explicit
module object, only characterised by (multiplicities of) characters — is a faithful
equivalent reformulation, not a weakening, and is exactly the char-0 acceptance the
issue permits. Axiom set is clean (no `sorry`). **No defect found; nothing filed.**

Recommendation: set `Chapter5/Problem5.16.1` `fidelity: verified` in
`progress/items.json`.
