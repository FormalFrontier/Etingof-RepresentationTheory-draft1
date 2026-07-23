# Fidelity audit: Chapter 2, Problem 2.16.4 — irreducible reps of `𝔰𝔩(2)` in characteristic `p > 2` (#7196)

> Historical audit snapshot. The declarations assessed below remain source-present,
> but the current `Sl2Irrep.lean` / `Problem2_16_4.lean` sources no longer pass a
> fresh check. Regression #7531 tracks restoring those partial endpoints. The
> separate full-classification reprise remains governed by `deferred-reprises.md`.

**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 0a63f2dd)
**Scope:** `EtingofRepresentationTheory/Chapter2/Problem2_16_4.lean` (1098 lines).
**Method:** book statement first (`blobs/Chapter2/Problem2.16.4.md` — a one-line
"classify" instruction; standard mathematical content summarized in the file
docstring), then statement-vs-book fidelity of each headline declaration, then the
central upper-bound adjudication, then non-vacuity, then build + axiom-cleanliness.
Mirrors the established confidence-phase pattern (e.g.
`2026-07-21-ch5-theorem5_26_1-artin-fidelity.md`).

## Overall verdict: **FAITHFUL** (dimension bound rendered in *both* directions; fine classification deferred, deferral documented and pre-accepted by the issue)

The book asks to "classify irreducible representations of `𝔰𝔩(2)` over an
algebraically closed field `k` of characteristic `p > 2`." The crisp, universally-true
content of that answer is the **dimension bound**: every finite-dimensional
irreducible `𝔰𝔩(2, k)`-representation has dimension `≤ p`, and this bound is achieved.
The file renders that dimension bound in **both** directions with genuine, sorry-free,
axiom-clean proofs:

- **Upper half** — `finrank_irreducible_le_char`: for *every* finite-dimensional
  irreducible `𝔰𝔩(2, k)`-module `M` (an abstract `M`, genuinely universally
  quantified), `finrank k M ≤ p`.
- **Lower / sharpness half** — `irrep_isIrreducible` + `irrep_finrank` +
  `exists_irreducible_dim_char`: a `d`-dimensional module `L(d) = Fin d → k` is
  constructed for every `d`, proved irreducible for `1 ≤ d ≤ p`, has `finrank = d`,
  and (at `d = p`) witnesses that the bound `≤ p` is attained (not merely `< p`).

The only deferred piece is the *fine classification* (parametrization of the
irreducibles by a highest weight `λ ∈ k`, with completeness / pairwise
non-isomorphism). The file docstring (lines 19–24) states this deferral explicitly
and honestly — it is not a hidden over-claim. Issue #7196 pre-authorizes exactly this
scoping: "set `fidelity` to `verified` only if the book's claim (as scoped by an
accepted deferral of the fine classification — the dimension bound in *both*
directions) is faithfully rendered." That condition is met.

**Correction to the issue's premise.** The issue body lists the headline
declarations and characterizes the file as (possibly) proving "only the *lower* half
(construct a `≤ p` family and prove those irreducible)", asking the reviewer to
"search for any universally-quantified 'for all irreducible `M`, `finrank ≤ p`'
statement." That statement **is present**: `finrank_irreducible_le_char`
(lines 664–670), which the issue's headline-decl list omitted. The gap condition of
deliverable 2 ("no upper bound over *all* irreps") is therefore **not** satisfied, so
this is not a `fidelity: gap`.

---

## Build & axioms

- `lake exe cache get` → cache present; `lake build
  EtingofRepresentationTheory.Chapter2.Problem2_16_4` → exit 0
  (`Build completed successfully (1992 jobs)`). Only benign
  `unusedSectionVars` linter warnings on three `SchurHelpers` lemmas
  (`eq_top_of_lie_closed`, `span_closed_of_gens`, `finrank_le_of_orbit_top`) where a
  section `variable` is not used; no errors, no `sorry`.
- `#print axioms` for every headline declaration →
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`. Checked:
  `rhoLieHom`, `irrep_isIrreducible`, `irrep_finrank`,
  `exists_irreducible_dim_char`, `lie_schur`, `finrank_irreducible_le_char`,
  `lie_sl2_h_e`, `lie_sl2_h_f`, `lie_sl2_e_f`.
- No literal `sorry` in the file. `noncomputable def`s
  (`sl2`, `sl2_e/f/h`, `rhoH/E/F`, `rhoLieHom`, the two module instances) all have
  real bodies — no def-body sorry.

---

## Statement fidelity

### The Lie algebra and its action are genuine

- `sl2 k := LieAlgebra.SpecialLinear.sl (Fin 2) k` — the honest `𝔰𝔩(2, k)`
  (traceless `2×2` matrices), not a surrogate. `sl2_traceless` confirms the
  `(1,1)`-entry is `-(0,0)`-entry.
- The representation `rhoLieHom k d : sl2 k →ₗ⁅k⁆ Module.End k (Fin d → k)` is a
  genuine **Lie algebra homomorphism**: `map_add'`, `map_smul'`, and crucially
  `map_lie'` are all proved (the last from the bracket relations
  `lie_rhoH_rhoE`, `lie_rhoH_rhoF`, `lie_rhoE_rhoF`). The module structure
  (`irrepLieRingModule`, `irrepLieModule`) is obtained by `compLieHom` on this real
  hom — the action is the true `𝔰𝔩(2)`-action, not a weaker stand-in.
- The `𝔰𝔩(2)` structure relations hold on the nose in the Lie algebra itself:
  `lie_sl2_h_e : ⁅h, e⁆ = 2·e`, `lie_sl2_h_f : ⁅h, f⁆ = -2·f`,
  `lie_sl2_e_f : ⁅e, f⁆ = h` (lines 528–560), each proved by direct matrix
  computation. `sl2_decomp` shows every element is `x₀₁·e + x₁₀·f + x₀₀·h`.

### "Irreducible" is the genuine condition

`LieModule.IsIrreducible k (sl2 k) M` unfolds (Mathlib
`Algebra/Lie/Semisimple/Defs.lean`) to `IsSimpleOrder (LieSubmodule k (sl2 k) M)` —
"a nontrivial Lie module whose only Lie submodules are `⊥` and `⊤`." This is the real
no-nontrivial-invariant-submodule condition (and `IsSimpleOrder` entails
`Nontrivial`, ruling out the zero module), not a dimension surrogate. The
irreducibility proof `irrep_isIrreducible` works directly with an arbitrary Lie
submodule `N ≠ ⊥` and shows `N = ⊤` by extracting one basis vector via the
`h`-eigenvalue separation and propagating with `e`/`f`.

### Upper bound — the central claim

`finrank_irreducible_le_char` (lines 664–670):

```
theorem finrank_irreducible_le_char [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p)
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (sl2 k) M]
    [LieModule k (sl2 k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (sl2 k) M] :
    Module.finrank k M ≤ p
```

This is the honest universally-quantified upper bound: `M` is an **arbitrary**
finite-dimensional irreducible `𝔰𝔩(2, k)`-module (not the constructed family). The
proof is the genuine mathematical argument sketched in the book / docstring: build
`E, F, H : End M` from the standard basis via `LieModule.toEnd`, establish the
operator relations `[H,E]=2E`, `[H,F]=-2F`, `[E,F]=H`, show `E^p` and `F^p` are
central (commute with `E, F, H` — the char-`p` collapse of the binomial coefficients),
hence scalars `α, β` by Schur's lemma (`lie_schur`), then split on `α = 0`
(nilpotent `E`, highest-weight vector, `F`-orbit) vs `α ≠ 0` (injective `E`, joint
`H`/`FE`-eigenvector, `E`-orbit); each orbit spans `M`, giving `finrank ≤ p`. The
`[IsAlgClosed k]` hypothesis is used exactly where the book uses it — to invoke
Schur's lemma (existence of an eigenvalue) — and is faithful, not a hidden weakening.

`lie_schur` is the genuine Schur's lemma for this action: a commuting `k`-endomorphism
of a finite-dimensional irreducible module over `[IsAlgClosed k]` is a scalar, proved
via eigenvalue existence + the eigenspace being a nonzero invariant submodule.

### Lower / sharpness half

- `irrep_isIrreducible (p) [CharP k p] (2 < p) (d) [NeZero d] (d ≤ p)`: the
  constructed `L(d) = Fin d → k` is irreducible when `1 ≤ d ≤ p`. The three
  char-`p` scalar facts (`natCast_inj_lt`, `natCast_ne_zero_of_lt`) are where `p > 2`
  and `d ≤ p` genuinely enter.
- `irrep_finrank (d) [NeZero d] : finrank k (Fin d → k) = d`.
- `exists_irreducible_dim_char [IsAlgClosed k] (p) [Fact p.Prime] [CharP k p] (2 < p)`:
  `¬ ∀ irreducible M, finrank M < p` — i.e. the bound `≤ p` is **attained**, witnessed
  by `L(p) = Fin p → k` (irreducible by `irrep_isIrreducible` at `d = p`, of dimension
  exactly `p`). Together with the upper bound this pins the maximum dimension to `p`.

---

## Non-vacuity

- **`irrep_isIrreducible`** — hypotheses `[Field k]`, `[CharP k p]`, `2 < p`,
  `[NeZero d]`, `d ≤ p` are simultaneously satisfiable: `k = 𝔽_3^alg` (an algebraic
  closure of `𝔽₃`), `p = 3`, `d ∈ {1,2,3}`. So the constructed irreducibles genuinely
  exist and the theorem is not vacuously true.
- **`finrank_irreducible_le_char`** — the universally-quantified upper bound is
  non-vacuous: the class of `M` satisfying its hypotheses is inhabited. Concretely,
  for `k = 𝔽_p^alg` and `M = Fin p → k`, `irrep_isIrreducible` supplies
  `LieModule.IsIrreducible`, `M` is finite-dimensional, and `Fact p.Prime`/`CharP`
  hold. The bound therefore constrains a real, non-empty family (and is sharp: that
  witness has `finrank = p`).
- **`exists_irreducible_dim_char`** — same witness family; its conclusion is a genuine
  negation (there really is an irreducible of dimension exactly `p`), not a vacuous
  `¬ False`.
- **`lie_schur`** — instantiated inside `finrank_irreducible_le_char` on `E^p`, `F^p`
  over the non-empty witness family; hypotheses jointly satisfiable.

---

## Verdict and items.json

Verdict: **FAITHFUL**. Both directions of the dimension bound are genuinely,
axiom-cleanly, non-vacuously rendered; the action is the true `𝔰𝔩(2)`-action; "irreducible"
is the real condition; the `[IsAlgClosed k]` and `p > 2` hypotheses are faithful. The
fine classification (highest-weight parametrization) is deferred with an explicit,
honest docstring note, and issue #7196 pre-accepts that deferral as the scoping for a
`verified` verdict.

`progress/items.json`: set `Chapter2/Problem2.16.4` `fidelity: "verified"` with a note
recording that the rendered content is the dimension bound in both directions and that
the fine classification is a documented deferral. No `feature` follow-up is filed for a
missing upper bound (it is present). A *separate, optional* future enhancement — the
full highest-weight parametrization / completeness — remains out of scope for this book
item as currently planned and is not a fidelity defect.
