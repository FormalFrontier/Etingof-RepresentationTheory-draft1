# Review: Ch4 Theorem 4.6.2 — existence/uniqueness of a unitary structure: statement-fidelity + non-vacuity audit

**Issue:** #7156 (review, report-only)
**File:** `EtingofRepresentationTheory/Chapter4/Theorem4_6_2.lean` (330 lines)
**Book reference:** `blobs/Chapter4/Theorem4.6.2.md`, `blobs/Chapter4/Discussion_after_Theorem4.6.2.md`
**Date:** 2026-07-21 (UTC)

## Verdict

**FAITHFUL — no defect.** All three audited headline declarations
(`Theorem4_6_2_existence`, `Theorem4_6_2.innerEquivDual`, `Theorem4_6_2_uniqueness`) faithfully
state the book's claims, are non-vacuous, and are axiom-clean: each depends only on the standard
`[propext, Classical.choice, Quot.sound]` set — no `sorryAx`, no custom axiom. No `def` body is
sorried (`coreOfLinearEquiv`, `avgCore`, `innerFunctional`, `innerToDual`, `innerEquivDual` are all
genuinely constructed). No proposition is weakened to `True`. Report-only; no Lean changes and no
`feature` follow-up is warranted.

- `lake build EtingofRepresentationTheory.Chapter4.Theorem4_6_2` exits 0 (8580 jobs).
- Comment-stripped `sorry`/`admit` scan of the file: **0** real occurrences.

## 1. Axiom-cleanliness audit

`#print axioms` was run on the three headline declarations via a scratch importer. All three
report exactly `[propext, Classical.choice, Quot.sound]`:

| Declaration | Location | Axioms |
|---|---|---|
| `Etingof.Theorem4_6_2_existence` | `Theorem4_6_2.lean:112` | clean |
| `Etingof.Theorem4_6_2.innerEquivDual` | `Theorem4_6_2.lean:228` | clean |
| `Etingof.Theorem4_6_2_uniqueness` | `Theorem4_6_2.lean:246` | clean |

("clean" = `depends on axioms: [propext, Classical.choice, Quot.sound]`.)

## 2. What the book claims

> **Theorem 4.6.2.** If G is finite, then any finite dimensional representation of G has a
> unitary structure. If the representation is irreducible, this structure is unique up to scaling
> by a positive real number.

- **Part (i)** — existence, via Weyl averaging `B̄(v,w) = Σ_{g∈G} B(ρ(g)v, ρ(g)w)`, producing a
  positive definite `G`-invariant Hermitian form.
- **Part (ii)** — for irreducible `V`, any two positive definite `G`-invariant Hermitian forms are
  related by `B₁(v,w) = B₂(Av,w)` with `A` a representation homomorphism (nondegeneracy gives the
  intertwiner `A`); by Schur `A = λ·Id`, and `λ > 0`.

Book conventions (footnote): a Hermitian form is sesquilinear with `(zv,w) = z(v,w)`,
`(v,w) = conj (w,v)`, and positive definite means `(v,v) > 0` for `v ≠ 0`.

## 3. Statement-fidelity audit

### 3.1 `Theorem4_6_2_existence` (`Theorem4_6_2.lean:112`) — FAITHFUL

```lean
theorem Theorem4_6_2_existence
    (G : Type*) [Group G] [Fintype G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ c : InnerProductSpace.Core ℂ V,
      ∀ (g : G) (v w : V), c.inner (ρ g v) (ρ g w) = c.inner v w
```

- **"unitary structure" = positive definite Hermitian form.** `InnerProductSpace.Core ℂ V`
  bundles exactly this: `conj_inner_symm` (Hermitian symmetry), `re_inner_nonneg` (positive
  semidefinite), `definite` (`inner x x = 0 → x = 0`), and `add_left`/`smul_left` (sesquilinearity).
  Together `re_inner_nonneg` + `definite` give genuine positive-definiteness. The form is real
  data, not a `Prop` placeholder.
- **Convention note (harmless).** Mathlib's `Core` is conjugate-linear in the *first* slot
  (`smul_left : inner (r•x) y = conj r * inner x y`), the mirror of the book's linear-in-first
  convention. This is a pure convention flip; "positive definite `G`-invariant Hermitian form" is
  the same object under either slot choice, and neither invariance nor positivity depends on it.
  No fidelity loss.
- **`G`-invariance is genuinely in the statement**, not dropped: the second conjunct
  `∀ g v w, c.inner (ρ g v) (ρ g w) = c.inner v w` is exactly `G`-invariance of the form.
- **Hypotheses are load-bearing.** `Fintype G` is required for the averaging sum `Σ_{g∈G}`;
  `FiniteDimensional ℂ V` is required to obtain the seed inner product from a finite basis
  (`Module.finBasis` → `EuclideanSpace`). Removing either breaks the construction.
- **Non-vacuous.** The witness is genuinely constructed as `avgCore ρ (coreOfLinearEquiv e)`; both
  helper `def`s have real bodies (no sorry). `InnerProductSpace.Core ℂ V` is inhabited with real
  content for any f.d. `V`. The degenerate `V = 0` case is still a true, meaningful instance (a
  trivial form is `G`-invariant), not a vacuity artifact — the claim holds for every f.d. `V`.

Matches the book's part (i) exactly, including the averaging construction in the proof
(`avgCore`, lines 62–106).

### 3.2 `innerEquivDual` (`Theorem4_6_2.lean:228`) — FAITHFUL (real constructed def)

```lean
noncomputable def innerEquivDual (c : InnerProductSpace.Core ℂ V) [FiniteDimensional ℂ V] :
    V ≃ₛₗ[starRingEnd ℂ] Module.Dual ℂ V :=
  LinearEquiv.ofBijective (innerToDual c) ⟨innerToDual_injective c, innerToDual_surjective c⟩
```

- **Not a sorry'd def.** The body is a genuine `LinearEquiv.ofBijective` applied to the
  conjugate-linear map `innerToDual c` (`v ↦ c(v, ·)`), with real bijectivity proofs: injectivity
  from `definite` (`innerToDual_injective`, lines 197–205) and surjectivity from equal real
  finrank of `V` and `Module.Dual ℂ V` (`innerToDual_surjective`, lines 209–224). No sorry anywhere
  in the chain.
- **Correct type.** It is a *conjugate-linear* equivalence `V ≃ₛₗ[starRingEnd ℂ] V*`, matching the
  discussion after 4.6.2: a nondegenerate invariant sesquilinear form is the same as an isomorphism
  `V̄ → V*`. The `@[simp]` companion `innerEquivDual_apply` pins the action to `c.inner v w`,
  confirming the equivalence really is "pair with the form."
- **Non-vacuous / load-bearing hypothesis.** `[FiniteDimensional ℂ V]` is essential: the map is
  injective without it, but surjectivity (hence the equivalence) uses the finite-dimensional
  finrank equality. Serves its role as the intertwiner-building tool in the uniqueness proof.

### 3.3 `Theorem4_6_2_uniqueness` (`Theorem4_6_2.lean:246`) — FAITHFUL

```lean
theorem Theorem4_6_2_uniqueness
    (G : Type*) [Group G] [Fintype G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hnontrivial : Nontrivial V)
    (hirr : ∀ W : Submodule ℂ V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (c₁ c₂ : InnerProductSpace.Core ℂ V)
    (h₁ : ∀ (g : G) (v w : V), c₁.inner (ρ g v) (ρ g w) = c₁.inner v w)
    (h₂ : ∀ (g : G) (v w : V), c₂.inner (ρ g v) (ρ g w) = c₂.inner v w) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v w : V, c₂.inner v w = (lam : ℂ) * c₁.inner v w
```

- **Scoped to irreducible `V`.** Irreducibility is expressed correctly as the pair
  (`Nontrivial V`) + (every `ρ`-invariant submodule is `⊥` or `⊤`). `hnontrivial` rules out
  `V = 0` so that `⊥ ≠ ⊤`; `hirr` is the no-proper-nonzero-invariant-subspace condition. Together
  this is exactly "irreducible representation."
- **Two invariant positive definite forms.** `c₁, c₂ : InnerProductSpace.Core ℂ V` with `h₁, h₂`
  their `G`-invariance — matching the book's "two positive definite `G`-invariant Hermitian forms."
- **Conclusion = "unique up to a positive real scalar."** `∃ lam : ℝ, 0 < lam ∧ c₂ = lam • c₁`
  (pointwise `c₂.inner v w = (lam:ℂ) * c₁.inner v w`). The scalar is a **real** number and is
  **strictly positive**, faithfully matching "unique up to scaling by a positive real number."
  The proof genuinely follows the book: builds the intertwiner `A` (via `innerEquivDual`), shows it
  commutes with `ρ` (`hcomm`), applies Schur through `Module.End.exists_eigenvalue` + irreducibility
  to get `A = μ•Id`, then identifies `conj μ` with the positive real `b/a` using positivity of the
  form on a nonzero vector.
- **Non-vacuous; hypotheses satisfiable.** `Theorem4_6_2_existence` supplies invariant forms, and
  irreducible finite-dimensional complex reps of finite groups exist, so `c₁, c₂, h₁, h₂, hirr,
  hnontrivial` are jointly satisfiable — the theorem is not vacuously true. `Nontrivial V` is
  load-bearing (needed both for `exists_eigenvalue` and to extract a nonzero `v₀` for the positivity
  argument); `hirr` is load-bearing (Schur step); `Fintype G`/`FiniteDimensional ℂ V` feed the
  eigenvalue/finrank machinery. No degenerate case collapses the statement: the conclusion is a real
  proportionality claim (`c₁ = c₂` merely yields `lam = 1`), not a triviality.

## 4. Conclusion

All three headline declarations are **FAITHFUL** to Theorem 4.6.2 and its surrounding discussion,
**non-vacuous**, and **axiom-clean** (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
The `Core`-convention slot flip and the trivial `V = 0` boundary case are both harmless and do not
affect fidelity. No statement or vacuity defect found; **report-only, no `feature` follow-up.**
