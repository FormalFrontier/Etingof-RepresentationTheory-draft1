# Statement-fidelity & non-vacuity audit — Theorem 5.23.2 (Peter-Weyl for GL(V))

**Issue:** #7149
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 845e0c03)
**Scope:** report-only fidelity + non-vacuity audit of `Etingof.Theorem5_23_2_i`
and `Etingof.Theorem5_23_2_ii`
(`EtingofRepresentationTheory/Chapter5/Theorem5_23_2.lean`), with the companion
equivariant capstone `Etingof.Theorem5_23_2_ii_equivariant`
(`…/Theorem5_23_2_PeterWeyl.lean`) inspected as context.
**Verdict: FAITHFUL with documented nuance — all three declarations axiom-clean,
no defect. Nothing filed.**

## Headline findings

1. **Part (i) `Theorem5_23_2_i` is a faithful (partial) rendering of book part
   (i).** It captures "every finite-dimensional algebraic representation of
   `GL(V)` is completely reducible" exactly, as semisimplicity of `ρ` over the
   group algebra `k[GLₙ]`. The book's *finer* claim (the summands are the `Lλ`
   and are pairwise non-isomorphic) is **not** part of this declaration; it is
   documented as tracked separately and is genuinely realized elsewhere
   (`AlgIrrepGL`, and used by the equivariant part (ii)).
2. **Part (ii) `Theorem5_23_2_ii` deliberately understates the book** — it is a
   *bare `k`-linear* rank isomorphism `R ≃ₗ[k] ⊕_λ L*_λ ⊗ L_λ`, carrying **no**
   `GL×GL`-equivariant content. This is loudly and accurately flagged in its own
   docstring ("⚠ Partial formalization … carries **no** `GL_n × GL_n`-equivariant
   content — the actual mathematical theorem"). No hidden vacuity: the
   understatement is transparent.
3. **The genuine equivariant Peter-Weyl statement now exists and is complete.**
   `Theorem5_23_2_ii_equivariant` (companion file) states a genuine
   `GL×GL`-equivariant isomorphism (`IsEquivariantEquiv (localBiRep k n)
   (peterWeylRHS n k) e`) and is **sorry-free and axiom-clean**. This corrects
   the issue's premise that the finer file "currently carries sorrys (≈10)": the
   ten `grep` hits are all the string **"sorry-free"** in comments; the file has
   **zero** actual `sorry`s.
4. **All three declarations are axiom-clean** (`[propext, Classical.choice,
   Quot.sound]`, no `sorryAx`).

## Sources compared

- **Book statement** (`blobs/Chapter5/Theorem5.23.2.md`):
  > **Theorem 5.23.2.** *(i) Every finite dimensional algebraic representation of
  > `GL(V)` is completely reducible, and decomposes into summands of the form
  > `Lλ` (which are pairwise nonisomorphic).*
  >
  > *(ii) (The Peter-Weyl theorem for `GL(V)`) Let `R` be the algebra of
  > polynomial functions on `GL(V)`. Then as a representation of `GL(V) × GL(V)`
  > (with action `(ρ(g,h)φ)(x) = φ(g⁻¹xh)`), `R` decomposes as
  > `R = ⊕_λ L*_λ ⊗ L_λ`, where the summation runs over all `λ`.*
- **Book proof** (`blobs/Chapter5/Discussion_proof_of_Theorem5.23.2.md`):
  (i) equivariant embedding `ξ : Y → Y ⊗ R`, reduce to `Y ⊆ Rᵐ`; every element of
  `R` is a polynomial in `gᵢⱼ` times a nonpositive power of `det(g)`, so `R` is a
  quotient of `⊕ Sʳ(V⊗V*) ⊗ (∧ᴺV*)^{⊗s}`; hence `Y` embeds in a sum of
  `V^{⊗n} ⊗ (∧ᴺV*)^{⊗s}`, which are completely reducible (Schur-Weyl). (ii)
  `Hom_{GL}(Y,R) ≅ Y*` for right-translation `R`; combined with (i) gives the
  decomposition, compatible with the left action.
- **Book definition of "algebraic"** (`blobs/Chapter5/Definition5.23.1.md`):
  > **Definition 5.23.1.** A finite dimensional representation `Y` of `GL(V)` is
  > **algebraic** (rational, polynomial) if its matrix elements are polynomial
  > functions of the entries of `g`, `g⁻¹` (i.e. belong to `k[gᵢⱼ][1/det(g)]`).

## Part (i): `Theorem5_23_2_i` (`Theorem5_23_2.lean:85`)

```lean
theorem Theorem5_23_2_i
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ)
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : Etingof.IsAlgebraicRepresentation n ⇑ρ) :
    IsSemisimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule
```

### Conclusion faithfully renders "completely reducible"
- `IsSemisimpleModule (MonoidAlgebra k GLₙ) ρ.asModule` is semisimplicity of `Y`
  **as a `k[GLₙ]`-module**, i.e. of the *representation* `ρ`. That is exactly
  "completely reducible" (`Y` = direct sum of irreducible subrepresentations). ✓
- **Genuine equivariant content, not a triviality.** `k[GLₙ]` is not a
  semisimple ring (`GLₙ(k)` is infinite), so this is false for a generic
  `k[GLₙ]`-module; it holds *because* `ρ` is algebraic. The docstring explicitly
  contrasts a previous weaker formalization (`IsSemisimpleModule k Y`, trivially
  true for any vector space) — the current statement avoids that vacuity. ✓

### Documented scope reduction: the `Lλ` refinement
- The book's part (i) also asserts the summands are the `Lλ`, pairwise
  non-isomorphic. The Lean declaration proves *only* semisimplicity; the
  highest-weight identification is **not** in this statement. This is an honest,
  documented partial rendering (docstring lines 62–65: "tracked separately"), and
  the `Lλ` content is realized elsewhere — `AlgIrrepGL n lam k` and the pairwise
  distinctness are what the equivariant part (ii) (`peterWeylMap_injective`)
  depends on. **Not a defect**, but noted: "completely reducible" is captured;
  "into pairwise-nonisomorphic `Lλ`" is deferred, not delivered by *this* decl.

### Hypotheses vs. the book's ambient assumptions
- `[Field k] [IsAlgClosed k] [CharZero k]`: §5.23 sits in the alg-closed,
  characteristic-0 setting of Chapter 5 (Schur-Weyl / `Lλ` theory). These match
  the book's ambient assumptions and are genuinely used by the proof route:
  the polynomial-decomposition engine (`polynomialRep_isSemisimple`,
  `decompose_polynomial_gl_rep`) rests on Schur-Weyl semisimplicity, which needs
  `CharZero` (semisimplicity of `Sⁿ`) and `IsAlgClosed` (the `Lλ`
  classification). Neither is stronger than the book. ✓
- `[Module.Finite k Y]` = "finite dimensional" from the book statement. ✓
- **Universe nuance:** `k : Type` (universe 0), not `Type*`. This is a technical
  restriction inherited from the polynomial-decomposition machinery
  (`decompose_polynomial_gl_rep`), noted in the docstring (lines 82–83). It
  covers the book's intended fields (e.g. `ℂ`), so it is not a fidelity gap, but
  it does mean part (i) is not stated in full universe generality.

### Non-vacuity: the hypothesis `IsAlgebraicRepresentation` is real and satisfiable
- **Real content** (`Definition5_23_1.lean:43`): `IsAlgebraicRepresentation n ρ`
  demands a basis `b` and polynomials `P a c ∈ k[GLCoordVars n]` with
  `b.repr (ρ g (b c)) a = evalAtGL g (P a c)` for **all** `g` — i.e. every matrix
  coefficient `g ↦ (ρ g)_{ac}` is a regular function in `gᵢⱼ` and `det(g)⁻¹`
  (`GLCoordVars n = (Fin n × Fin n) ⊕ Unit`, the extra `Unit` = the `1/det`
  variable; `evalAtGL` substitutes `Xᵢⱼ ↦ gᵢⱼ`, `D ↦ det(g)⁻¹`). This is exactly
  Definition 5.23.1 and is **not** trivially satisfiable — a `ρ` with a
  non-regular matrix coefficient fails it. ✓
- **Concrete witness:** `glTensorRep_isAlgebraic k n m`
  (`GLRepAlgebraic.lean:193`) proves the diagonal tensor action `g ↦ g^{⊗m}` on
  `(kⁿ)^{⊗m}` is algebraic (matrix coefficient = the monomial
  `∏ₘ X_{(h m, f m)}`). For `m = 1` this is the **standard representation** `kⁿ`
  of `GLₙ`. Also `algIrrepGLRepρ_isAlgebraic` (`PeterWeylMatrixCoeff.lean:107`)
  witnesses algebraicity of each `Lλ`. Hence the hypothesis is satisfiable and
  part (i) is non-vacuous. ✓

### Axioms
`#print axioms Etingof.Theorem5_23_2_i` →
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`. ✓

## Part (ii): `Theorem5_23_2_ii` (`Theorem5_23_2.lean:315`)

```lean
theorem Theorem5_23_2_ii [CharZero k] (n : ℕ) (hn : 0 < n) :
    Nonempty (GLCoordinateRing n k ≃ₗ[k]
      (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)))
```
where `GLCoordinateRing n k = MvPolynomial (GLCoordVars n) k` = `k[Xᵢⱼ, D]`.

### What it claims vs. what the book claims
- **Claim as formalized:** a *bare `k`-linear* isomorphism between `R` and
  `⊕_λ L*_λ ⊗ L_λ`, established by `nonempty_linearEquiv_of_rank_eq` from a rank
  computation (`peterWeyl_rank_eq`): both sides are countably-infinite-dimensional
  free `k`-modules for `n ≥ 1` (LHS rank `ℵ₀` via `glCoordinateRing_rank`; RHS
  `≤ ℵ₀` by `directSum_rank_le_aleph0` and `≥ ℵ₀` by `directSum_rank_ge_aleph0`,
  using that the one-row weights give `ℵ₀`-many nonzero summands).
- **Understatement, transparently flagged.** Because it is *just* a rank match,
  the iso holds for **any** two countably-infinite-dimensional `k`-modules and
  carries **none** of the book's `GL×GL`-equivariant content. The docstring says
  precisely this (lines 142–153) and labels the declaration "retained only as
  scaffolding". So this is a *documented, deliberate* understatement, not a hidden
  vacuity masquerading as the theorem. ✓ (documented nuance)
- **`R`-model nuance.** The book's `R` is `k[gᵢⱼ][1/det]`, the localization.
  This declaration models it by the *polynomial ring* `MvPolynomial (GLCoordVars
  n) k` with a free `Unit` variable for `1/det` — as a bare polynomial ring this
  is a *presentation* that is strictly larger than the true localization (the
  relation `det·D = 1` is not imposed). For the rank iso (both `ℵ₀`) this is
  harmless. The genuine equivariant statement uses the **correct** model
  `Localization.Away (detPoly k n)` (see below).
- **`n = 0` caveat.** With the free `1/det` variable, `n = 0` makes the LHS
  infinite-dimensional while the RHS is 1-dimensional; the hypothesis `hn : 0 < n`
  correctly excludes this, and the comment (lines 159–162) documents it. ✓

### The genuine equivariant theorem (companion file — context, not in scope decls)
`Theorem5_23_2_ii_equivariant` (`Theorem5_23_2_PeterWeyl.lean:892`):

```lean
theorem Theorem5_23_2_ii_equivariant (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Nonempty { e : Localization.Away (detPoly k n) ≃ₗ[k]
        (DirectSum (DominantWeight n) fun lam => (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) //
      IsEquivariantEquiv (localBiRep k n) (peterWeylRHS n k) e }
```
- This is the **faithful** rendering of book part (ii): a `GL×GL`-equivariant
  isomorphism (`IsEquivariantEquiv`) intertwining the left/right translation
  bi-action `localBiRep` on `R = k[gᵢⱼ][1/det]` (correctly the localization) with
  the action on `⊕_λ L*_λ ⊗ L_λ` (`peterWeylRHS`). It is assembled from
  `peterWeylMap_bijective = ⟨peterWeylMap_injective, peterWeylMap_surjective⟩`
  (the Cauchy decomposition: matrix coefficients of the distinct `Lλ` are
  independent and span `R`).
- **It is complete.** `grep -c sorry` on the file returns 10, but every one is
  the substring "sorry-free" inside a comment; there are **no** actual `sorry`s,
  and `#print axioms Etingof.Theorem5_23_2_ii_equivariant` →
  `[propext, Classical.choice, Quot.sound]`. So the issue's stated premise that
  this file "currently carries sorrys (≈10)" is **outdated**; the equivariant
  capstone is now axiom-clean.

### Axioms
`#print axioms Etingof.Theorem5_23_2_ii` →
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`. ✓

## Non-vacuity / axiom summary (deliverable 2)

| Declaration | `#print axioms` | `sorryAx`? | Concrete non-vacuous witness |
|---|---|---|---|
| `Theorem5_23_2_i` | `[propext, Classical.choice, Quot.sound]` | no | standard rep `kⁿ` (`glTensorRep_isAlgebraic k n 1`) is algebraic → hypothesis satisfiable; conclusion is genuine `k[GLₙ]`-semisimplicity |
| `Theorem5_23_2_ii` | `[propext, Classical.choice, Quot.sound]` | no | `n = 1`, `hn : 0 < 1`; both sides `ℵ₀`-dimensional free `k`-modules (bare linear iso) |
| `Theorem5_23_2_ii_equivariant` | `[propext, Classical.choice, Quot.sound]` | no | `n ≥ 1`, `k = ℂ`; genuine `GL×GL`-equivariant iso via `peterWeylMap_bijective` |

## Verification performed
- `lake exe cache get`, then
  `lake build EtingofRepresentationTheory.Chapter5.Theorem5_23_2` → exit 0
  (one harmless linter warning: overlapping `[CharZero k]` on
  `Theorem5_23_2_ii`; the `variable` block already provides `CharZero k`, so the
  explicit re-declaration is redundant but benign).
- `#print axioms` on all three declarations via a temporary
  `AxiomCheck5_23_2.lean` (built, results recorded above, file removed).
- `Theorem5_23_2.lean` `grep -c sorry` = 0;
  `Theorem5_23_2_PeterWeyl.lean` `grep -c sorry` = 10, all the string
  "sorry-free" in comments (0 real `sorry`s).

## Verdict

**FAITHFUL with documented nuance — no defect, nothing filed.**

- **Part (i)** faithfully renders "every finite-dimensional algebraic
  representation of `GL(V)` is completely reducible" as `k[GLₙ]`-semisimplicity;
  axiom-clean; hypothesis non-vacuous (standard rep witness). The book's finer
  "pairwise-nonisomorphic `Lλ`" refinement is a documented deferral, realized
  elsewhere in the project. The `k : Type` (universe 0) restriction is a
  documented technical scope limit, not a fidelity gap.
- **Part (ii)** `Theorem5_23_2_ii` is an intentionally understated bare linear
  rank iso, transparently documented as scaffolding, and **superseded by the now
  complete, axiom-clean `Theorem5_23_2_ii_equivariant`**, which is the genuine
  `GL×GL`-equivariant Peter-Weyl. No hidden vacuity: the weaker statement's limits
  are loudly flagged and the true statement exists sorry-free.

The one factual correction to record (documentation freshness, not a code
defect): the issue's assumption that the finer Peter-Weyl file carries ~10
`sorry`s is stale — that file is sorry-free and its equivariant capstone is
axiom-clean. No follow-up issue is warranted.
