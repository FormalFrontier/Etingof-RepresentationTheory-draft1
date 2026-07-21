# Fidelity audit: Chapter 3, Theorem 3.2.2 — the density theorem (#7119)

**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 7cb4f9d4)
**Scope:** `EtingofRepresentationTheory/Chapter3/Theorem3_2_2.lean`
(`Etingof.density_theorem_part1`, `Etingof.density_theorem_part2`)
**Method:** book statement/proof + cited dependencies first, then statement-vs-blob
fidelity of each part, then non-vacuity, then axiom-cleanliness.
Mirrors the established confidence-phase pattern
(`2026-07-21-ch2-theorem2_1_1-fidelity.md`, `2026-07-20-ch3-problem3_9-fidelity.md`).

## Overall verdict: **FAITHFUL**

Both declarations are genuine, axiom-clean formalizations of Etingof Theorem 3.2.2.
Part (i) is the surjectivity of the representation map onto the full k-linear
endomorphism algebra; part (ii) is the surjectivity of the combined map onto the
finite product of endomorphism algebras. The single non-printed hypothesis
(`IsAlgClosed k`) is the **standing convention of Section 3.2** and is required for
the book's "map into `End V`" formulation to hold; it is faithful, not a
strengthening. No defect filed.

## Build and axioms

- `lake exe cache get` then
  `lake build EtingofRepresentationTheory.Chapter3.Theorem3_2_2` exits 0,
  **1949 jobs** (`Built EtingofRepresentationTheory.Chapter3.Theorem3_2_2`).
- One pre-existing **style** linter warning only: `linter.unusedFintypeInType` on
  `density_theorem_part2` notes `[Fintype ι]` does not appear in the *type* (it is
  used in the proof, and could in principle be `Finite ι`). Not a fidelity issue;
  `[Fintype ι]` genuinely keeps the family finite, matching the book (footnote 3,
  "we will only consider finite direct sums").

`#print axioms`:

| Declaration | Axioms |
|---|---|
| `Etingof.density_theorem_part1` | `propext, Classical.choice, Quot.sound` |
| `Etingof.density_theorem_part2` | `propext, Classical.choice, Quot.sound` |

No `sorryAx`. No custom axioms. **Axiom-clean** (exactly the standard set).

## The `IsAlgClosed k` hypothesis (part i and part ii) — FAITHFUL

The printed statement of Theorem 3.2.2 does not repeat "algebraically closed", but
the Lean statements assume `[IsAlgClosed k]`. This is faithful, and required:

1. **It is the section's standing hypothesis.** `blobs/Chapter3/Introduction_to_3.2.md`
   opens Section 3.2 with, verbatim: *"Let $A$ be an algebra over an algebraically
   closed field $k$."* The chapter head (`Introduction.md`, Section 3.1) states the
   same. The book prints the convention once at the section head and does not repeat
   it inside each theorem statement.

2. **The theorem is false without it, in the exact form the book states.** The book's
   conclusion is that `ρ : A → End V` (full k-endomorphism algebra) is *onto*. Over a
   non-algebraically-closed field, `D := End_A(V)` is a division algebra possibly
   strictly larger than `k`, the image of `A` lands in `End_D(V) ⊊ End_k(V)`, and the
   map into `End_k(V)` is not surjective. `blobs/Chapter3/Remark3.1.5.md` makes this
   explicit for the underlying Proposition 3.1.4: dropping algebraic closure forces
   the matrix entries "no longer in `k` but in `D_i = End_A(V_i)`". The proof chain
   Theorem 3.2.2 → Corollary 3.2.1 → Proposition 3.1.4 uses `End_A(V_i) = k` (the
   second, field-dependent half of Schur's lemma), which holds precisely because `k`
   is algebraically closed.

**Verdict:** `IsAlgClosed k` is a faithful transcription of the Section 3.2 ambient
context, not an unlicensed added hypothesis. It is realized in Lean via
`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` (`End_A(V) ≅ k`), used in
both proofs.

## Part (i) — `density_theorem_part1` — FAITHFUL

Book: *"Let `V` be an irreducible finite dimensional representation of `A`. Then the
map `ρ : A → End V` is surjective."*

Lean: `Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] End k V)` under
`[Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]`
`[FiniteDimensional k V] [IsSimpleModule A V]` (and `[IsAlgClosed k]`, above).

- **The map is `ρ`.** Confirmed by `rfl`: for the ascribed
  `Algebra.lsmul k k V : A →ₐ[k] Module.End k V`, `(lsmul … a) v = a • v` holds
  definitionally. So the map is `a ↦ (v ↦ a • v)`, the representation map, and its
  codomain `End k V = Module.End k V` is the **full** k-linear endomorphism algebra
  (the book's `End V`). Surjectivity is onto all of it — matching the book's proof,
  which realizes an arbitrary `c ∈ End(V)` by matching `a` to `c` on a basis. The
  proof's final line extracts `a` with `a • v = f v` for the arbitrary target
  `f : End k V`, confirming genuine surjectivity, not a diagonal/placeholder image.
- **`[IsSimpleModule A V]` = "irreducible".** `IsSimpleModule A V` is
  `IsSimpleOrder (Submodule A V)`: `V` is nontrivial and has no submodules other than
  `⊥, ⊤`. Exactly "nonzero, no proper nonzero subrepresentation". Faithful.
- **`[FiniteDimensional k V]` = "finite dimensional"**. Faithful.

## Part (ii) — `density_theorem_part2` — FAITHFUL

Book: *"Let `V = V₁ ⊕ ⋯ ⊕ Vᵣ`, where `Vᵢ` are irreducible pairwise nonisomorphic
finite dimensional representations of `A`. Then the map `⊕ᵢ ρᵢ : A → ⊕ᵢ End(Vᵢ)` is
surjective."*

Lean: `Function.Surjective (fun a i => (Algebra.lsmul k k (V i)) a : A → ∀ i, End k (V i))`
under `[Fintype ι]`, `V : ι → Type*` each an irreducible fin-dim rep, and
`h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)`.

- **Combined map `⊕ᵢ ρᵢ`.** `a ↦ (i ↦ ρᵢ(a))` (each component is the `lsmul`
  representation map on `V i`, same as part (i)). Faithful.
- **Codomain: product vs direct sum.** The Lean codomain `∀ i, End k (V i)` is the
  finite **product**; the book writes the finite **direct sum** `⊕ᵢ End(Vᵢ)`. The
  book's own footnote [^3] states that for finite families "this distinction is
  immaterial", and `[Fintype ι]` keeps the family finite, so product = direct sum
  here. Faithful. Surjectivity is onto the **whole** product (the proof builds a
  single `a` hitting `f i` in every component `i` simultaneously, via the
  off-diagonal-vanishing + diagonal-scalar decomposition, then Jacobson density),
  not a diagonal or single-factor subset.
- **`h_noniso` = "pairwise nonisomorphic".** `IsEmpty (V i ≃ₗ[A] V j)` for `i ≠ j`
  means there is no A-linear isomorphism between distinct factors. Exactly "pairwise
  nonisomorphic". Faithful. (The book's Proposition 3.1.4 uses precisely this to get
  `B = ⊕ᵢ Bᵢ`; the Lean proof uses `bijective_or_eq_zero` + `h_noniso` to kill the
  off-diagonal blocks — the same mechanism.)
- **Each factor independently irreducible + finite-dimensional.**
  `[∀ i, IsSimpleModule A (V i)]` and `[∀ i, FiniteDimensional k (V i)]` are
  per-index, so every `V i` is separately irreducible and finite-dimensional.
  Faithful.

**Minor, non-defect generalization:** the Lean statement admits `ι` empty (`r = 0`),
where the codomain is a singleton and surjectivity is trivially true. The book
implicitly takes `r ≥ 1`. This is a harmless strict generalization (the degenerate
case is consistent, not a weakening of any claim the book makes), so no defect.

## Non-vacuity

- **Part (i) hypotheses jointly satisfiable and conclusion genuine.** Take `k = ℂ`
  (algebraically closed), `V = k` (or `V = kⁿ`), `A = End_k(V)` acting by evaluation.
  Then `IsSimpleModule A V`, `FiniteDimensional k V` hold, `End k V` is nontrivial
  (`dim = n² ≥ 1`), and `A → End k V` is (essentially the identity) genuinely onto —
  not a map into a trivial/singleton codomain.
- **Part (ii) likewise:** `ι = Fin r`, distinct simple factors (e.g.
  `A = ∏ᵢ End_k(Vᵢ)`), pairwise non-isomorphic; the product `∏ᵢ End k (V i)` is
  nontrivial for `ι` nonempty (each `IsSimpleModule` forces `Nontrivial (V i)`, hence
  `End k (V i)` nontrivial), and the combined map is onto. Genuine.

## Notes / follow-ups

- None required. Statement is faithful and axiom-clean; nothing to change in the Lean
  file. The module docstring already records the `IsAlgClosed k` hypothesis explicitly
  ("over an algebraically closed field `k`"), so no docstring reword is warranted.
- The `linter.unusedFintypeInType` warning on `density_theorem_part2` is cosmetic
  (`Fintype ι` → `Finite ι` would still need `Fintype.ofFinite` in the proof) and out
  of scope for this report-only fidelity review; not filed as a defect.

**Verdict: FAITHFUL — both parts, axiom-clean, no defect.** No DEFECT issue filed.
