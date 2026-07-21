# Review — Ch4 Theorem 4.1.1: Maschke's Theorem (parts i & ii)

- **Issue:** #7126 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/dd09f010`
- **Target:** `EtingofRepresentationTheory/Chapter4/Theorem4_1_1.lean` (89 lines), sorry-free on `main`
- **Supporting infrastructure:** `EtingofRepresentationTheory/Infrastructure/IrreducibleEnumeration.lean` (804 lines, 0 `sorry`) — supplies `IrrepDecomp` and the Wedderburn-Artin machinery the theorems package.
- **Fidelity reference:** `blobs/Chapter4/Theorem4.1.1.md` (+ `.refs.md`)
- **Focus areas:** statement fidelity per book part (i)/(ii); non-vacuity (existential witnessed by a genuine construction, hypotheses jointly satisfiable); axiom cleanliness.
- **Overall verdict:** **FAITHFUL** (with two recorded scope/cleanup notes, neither a defect).
  All three declarations build, are axiom-clean, and transcribe what they claim without
  overstatement. Part (i)'s conclusion matches the book exactly; part (ii) is formalized in
  two faithful forms (full algebra-iso + enumeration + sum-of-squares, and a dimension-only
  weakening) whose existentials are witnessed by the genuine `IrrepDecomp.mk'` construction
  (built on `MonoidAlgebra.wedderburnArtin`), never `sorry`/`True`. Two things are recorded
  below and **one low-priority follow-up is filed**: (a) part (i) carries an unused
  `[DecidableEq G]` hypothesis (cosmetic, mirrors #7118); (b) the book's "isomorphism *of
  representations*" clause and the resulting regular-representation decomposition
  `k[G] ≅ ⊕ᵢ dim(Vᵢ)·Vᵢ` are captured only in the module/docstring prose, not as a Lean
  statement — a completeness gap, not a divergent or false claim. Neither undermines the
  fidelity of the statements that *are* present.

---

## 0. Build and axiom-cleanliness audit

`lake build EtingofRepresentationTheory.Chapter4.Theorem4_1_1` exits 0 (**8581 jobs**;
incremental 2.7s after `lake exe cache get`). `#print axioms` on all three declarations
(via a scratch importer, since removed) returns exactly the standard trio — **no `sorryAx`,
no custom axiom**:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `Etingof.Theorem4_1_1_semisimple` | 32 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem4_1_1_sum_of_squares` | 51 | `[propext, Classical.choice, Quot.sound]` |
| `Etingof.Theorem4_1_1_algebra_iso` | 76 | `[propext, Classical.choice, Quot.sound]` |

A `sorry` grep over the target file and its sole project dependency
`Infrastructure/IrreducibleEnumeration.lean` returns 0 hits. The `IrrepDecomp` data and every
field the theorems project out (`n`, `d`, `d_pos`, `sum_sq_eq_card`, `columnFDRep`,
`columnFDRep_simple`, `columnFDRep_injective`, `columnFDRep_surjective`, `endIso`,
`sum_finrank_sq_eq_card`) are real declarations, not placeholders.

Build carries two pre-existing non-blocking linter warnings in the infrastructure file
(`show`-vs-`change` at lines 669/695) and the `[DecidableEq G]` unused-hypothesis note on
part (i) (see §1). None affect correctness.

---

## 1. Statement fidelity, per part

**Book (Theorem 4.1.1, Maschke).** *"Let G be a finite group and let k be a field whose
characteristic does not divide |G|. Then: (i) The algebra k[G] is semisimple. (ii) There is
an isomorphism of algebras ψ : k[G] → ⊕ᵢ End Vᵢ defined by g ↦ ⊕ᵢ g|_{Vᵢ}, where Vᵢ are the
irreducible representations of G. In particular, this is an isomorphism of representations of
G ... Hence, the regular representation k[G] decomposes into irreducibles as ⊕ᵢ dim(Vᵢ)·Vᵢ,
and one has |G| = Σᵢ dim(Vᵢ)²."*

### Part (i) — `Etingof.Theorem4_1_1_semisimple` — **FAITHFUL**

```
(k G : Type*) [Field k] [Group G] [Fintype G] [DecidableEq G]
(h : IsUnit (Fintype.card G : k)) : IsSemisimpleRing (MonoidAlgebra k G)
```

- **Conclusion.** `IsSemisimpleRing (MonoidAlgebra k G)` = "k[G] is semisimple", exactly the
  book's part (i). `MonoidAlgebra k G` is the book's `k[G]` (confirmed by `.refs.md`).
- **Hypothesis.** `IsUnit (Fintype.card G : k)` over a field is equivalent to
  `(card G : k) ≠ 0`, i.e. `char k ∤ |G|` — a faithful rendering of the book's hypothesis.
  The proof converts it to `NeZero (Nat.card G : k)` and closes by `infer_instance`
  (`MonoidAlgebra.instIsSemisimpleRing`).
- **Note (cosmetic, not a defect):** `[DecidableEq G]` is unused (compiler linter confirms).
  It is always satisfiable (`Classical.decEq`), so it neither strengthens the hypothesis in
  any real sense nor induces vacuity; it is dead weight that should be dropped in favour of
  `classical`. This mirrors the #7118 finding (an unnecessary `[FiniteDimensional k A]` on
  `characters_linearly_independent`). Filed as low-priority cleanup follow-up #7130.

### Part (ii), full form — `Etingof.Theorem4_1_1_algebra_iso` — **FAITHFUL**

```
(k G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
∃ (n : ℕ) (V : Fin n → FDRep k G),
  (∀ i, Simple (V i)) ∧
  (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
  (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
  Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Module.End k (V i)) ∧
  ∑ i, Module.finrank k (V i) ^ 2 = Fintype.card G
```

- **The Vᵢ.** Quantifying `V : Fin n → FDRep k G` with (a) each `Simple`, (b) pairwise
  non-isomorphic (`Nonempty (V i ≅ V j) → i = j`), (c) exhaustive (every simple `W` is `≅`
  some `V i`) is precisely the book's "the Vᵢ are *the* irreducible representations of G"
  — a genuine complete, non-redundant enumeration of iso-classes, not a mere finite list.
- **The isomorphism.** `Nonempty (k[G] ≃ₐ[k] Π i, Module.End k (V i))` is the book's
  algebra iso `ψ : k[G] → ⊕ᵢ End Vᵢ` (finite `Π` = `⊕`). The witness is `IrrepDecomp.endIso`,
  the Wedderburn iso `k[G] ≃ Π Matrix` composed with `Matrix.toLinAlgEquiv'` reading each
  block as `End(Vᵢ)`. Because `columnRep` (hence each `Vᵢ = columnFDRep i`) is *defined* as
  the block-projection action of `k[G]`, `ψ` restricted to `End(Vᵢ)` is literally
  `g ↦ g|_{Vᵢ}` — so the book's defining formula `g ↦ ⊕ᵢ g|_{Vᵢ}` holds by construction.
  The statement asserts only *existence* of an algebra iso; that this specific `ψ` realizes
  the book's map is documented in the docstring and true of the witness.
- **Sum of squares.** `∑ i, finrank k (V i) ^ 2 = card G` is `|G| = Σᵢ dim(Vᵢ)²`, verbatim.
- **`IsAlgClosed k`.** Correctly present and genuinely *needed*: the `⊕ End_k(Vᵢ)` (matrix-
  block) form and the sum-of-squares formula hold over an algebraically closed field (so that
  `End_G(Vᵢ) = k` by Schur); over e.g. ℝ both can fail. This matches the book's operative
  setting for part (ii). Not an over-strengthening.

### Part (ii), dimension-only form — `Etingof.Theorem4_1_1_sum_of_squares` — **FAITHFUL (weakening)**

```
... [NeZero (Nat.card G : k)] :
∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧ ∑ i, (d i) ^ 2 = Fintype.card G
```

A faithful projection of the full form to the numeric identity: same hypotheses, and its
conclusion `∑ (d i)² = card G` with `d i > 0` is entailed by (a strict weakening of) the
full form (`d i = finrank k (V i)`, positive since each `Vᵢ` is a nonzero simple). It makes
**no** claim the book does not; it is a corollary, not a divergent statement.

---

## 2. Non-vacuity

- **Hypotheses jointly satisfiable.** Take `k = ℂ`, `G` any finite group: `ℂ` is a field,
  algebraically closed, and `(Nat.card G : ℂ) ≠ 0` (char 0), so `NeZero` holds; for part (i),
  `IsUnit (card G : ℂ)` holds likewise. The theorems are therefore not vacuously true.
- **Existentials witnessed by real constructions.** Both part-(ii) statements instantiate
  `D : IrrepDecomp k G := IrrepDecomp.mk'`, whose fields come from
  `MonoidAlgebra.wedderburnArtin` (`choose n d hd he`). The projected data — `D.n`, `D.d`,
  `D.d_pos`, `D.columnFDRep`, `D.endIso`, and the proved lemmas `columnFDRep_simple/injective/
  surjective`, `sum_sq_eq_card`, `sum_finrank_sq_eq_card` — are all genuine (no `sorry`,
  no `True` placeholder). `columnFDRep i = FDRep.of (columnRep i)` is a real `FDRep`, and the
  `≅` produced by `columnFDRep_surjective` is a genuine `FDRep` isomorphism (built via Schur
  in the infrastructure), not a trivial/placeholder morphism.
- **Enumeration is over a nonempty, correctly-sized class.** `card G ≥ 1` forces
  `∑ (d i)² = card G ≥ 1`, so `n ≥ 1`: there is at least one irreducible (the trivial rep),
  confirming the family is not the empty enumeration.

---

## 3. Scope note — the "isomorphism of representations" clause (completeness gap, not a defect)

The book's part (ii) additionally states that `ψ` is *also* an isomorphism **of
representations** (G acting by left multiplication on both sides), and draws the corollary
that the regular representation decomposes as `k[G] ≅ ⊕ᵢ dim(Vᵢ)·Vᵢ`. The Lean file:

- states `endIso` as an **algebra** isomorphism (`≃ₐ[k]`) only — it does not assert
  G-equivariance / a `FDRep`-morphism structure; and
- does **not** state the regular-representation decomposition `k[G] ≅ ⊕ᵢ dim(Vᵢ)·Vᵢ` as a
  theorem (it appears only in the module docstring, lines 12–14, and the header prose).

This is a **coverage gap**, not a fidelity defect: every statement present is faithful and
true, and nothing claims the representation-isomorphism content falsely. The sum-of-squares
identity — the book's headline consequence — *is* captured. I record the gap in follow-up
#7130 so a later session can add the representation-level decomposition if desired; it is not
required to certify the present statements as faithful.

---

## Verdict

**FAITHFUL.** Parts (i) and (ii) are transcribed correctly, non-vacuously, and axiom-cleanly.
Two recorded items — the unused `[DecidableEq G]` on part (i), and the un-formalized
representation-isomorphism / regular-rep-decomposition clause of part (ii) — are cosmetic /
completeness matters, not defects in the stated theorems. One consolidated low-priority
follow-up filed (#7130); no DEFECT issue warranted. Report-only: no `.lean` statement or
proof edits.
