# Statement-fidelity & non-vacuity audit — Theorem 4.5.4 (second/column orthogonality)

**Issue:** #7170
**File:** `EtingofRepresentationTheory/Chapter4/Theorem4_5_4.lean`
**Book source:** `blobs/Chapter4/Theorem4.5.4.md`
**Date:** 2026-07-21
**Verdict:** **PASS — all headline declarations FAITHFUL, axiom-clean (no `sorryAx`), non-vacuous.**

## Book statement

> **Theorem 4.5.4.** Let `g, h ∈ G`, and let `Z_g` denote the centralizer of `g` in `G`. Then
> `∑_V χ_V(g)·conj(χ_V(h)) = |Z_g|` if `g` is conjugate to `h`, and `0` otherwise,
> the sum over all irreducible representations of `G`.

The proof note establishes `conj(χ_V(h)) = χ_{V*}(h)`, then computes both sides as
`Tr|_{ℂ[G]}(x ↦ g x h⁻¹)` (basis count = conjugators; Wedderburn decomposition = character sum).

## 1. Statement fidelity

`Etingof.Theorem4_5_4` (`Theorem4_5_4.lean:347`) states, for `D : IrrepDecomp k G` and a family
`V : Fin D.n → FDRep k G`:

```
∑ i, (V i).character g * (V i).character h⁻¹
  = if IsConj g h then (Fintype.card ↥(Subgroup.centralizer ({g} : Set G)) : k) else 0
```

- **Sum over a complete irredundant system.** The hypotheses `hV : ∀ i, Simple (V i)`,
  `hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j`, and
  `hsurj : ∀ W, Simple W → ∃ i, Nonempty (W ≅ V i)` genuinely encode "each irreducible once,
  all of them." This is exactly "sum over all irreducible representations." **Faithful.**
- **RHS is the centralizer of `g`.** `Subgroup.centralizer ({g} : Set G)` is `Z_G(g)`, keyed on
  the singleton `{g}` — the centralizer of `g`, **not** `h`. Matches the book's `Z_g`. **Faithful.**
- **Conjugacy branch.** `IsConj g h` is "`g` conjugate to `h`," matching the book's cases. **Faithful.**
- **`χ_V(h⁻¹)` for `conj(χ_V(h))`.** The book writes `conj(χ_V(h))` and immediately rewrites it as
  `χ_{V*}(h)`. For a finite-group character, `χ_{V*}(h) = χ_V(h⁻¹)`, so `(V i).character h⁻¹` is the
  correct field-agnostic stand-in. Over a general field there is no complex conjugation available;
  using `χ_V(h⁻¹)` is the faithful algebraic transcription of the book's own reduction. **Faithful.**
- **Generality `ℂ → k`.** The Lean version is stated over any `[Field k] [IsAlgClosed k]` with
  `[NeZero (Nat.card G : k)]`. `IsAlgClosed` supplies the Wedderburn split into matrix algebras;
  `NeZero (|G| : k)` is exactly Maschke's semisimplicity hypothesis (invertibility of `|G|`), which
  the book invokes ("using Maschke's theorem"). The generalization is **faithful and harmless** —
  it drops only the complex-conjugation notation, already reduced away by the book's `χ_{V*}` step.

Supporting declarations all match their intended meaning:
- `trace_mulLeftRight_monoidAlgebra` (`:246`) — `Tr|_{k[G]}(x ↦ g x h⁻¹) = |Z_G(g)|` if `g~h` else `0`
  (the book's first trace computation). **Faithful.**
- `column_orthogonality_wedderburn` (`:276`) — the same trace via Wedderburn gives
  `∑_i χ_{col_i}(g)·χ_{col_i}(h⁻¹)` (the second computation). **Faithful.**
- `sum_character_prod_eq_of_complete` (`:291`) — the character sum is independent of the chosen
  complete system (transfer step). **Faithful.** (The linter notes `hW`/`hWinj` are unused in the
  proof; the statement is thus slightly *stronger* than needed, not weaker — not a defect.)
- `IrrepDecomp.columnFDRep_is_complete` (`:322`) — the Wedderburn column reps form a complete
  irredundant system (simple ∧ injective-on-classes ∧ surjective-onto-classes). **Faithful.**

## 2. Non-vacuity

- **Hypotheses simultaneously satisfiable.** `IrrepDecomp.columnFDRep_is_complete` proves the concrete
  family `D.columnFDRep` satisfies `hV`/`hinj`/`hsurj`; instantiating `V := D.columnFDRep` discharges
  all three, so the main theorem is not vacuously quantified. A decomposition itself exists via
  `IrrepDecomp.mk'` (`IrreducibleEnumeration.lean:70`), built from `MonoidAlgebra.wedderburnArtin` —
  genuine data, no sorry.
- **No `True`-weakening.** Every headline statement is a genuine equation of characters / traces /
  cardinalities; none is a placeholder.
- **`def`s construct real data.** `conjugatorEquiv` (`:47`) is a genuine `Equiv` with concrete
  `toFun z := ⟨c * z.1, …⟩` and `invFun x := ⟨c⁻¹ * x.1, …⟩` plus proved `left_inv`/`right_inv` — not a
  sorried body. `IrrepDecomp.columnRep`/`columnFDRep`/`projRingHom` (infrastructure) likewise carry
  real bodies. The `g ~ h` branch is inhabitable (e.g. `g = h`), so the `|Z_G(g)|` case is reachable.

## 3. Axiom cleanliness

`#print axioms` on every headline and supporting declaration returns exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no stray custom axiom:

```
Etingof.Theorem4_5_4                        [propext, Classical.choice, Quot.sound]
IrrepDecomp.columnFDRep_is_complete         [propext, Classical.choice, Quot.sound]
trace_mulLeftRight_monoidAlgebra            [propext, Classical.choice, Quot.sound]
column_orthogonality_wedderburn             [propext, Classical.choice, Quot.sound]
sum_character_prod_eq_of_complete           [propext, Classical.choice, Quot.sound]
conjugatorEquiv                             [propext, Classical.choice, Quot.sound]
card_conjugators                            [propext, Classical.choice, Quot.sound]
card_fixedPoints_eq_card_conjugators        [propext, Classical.choice, Quot.sound]
```

## Verification performed

- `lake exe cache get` then `lake build EtingofRepresentationTheory.Chapter4.Theorem4_5_4` — succeeds
  (8582 jobs; only style/unused-variable linter warnings, no errors).
- `grep -c sorry` on the file — `0`.
- `#print axioms` on all eight declarations — no `sorryAx`.

## Conclusion

**PASS.** Theorem 4.5.4 faithfully transcribes Etingof's second (column) orthogonality relation:
sum over a genuine complete irredundant system of irreducibles, RHS `|Z_G(g)|` on the centralizer of
`g`, `IsConj g h` branch, and `χ_V(h⁻¹)` as the faithful algebraic stand-in for `conj(χ_V(h))` per the
book's own `χ_{V*}` reduction. The `ℂ → k` generalization is faithful and harmless. All declarations
are non-vacuous and axiom-clean. No statement or vacuity defect found; no follow-up `feature` issue
required. Report-only.
