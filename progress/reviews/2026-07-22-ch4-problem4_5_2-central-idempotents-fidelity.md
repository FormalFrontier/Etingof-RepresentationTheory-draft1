# Stage 3.7 audit — Problem 4.5.2 (primitive central idempotents `ψ_i` of `ℂ[G]`)

**Issue:** #7244 (statement-fidelity & non-vacuity audit; report-only).
**File:** `EtingofRepresentationTheory/Chapter4/Problem4_5_2.lean` (325 lines).
**Blob:** `blobs/Chapter4/Problem4.5.2.md`.
**HEAD:** `2b305b75` (`origin/main`).
**Verdict:** **VERIFIED** — statement-faithful and non-vacuous for both parts (i) and (ii).

## Build / axiom check

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_5_2` exits 0 (only
  `unusedFintypeInType` lint warnings on three private helpers — cosmetic, no
  bearing on fidelity).
- `#print axioms` on all four headline declarations returns exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, axiom-clean:
  `psi_acts_self`, `psi_acts_other`, `psi_idempotent`, `psi_orthogonal`.

## Book text

> Let `G` be a finite group. Let `V_i` be the irreducible complex representations of `G`.
> For every `i`, let `ψ_i = (dim V_i / |G|) · ∑_{g∈G} χ_{V_i}(g)·g⁻¹ ∈ ℂ[G]`.
> (i) Prove that `ψ_i` acts on `V_j` as the identity if `j = i`, and as the null map if `j ≠ i`.
> (ii) Prove that the `ψ_i` are idempotents: `ψ_i² = ψ_i`, and `ψ_i ψ_j = 0` for `i ≠ j`.

## Definition faithfulness — `psi` (line 44)

```lean
noncomputable def psi (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) •
    ∑ g : G, V.character g • MonoidAlgebra.single g⁻¹ (1 : ℂ)
```

- Real `def` with a genuine body (noncomputable but constructed — not a stub).
- **Scalar** `finrank ℂ V / card G` = `dim V_i / |G|` — exact. ✓
- **Sum** `∑ g, χ_V(g) • single g⁻¹ 1`: `single g⁻¹ (1:ℂ)` is the group-algebra basis
  element `g⁻¹`, scaled by the character value. This is `∑_g χ_{V_i}(g)·g⁻¹` — the
  inverse `g⁻¹` is present (not `g`), matching the book precisely. ✓
- `V.character g = LinearMap.trace ℂ V (V.ρ g)` (Mathlib `FDRep.character`, confirmed) —
  the genuine character `χ_{V_i}(g)`, not a placeholder. ✓

The action of `ψ V` on a representation `W` is taken via
`Representation.asAlgebraHom W.ρ : ℂ[G] →ₐ[ℂ] End ℂ W`, the genuine group-algebra
module action — so "`ψ_i` acts on `V_j`" is encoded correctly.

## Part (i) fidelity

- `psi_acts_self (V) [Simple V] : asAlgebraHom V.ρ (psi V) = LinearMap.id` (line 166).
  Conclusion is the **identity** endomorphism (scalar `1`), not the weaker "acts as
  *some* scalar" — this is the key fidelity risk flagged by the issue, and it is
  discharged: the scalar `c` is pinned to `1` (line 181, via the trace
  `= dim V` computed from `∑ χ_V(g)χ_V(g⁻¹) = |G|`). ✓
- `psi_acts_other (V W) [Simple V] [Simple W] (h : IsEmpty (W ≅ V)) :
  asAlgebraHom W.ρ (psi V) = 0` (line 189). Conclusion is the **zero** map (scalar `0`,
  pinned at line 203 from `∑ χ_V(g)χ_W(g⁻¹) = 0`). ✓
- **`IsEmpty (W ≅ V)`** is `CategoryTheory.Iso` in `FDRep ℂ G`: no isomorphism of
  representations `W ≅ V`. With `[Simple V] [Simple W]` this genuinely encodes
  "two non-isomorphic irreducibles `V_j ≇ V_i`" — not vacuous, not over-strong. ✓
- The Schur step is the categorical Schur's lemma
  (`finrank_endomorphism_simple_eq_one`) applied to the invariants of
  `Representation.linHom V.ρ V.ρ` — the honest realization of the blob's
  Corollary 2.3.10 hint, with the scalar read off from the trace.

## Part (ii) fidelity

- `psi_idempotent (V) [Simple V] : psi V * psi V = psi V` (line 309): `ψ_i² = ψ_i` as
  elements of `MonoidAlgebra ℂ G` (the group algebra `ℂ[G]`), i.e. multiplication in
  `ℂ[G]` — not mere operator composition on one module. ✓
- `psi_orthogonal (V W) [Simple V] [Simple W] (h : IsEmpty (W ≅ V)) : psi W * psi V = 0`
  (line 318): `ψ_j ψ_i = 0` in `ℂ[G]`. Because representation-iso is symmetric,
  `IsEmpty (W ≅ V) ↔ IsEmpty (V ≅ W)`, so instantiating with `V, W` swapped also gives
  `psi V * psi W = 0`; the single theorem therefore covers the full symmetric
  orthogonality claim "`ψ_i ψ_j = 0` for `i ≠ j`". ✓

## Irreducibility hypotheses

`[Simple V]` / `[Simple W]` are `CategoryTheory.Simple` in `FDRep ℂ G` — a simple object
of `FDRep ℂ G` is exactly an irreducible complex representation. Genuine irreducibility
hypotheses (used to invoke `FDRep.char_orthonormal`, which itself requires
`[Simple V] [Simple W]`), not weakened or mistargeted. ✓

## Non-vacuity

- Hypotheses are simultaneously satisfiable: every finite group has the trivial
  irreducible (part (i) diagonal, idempotence); any group with ≥2 non-isomorphic
  irreducibles (e.g. a nontrivial abelian group, or `S₃`) satisfies the off-diagonal /
  orthogonality hypotheses. So no theorem is vacuously true.
- `psi V` is a genuine `ℂ[G]` element (real body); `G` is forced nonempty (`Nonempty G`
  from `⟨1⟩`, used in `card_ne_zero_cx`); simple objects have positive finrank
  (`finrank_pos_of_simple`), so the identity/zero distinction is non-degenerate.
- No `True`-typed or trivially-dischargeable hypothesis anywhere.

## Coverage

The book indexes over the isomorphism classes `{V_i}` of irreducible reps; the Lean
statements quantify over simple objects `V, W : FDRep ℂ G` directly. Every irreducible
is a simple `FDRep` and conversely, so the object-level quantification faithfully covers
the indexed family (indeed covers every representative, not just one per class).
**`coverage: covered_full`** — both parts (i) and (ii), all four sub-claims, present and
faithful.

## Conclusion

No fidelity gap. `items.json` updated: `fidelity: verified`, `coverage: covered_full`,
plus `fidelity_decl` / `lean_file` / `fidelity_note`. No `.lean` edits (report-only), no
follow-up issue required.
