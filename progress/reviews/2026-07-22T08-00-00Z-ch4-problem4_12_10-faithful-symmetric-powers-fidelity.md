# Stage 3.7 fidelity & non-vacuity audit — Problem 4.12.10 (faithful rep contains every irreducible in a tensor/symmetric power)

- **Issue:** #7284
- **Verdict:** `verified` — `covered_partial`
- **Audited against:** `origin/main` HEAD `3b166a4d`
- **Mathlib:** as pinned in this worktree (`lake exe cache get` clean, build ✔)
- **Reviewer path:** independent re-reading of the book statement + scope check of what
  `diagTensorPow` actually names, distinct from the original formalizer's construction path.

## Book statement (`blobs/Chapter4/Problem4.12.10.md`)

> **Problem 4.12.10.** Let `G` be a finite group and let `V` be a complex representation of
> `G` which is faithful, i.e., the corresponding map `G → GL(V)` is injective. Show that any
> irreducible representation of `G` occurs inside `SⁿV` (**and hence inside `V^{⊗n}`**) for
> some `n`.
>
> Hint: … define the map `SV → F(G, ℂ)` sending a polynomial `f` on `V*` to `f_u(g) = f(gu)`.
> Show that this map is surjective and use this to deduce the desired result.

The primary asserted result is the **symmetric-power** statement (`W ↪ SⁿV`); the
tensor-power statement (`W ↪ V^{⊗n}`) is flagged in the book itself as the weaker
consequence ("and hence"). The hint's `SV → F(G, ℂ)` surjectivity argument targets the
symmetric algebra `SV` directly.

## Declaration audited

| Declaration | File:line |
|-------------|-----------|
| `Etingof.Problem4_12_10` | `Chapter4/Problem4_12_10.lean:248` |

Supporting: `diagTensorPow` (line 31), `diagTensorPow_apply` (42),
`trace_piTensorProduct_map_const` (53), `character_diagTensorPow` (83),
`eq_one_of_conjTranspose_mul_self_eq_one_of_trace_eq_card` (98),
`ρ_eq_one_of_character_eq_finrank` (161).

Headline signature:

```lean
theorem Etingof.Problem4_12_10 {G} [Group G] [Fintype G]
    {V} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ)
    {W} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule) :
    ∃ (n : ℕ) (φ : W →ₗ[ℂ] (⨂[ℂ]^n V)),
      φ ≠ 0 ∧ ∀ g : G, φ ∘ₗ σ g = (diagTensorPow ρ n g) ∘ₗ φ
```

## 1. Statement fidelity — the SⁿV vs V^{⊗n} scope question (the crux)

**What `diagTensorPow` names.** `diagTensorPow ρ n : Representation ℂ G (⨂[ℂ]^n V)` sends
`g ↦ PiTensorProduct.map (fun _ : Fin n => ρ g)`, i.e. the diagonal action on the **full**
`n`-th tensor power `⨂ⁿV` (`PiTensorProduct` over `Fin n`). It is emphatically **not** the
symmetric power `SⁿV`: no symmetrization projector, no `Sym`/`SymmetricPower` type appears.
So the theorem's target is the tensor power, not the symmetric power.

**Faithfulness of the hypotheses (for the form actually proved).**
- `hρ : Function.Injective ρ` is the correct rendering of "the map `G → GL(V)` is injective"
  (`ρ : G → GL(V)` as a `Representation`, injective as a function). Faithful.
- `hσ : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule` is the project-standard encoding of
  "`σ` is an irreducible representation": `σ.asModule` is the `MonoidAlgebra ℂ G`-module of
  `σ`, and `IsSimpleModule` is `Nontrivial` + only `⊥/⊤` submodules. Faithful.
- `[Group G] [Fintype G]` gives the "finite group". Faithful.

**Faithfulness of the "occurs inside V^{⊗n}" conclusion.** "`W` occurs inside `V^{⊗n}`" is
rendered as the existence of a **nonzero** `G`-equivariant `φ : W → ⨂ⁿV`
(`∀ g, φ ∘ₗ σ g = diagTensorPow ρ n g ∘ₗ φ`). Because `σ` is simple, `ker φ` is a
subrepresentation, so `φ ≠ 0 ⟹ ker φ = ⊥ ⟹ φ` injective (Schur), hence `W` embeds as a
subrepresentation of `⨂ⁿV`. This is a faithful encoding of "occurs inside", and the module
docstring (lines 15-17) states this reasoning explicitly.

**Coverage classification.** The theorem proves the `V^{⊗n}` half only. The book's headline
result is the strictly stronger `SⁿV` statement: in characteristic 0 `SⁿV` is a
`G`-direct-summand of `V^{⊗n}` (via the symmetrization projector), so `W ↪ SⁿV ⟹ W ↪ V^{⊗n}`
but **not** conversely. Proving `W ↪ V^{⊗n}` does not establish `W ↪ SⁿV`. Therefore:

> **`covered_partial`.** The proved theorem is the book's own weaker "and hence inside
> `V^{⊗n}`" corollary; the primary `SⁿV` result (which the hint's `SV → F(G,ℂ)` map is
> built to deliver) is **not** formalized.

**Docstring honesty (per the issue's "do not silently upgrade" instruction).** The module
header restates the book verbatim (title "…in symmetric powers", line 8 `SⁿV`), but the
`## Formalization` section (lines 11-18) is **explicit** that only the `V^{⊗n}` form is
formalized ("We formalize the 'hence inside `V^{⊗n}`' form (the symmetric-power form implies
it)"). So the file does not silently over-claim `SⁿV`; the scope reduction is disclosed in
place. No docstring edit made (report-only). Minor observation: the one-line title
("…in symmetric powers") reads as the stronger claim in isolation; a future doc pass could
soften it to "…in a tensor power", but this is not a fidelity gap given the explicit
Formalization note directly below it.

## 2. Non-vacuity

**Hypotheses simultaneously satisfiable.** Take any nontrivial finite `G` with its regular
representation `V` (faithful) and any irreducible `σ` — e.g. `G = ℤ/2`, `V` the regular rep
(`Injective ρ` holds), `σ` the sign rep (`IsSimpleModule`). None of the typeclass/`Prop`
hypotheses is contradictory, so the theorem is not vacuously true by unsatisfiable premises.

**`φ ≠ 0` is a genuine constraint.** Without it the conclusion is trivial: the zero map
`0 : W → ⨂ⁿV` intertwines any pair of representations. Requiring `φ ≠ 0` is exactly what
makes the statement assert a real occurrence, and the proof discharges it via a strictly
positive multiplicity `0 < finrank (IntertwiningMap σ (diagTensorPow ρ n))` for some `n`,
obtained by the character/power-sum contradiction — not by any trivial witness.

**`diagTensorPow` is a genuine construction, not a placeholder.** Its `def` body is real
data (`PiTensorProduct.map (fun _ => ρ g)`) with honest `map_one'` (`PiTensorProduct.map_id`)
and `map_mul'` (`PiTensorProduct.map_comp`) proofs — it satisfies the "Definitions Must Be
Constructed" rule, no `sorry` in the object.

**Supporting infrastructure is real and correctly typed** (`#check`-confirmed):
- `Representation.IntertwiningMap ρ σ` is a genuine `Type` (the space of `G`-equivariant maps),
  finite-dimensional, whose `finrank` is the intertwiner multiplicity.
- `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` is the honest multiplicity
  formula `|G|⁻¹ Σ_g χ_σ(g) χ_ρ(g⁻¹) = finrank (IntertwiningMap ρ σ)`.
- `Representation.char_one ρ : ρ.character 1 = finrank ℂ V` (used to isolate the `g = 1` term).
- `IsSimpleModule` is Mathlib's standard simplicity predicate.

**The key analytic lemma is real.** `ρ_eq_one_of_character_eq_finrank` (`χ_V(g) = dim V ⟹ ρ g = 1`)
is fully proved by matrix unitarization (averaged Hermitian form `H`, CFC square root `L`,
`U = L (ρ g) L⁻¹` standard-unitary with trace `= dim`, then the elementary
column-length argument `eq_one_of_conjTranspose_mul_self_eq_one_of_trace_eq_card`). This is
where faithfulness is actually consumed: only `g = 1` has `χ_V(g) = dim V`, so the
polynomial `∏_{μ≠d}(X-μ)` isolates the `g = 1` term and forces `finrank W ≠ 0` into a
contradiction. Genuine mathematical content, no shortcut.

## 3. Axiom cleanliness

`lake build EtingofRepresentationTheory.Chapter4.Problem4_12_10` exits 0. `#print axioms`:

```
'Etingof.Problem4_12_10'                depends on axioms: [propext, Classical.choice, Quot.sound]
'diagTensorPow'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'character_diagTensorPow'               depends on axioms: [propext, Classical.choice, Quot.sound]
'trace_piTensorProduct_map_const'       depends on axioms: [propext, Classical.choice, Quot.sound]
'ρ_eq_one_of_character_eq_finrank'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

All subsets of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no custom axioms.
The file is genuinely `sorry`-free (the only `sorry` token is inside a docstring).

## Verdict

**`verified` / `covered_partial`.** The theorem `Etingof.Problem4_12_10` faithfully and
non-vacuously proves the book's weaker "and hence inside `V^{⊗n}`" corollary: any
irreducible `σ` admits a nonzero `G`-equivariant embedding into the diagonal tensor power
`⨂ⁿV` for some `n`, with faithfulness genuinely consumed and `φ ≠ 0` a real constraint.
The book's primary result — occurrence inside the **symmetric** power `SⁿV` — is strictly
stronger (`SⁿV` a `G`-summand of `V^{⊗n}` in char 0) and is **not** formalized. Coverage is
therefore partial. The docstring discloses the scope reduction rather than over-claiming, so
this is a genuine coverage gap in the formalization, not a misleading statement.

Follow-up `feature` issue **#7285** filed for the missing `SⁿV` half. Report-only: no Lean
proof modified.
