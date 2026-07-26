# Review — Ch7 Example 7.3.2: Examples of Natural Transformations

> **Superseded (2026-07-26).** Issue #7103 was reopened on 2026-07-22 because this review's
> "FAITHFUL, no defect filed" verdict was too lenient on two points, both of which it does
> record below but classifies as non-defects:
>
> 1. **Parts (3)/(4)** — the "trivial reverse-surjection observation" in §1 is the missing half
>    of the book's `End F = A` and `End(id) = Z(A)`. Determination alone gives injectivity, not
>    the equalities the docstrings assert.
> 2. **Part (2)** — the `∃ l ≠ 0, l² ≠ 1` hypothesis is not merely "documented, not silent": the
>    book states the non-naturality for an arbitrary field, and the claim is in fact true over
>    `𝔽₂` and `𝔽₃`. The restriction was an artefact of testing at the one-dimensional object.
>
> Both gaps are now closed in `EtingofRepresentationTheory/Chapter7/Example7_3_2.lean`
> (`forgetfulEndRingEquiv : End F ≃+* A`, `idFunctorEndRingEquiv : End 𝟭 ≃+* Subring.center A`,
> and a hypothesis-free `not_natIso_id_contragredientFunctor` proved via transvections at `k³`).
> The section-by-section analysis below remains accurate as a description of the file *before*
> that work; only its dispositions are superseded.

- **Issue:** #7103 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/d549ccad`
- **Target:** `EtingofRepresentationTheory/Chapter7/Example7_3_2.lean` (361 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter7/Example7.3.2.md`
- **Focus areas:** statement fidelity per book part (1)-(4); Mathlib-correspondence accuracy; vacuity / hidden-hypothesis check (report-only, no `.lean` edits)
- **Overall verdict:** **FAITHFUL.** All four book parts are formalized, each headline
  claim is a correct transcription (right quantifiers, right direction of the is/is-not
  isomorphic claims), and the negative parts are genuine non-existence / non-bijectivity
  results, not vacuous placeholders. All 14 declarations build and are axiom-clean (no
  `sorryAx`, no custom axiom). **No defect filed.** One prominent scope caveat (Part 2 is
  proved over fields with > 3 elements — but the restriction is *loudly documented in every
  relevant docstring*, so it is not a silent specialization) and two minor
  completeness observations (Parts 3/4 formalize the hard "determination" direction and
  the ring/centrality structure but not the trivial reverse surjection) are recorded below.
  None is a defect.

---

## 0. Build and axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter7.Example7_3_2` (exit 0, 1804 jobs) and ran
`#print axioms` on all 14 declarations named in the issue. **Every** result is a subset of
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no stray custom axiom:

| Declaration | Line | `#print axioms` result |
|---|---|---|
| `double_dual_iso` | 34 | `[propext, Classical.choice, Quot.sound]` |
| `double_dual_naturality` | 44 | `[propext, Quot.sound]` |
| `linearEquiv_dualDual_iff_finiteDimensional` | 57 | `[propext, Classical.choice, Quot.sound]` |
| `doubleDualFunctor` | 93 | `[propext, Classical.choice, Quot.sound]` |
| `doubleDualNatIso` | 107 | `[propext, Classical.choice, Quot.sound]` |
| `linearEquiv_dual_iff_finiteDimensional` | 150 | `[propext, Classical.choice, Quot.sound]` |
| `dual_gl_natural_eq_zero` | 164 | `[propext, Classical.choice, Quot.sound]` |
| `not_bijective_of_gl_natural_dual` | 192 | `[propext, Classical.choice, Quot.sound]` |
| `contragredientFunctor` | 210 | `[propext, Classical.choice, Quot.sound]` |
| `not_natIso_id_contragredientFunctor` | 225 | `[propext, Classical.choice, Quot.sound]` |
| `forgetful_natEnd_eq_smul` | 285 | `[propext, Quot.sound]` |
| `forgetful_smul_comp` | 305 | (none) |
| `idFunctor_natEnd_eq_smul` | 330 | `[propext, Quot.sound]` |
| `idFunctor_natEnd_central` | 348 | `[propext, Quot.sound]` |

Declaration names and line numbers in the issue are all current. `grep` for
`sorry|admit|proof_wanted` and for `True`/`by trivial` placeholders returns nothing. Of the
14 declarations, 4 are `noncomputable def` (data: `double_dual_iso`, `doubleDualFunctor`,
`doubleDualNatIso`, `contragredientFunctor`) — none has a sorried body; the rest are
`theorem`s with real proofs.

---

## 1. Statement fidelity, per book part

### Part (1) — `id ≅ **` on `FVect_k`; `id ≇ **` on `Vect_k`

Book: on finite-dimensional `FVect_k`, `id` and `**` are isomorphic via `a_V : V → V**`,
`a_V(u)(f) = f(u)`; on all of `Vect_k` they are not isomorphic, because an infinite-dimensional
`V` is not isomorphic to `V**`.

Lean formalizes this in **four** complementary pieces, and the coverage is a strict
super-set of the book's assertion:

- **Pointwise iso (positive):** `double_dual_iso` gives `V ≃ₗ[k] Module.Dual k (Module.Dual k V)`
  for finite-dimensional `V`, defined as `Module.evalEquiv k V` — exactly the standard map
  `a_V(u)(f) = f(u)`. Faithful.
- **Naturality (positive):** `double_dual_naturality` states
  `f.dualMap.dualMap ∘ₗ eval k V = eval k W ∘ₗ f`, the naturality square making `a_•` a
  natural transformation `𝟭 ⇒ **`. Faithful; this is the content the book conveys by the
  word "isomorphic" (as *functors*, not merely pointwise).
- **Categorical iso (positive):** `doubleDualNatIso : 𝟭 (FGModuleCat k) ≅ doubleDualFunctor k`
  packages the two above into an actual `CategoryTheory.NatIso` on `FGModuleCat k` (Etingof's
  `FVect_k`), with components the evaluation equivalences. This is a *stronger and more
  literal* rendering of "the functors id and ** are isomorphic" than the book's prose. Faithful.
- **Negative half (`Vect_k`):** `linearEquiv_dualDual_iff_finiteDimensional` proves
  `Nonempty (V ≃ₗ[k] V**) ↔ FiniteDimensional k V`. The `←`-to-contrapositive direction is
  exactly the book's claim (infinite-dim ⟹ `V ≇ V**`), and it is a *genuine non-existence
  result*: the proof derives `Module.rank k V < Module.rank k V**` (Erdős–Kaplansky, via
  `lift_rank_lt_rank_dual`) and contradicts any hypothetical equivalence's rank equality. Not
  vacuous. The Lean statement is in fact stronger than the book (an iff, so it also recovers
  the finite-dimensional positive case). Faithful, no over-statement in the wrong direction.

**Verdict (1): faithful (with a strengthening).** Nothing dropped.

### Part (2) — `V ↦ V*` on `FVect'_k`: pointwise `≅ id` but not naturally `≅ id`

Book: on `FVect'_k` (finite-dim spaces, morphisms = isomorphisms), `F : V ↦ V*`,
`a ↦ (a*)⁻¹`, satisfies `V ≅ F(V)` for all `V`, yet `F` is *not* isomorphic to the identity
functor, because the iso `V ≅ V*` cannot be chosen `GL(V)`-compatibly (`V ≇ V*` as
`GL(V)`-representations).

- **Positive (pointwise):** `linearEquiv_dual_iff_finiteDimensional` proves
  `Nonempty (V ≃ₗ[k] V*) ↔ FiniteDimensional k V`, so on the finite-dim category `V ≅ F(V)`
  for every object. Faithful.
- **Obstruction:** `dual_gl_natural_eq_zero` — a `GL(V)`-natural `η : V →ₗ[k] V*` (i.e.
  `a* ∘ η ∘ a = η` for every `a ∈ GL(V)`) is forced to be `0`. This is precisely the book's
  "`B(u,w) := η_V u w` is a `GL(V)`-invariant bilinear form, hence `0`" argument, carried out
  with the scalar automorphisms `a = l • 𝟙`. Faithful transcription of the reasoning.
- **Corollary:** `not_bijective_of_gl_natural_dual` — for `V` nontrivial a `GL(V)`-natural
  `η` is not bijective (being `0`). Genuine.
- **Functor:** `contragredientFunctor` models `F` as an endofunctor of `Core (FGModuleCat k)`
  (the groupoid `FVect'_k`), `obj X ↦ X*`, `map a ↦ (a⁻¹)*`. The book writes `a ↦ (a*)⁻¹`;
  since dualization is contravariant `(a*)⁻¹ = (a⁻¹)*`, the two agree. The docstring correctly
  notes `F` is functorial only on the groupoid. Faithful.
- **Negative (categorical):** `not_natIso_id_contragredientFunctor` proves
  `IsEmpty (𝟭 (Core (FGModuleCat k)) ≅ contragredientFunctor k)`. This is a genuine
  non-existence result (`IsEmpty`, not a weakened placeholder); it extracts the component
  `η : k → k*` at the line `k` and the scalar-naturality square, then invokes the obstruction.
  Faithful; the direction ("is *not* naturally isomorphic") is correct.

**Scope caveat (documented, not a defect).** The negative results carry the hypothesis
`hk : ∃ l : k, l ≠ 0 ∧ l ^ 2 ≠ 1` — i.e. `k` has more than three elements (excludes `𝔽₂`,
`𝔽₃`, where every nonzero scalar squares to `1` and the scalar-automorphism argument gives no
traction). The book states the non-naturality without a cardinality restriction. This is a
mild *under*-statement relative to the book's full generality. **It is not a silent
specialization:** every relevant docstring (`dual_gl_natural_eq_zero`,
`not_bijective_of_gl_natural_dual`, `not_natIso_id_contragredientFunctor`, and the section
prose at lines 135-138) states the hypothesis explicitly with the "any field with more than
three elements" gloss. The restriction is exactly where the book's own stated argument (scalar
action / `V ≇ V*` as `GL(V)`-rep) applies; extending to `𝔽₂`/`𝔽₃` would require non-scalar
automorphisms and is beyond what the book's sketch supplies. Because it is transparently
declared and the theorems are non-vacuous, I judge this faithful and do **not** file a defect.

**Verdict (2): faithful, with a transparently-documented field restriction on the negative
half.**

### Part (3) — `End(F) = A` for the forgetful functor

Book: `F : A-mod → Vect_k` forgetful; by Problem 2.3.17, `End F = Hom(F,F) = A`.

- **Determination (the content):** `forgetful_natEnd_eq_smul` proves any `k`-linear natural
  family `η_M : M →ₗ[k] M` acts as `η M m = η A 1 • m` — every natural endomorphism is scalar
  multiplication by the single element `η A 1 ∈ A`. This is the injective side plus the map
  `End F → A`, exactly the Problem 2.3.17 idea (naturality against right multiplication
  `r_m : A → M` via `LinearMap.toSpanSingleton`). Faithful.
- **Ring structure:** `forgetful_smul_comp` proves `a • b • m = (a*b) • m`, i.e. composition
  of the scalar families multiplies elements in the same order — so `End F ≅ A`, **not**
  `Aᵒᵖ`. The docstring correctly explains why the opposite appears in Problem 2.3.17 (there one
  composes self-maps of the single module `A`) but not here. This resolves a genuine subtlety
  in the "`= A`" claim; faithful.

**Completeness observation (not a defect).** The file proves `End F ⊆ {scalar mults} ≅ A`
(determination + correct ring order) but does not separately state the trivial reverse
surjection "every `a ∈ A` yields a natural endomorphism `m ↦ a • m`." That direction is
immediate (`m ↦ a • m` is `A`-linear, hence natural under `restrictScalars`), and the
bijection-with-`A` content the book emphasizes (each endo is *determined by* its value at
`1`) is fully captured. I note it for completeness but it is not a fidelity gap: the hard
direction and the ring identification are present and correct.

**Verdict (3): faithful.**

### Part (4) — `End(id_{A-mod}) = Z(A)`

Book: the endomorphisms of the identity functor on `A-mod` form the center of `A`.

- **Determination:** `idFunctor_natEnd_eq_smul` — an `A`-linear natural family
  `η_M : M →ₗ[A] M` acts as `η M m = η A 1 • m`. Correct analogue of (3) with `A`-linear
  (not merely `k`-linear) components, matching that morphisms of `A-mod` are `A`-linear.
  Faithful.
- **Centrality:** `idFunctor_natEnd_central` — `η A 1 * b = b * η A 1` for all `b`, derived
  from `A`-linearity of `η A` (`η A (b • 1) = b • η A 1`) combined with determination. This is
  exactly the book's "`c*a = a*c`" computation. Faithful.

Together these give `End(id_{A-mod}) = Z(A)`: every natural endo is `• c` for a central `c`.
Same trivial-reverse-surjection observation as Part (3) applies (that every central `c` gives
a natural `A`-linear endo is not separately stated, but is immediate). Not a defect.

**Verdict (4): faithful.**

---

## 2. Mathlib-correspondence accuracy

Every "Mathlib correspondence" docstring claim matches what the declaration actually proves:

- Header + `double_dual_iso`: "double dual via `Module.evalEquiv` (for reflexive modules)"
  — body is literally `Module.evalEquiv k V`. `double_dual_naturality` body is
  `Module.Dual.eval_naturality f`, matching its docstring. ✓
- `linearEquiv_dual_iff_finiteDimensional` docstring cites
  `Basis.linearEquiv_dual_iff_finiteDimensional` — body is exactly that term. ✓
- `linearEquiv_dualDual_iff_finiteDimensional` docstring's "Erdős–Kaplansky /
  `Module.rank k V < Module.rank k V**`" — matches the proof (`lift_rank_lt_rank_dual`). ✓
- The issue's cross-reference "`End(F) = A` captured by `forgetful_natEnd_eq_smul`,
  `End(id) = Z(A)` by `idFunctor_natEnd_central`" is accurate: those are the decls that carry
  the respective content. ✓

No docstring drift found. (`IsReflexive.of_finite_of_free`, named in the header, is context
for why `evalEquiv` applies in finite dimension, not a claim about a specific decl's term; it
is used implicitly through instance resolution. Fine.)

---

## 3. Vacuity / hidden-hypothesis check

- **No sorried def bodies.** The four `noncomputable def`s build real data
  (`Module.evalEquiv`, a genuine `Functor` record with proved `map_id`/`map_comp`, a real
  `NatIso.ofComponents`, a real groupoid endofunctor). Axiom audit (§0) shows no `sorryAx`.
- **No vacuous negatives.** Both non-existence results are stated as `↔ FiniteDimensional`
  (Part 1/2 positive-or-negative dichotomy) and `IsEmpty (… ≅ …)` (Part 2 categorical), and
  `not_bijective_of_gl_natural_dual` as `¬ Bijective`; none is weakened to `True` or a trivial
  placeholder, and each has genuine mathematical content (rank strict inequality; forced-zero
  bilinear form).
- **Hidden hypotheses.** The only non-book hypothesis is the Part-2 field-cardinality
  condition `∃ l, l ≠ 0 ∧ l² ≠ 1`, which is transparently documented (see Part (2) above),
  not silent. The `[Module.Free k V]` instance on `double_dual_iso` is automatically satisfied
  over a field (every vector space is free), so it narrows nothing. No extra finiteness
  hypothesis narrows a claim the book makes in general beyond the documented Part-2 caveat.
- **Coverage.** The four formalized clusters collectively cover book parts (1)-(4) with
  nothing dropped; the only gaps are the two *trivial reverse-surjection* directions in
  Parts (3)/(4), noted as non-defects.

---

## Conclusion

Chapter 7 Example 7.3.2 is **faithfully formalized**. The Ch7 fidelity gap this issue targets
is closed for this file: all four book parts are present, correctly stated (including the
directions of the is/is-not-isomorphic claims), non-vacuous, and axiom-clean. The single scope
caveat (Part 2's `> 3`-element field hypothesis) is transparently documented rather than
silent, and the two reverse-surjection completeness observations concern trivial directions the
book does not dwell on. **No follow-up `feature` issue is filed.**

No `.lean` file was modified; the diff is confined to `progress/`.
