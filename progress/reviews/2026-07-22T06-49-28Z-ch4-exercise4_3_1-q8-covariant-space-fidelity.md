# Stage 3.7 audit — Exercise 4.3.1 (2-dim irreducible of `Q₈` in a covariant function space)

**Issue:** #7274 (statement-fidelity & non-vacuity audit; report-only).
**File:** `EtingofRepresentationTheory/Chapter4/Exercise4_3_1.lean` (258 lines).
**Blob:** `blobs/Chapter4/Exercise4.3.1.md`.
**HEAD:** `947ddc35` (`origin/main`).
**Verdict:** **VERIFIED** — statement-faithful (via the mathematically-forced convention
correction, see key check), non-vacuous, `covered_full`.

## Build / axiom check

- `lake build EtingofRepresentationTheory.Chapter4.Exercise4_3_1` exits 0
  (`✔ [8581/8581] Built ... (3.3s)`), no warnings.
- `#print axioms` on all three headline theorems returns exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, axiom-clean:
  - `Etingof.Exercise4_3_1.covariantSubspace_invariant`
  - `Etingof.Exercise4_3_1.covariantSubspace_finrank`
  - `Etingof.Exercise4_3_1.covariantSubspace_irreducible`

## Book text

> **Exercise 4.3.1.** Show that the 2-dimensional irreducible representation of `Q₈` can
> be realized in the space of functions `f : Q₈ → ℂ` such that `f(gi) = √(-1)·f(g)` (the
> action of `G` is by right multiplication, `g ∘ f(x) = f(xg)`).

## Modelling choices

- `Q₈` = Mathlib's `QuaternionGroup 2` (order 8); `i = a 1` (order 4, matching `rhoI`
  in the imported `Example4_3_Q8`); `√(-1) = Complex.I`.
- Right-translation action `(g ∘ f)(x) = f(x·g)` is `rightRegular` (line 42) — faithful
  to "the action of `G` is by right multiplication". `rightRegular_apply` (rfl) and the
  `map_one'`/`map_mul'` bundle confirm it is a genuine `Representation ℂ (QuaternionGroup 2)`.
- **Covariance convention.** The book writes the **right**-covariance `f(g·i) = √(-1)·f(g)`.
  The Lean `covariantSubspace` (line 59) is instead cut out by the **left**-covariance
  `f(a 1 · g) = I · f g`. The module docstring (lines 17–22) asserts these are "the
  standard equivalent conventions for the induced representation `Ind_{⟨i⟩}^{Q₈} χ`,
  `χ(i) = √(-1)`". The correctness of this substitution is the key check below.

## Headline declarations

```lean
theorem covariantSubspace_invariant (g : QuaternionGroup 2)
    (f : QuaternionGroup 2 → ℂ) (hf : f ∈ covariantSubspace) :
    rightRegular g f ∈ covariantSubspace

theorem covariantSubspace_finrank :
    Module.finrank ℂ covariantSubspace = 2

theorem covariantSubspace_irreducible
    (U : Submodule ℂ (QuaternionGroup 2 → ℂ))
    (hUle : U ≤ covariantSubspace)
    (hUinv : ∀ g : QuaternionGroup 2, ∀ f ∈ U, rightRegular g f ∈ U) :
    U = ⊥ ∨ U = covariantSubspace
```

## Object faithfulness — the key check (left- vs right-covariance)

The book pairs a **right**-covariance condition `f(g·i) = √(-1)·f(g)` with the **right**-
translation action `(g ∘ f)(x) = f(x·g)`. I checked whether that literal pairing even
yields a subrepresentation. It does **not**:

- In `QuaternionGroup 2`, conjugation flips the sign of `i`: machine-checked
  `(xa 0)⁻¹ * a 1 * xa 0 = a 3` (i.e. `j⁻¹ i j = i³ = -i`), equivalently
  `a 1 * xa 0 = xa 0 * a 3` and `a 1 * xa 0 ≠ xa 0 * a 1` (all `by decide`).
- Consequently, for `h = xa 0 (= j)` and `f` in the book's literal right-covariance set,
  `(h ∘ f)(g·i) = f(g·i·h) = f(g·h·i³) = (√-1)³·f(g·h) = -√(-1)·f(g·h)`, whereas
  invariance would require `+√(-1)·f(g·h)`. The sign mismatch (nonzero whenever
  `f(g·h) ≠ 0`) shows the book's **literal** subspace is *not* invariant under the
  right-regular action.

The mathematically correct realization of the induced representation with a **right**-
translation action is the **left**-covariance space `{f : f(h·g) = χ(h)·f(g), h ∈ ⟨i⟩}`
— exactly `covariantSubspace`. `covariantSubspace_invariant` proves this invariance
(`f(a1·(h·g)) = I·f(h·g)` via `mul_assoc`), which is the correct and provable statement.

So the Lean file's left/right substitution is not an arbitrary weakening: it is the
mathematically **forced correction** of a slightly loose book statement, and it realizes
the intended object — the induced representation `Ind_{⟨i⟩}^{Q₈} χ`, `χ(i) = i`, of
dimension `[Q₈:⟨i⟩] = 2`. Because `⟨i⟩ ⊴ Q₈` (index 2) and the conjugate character
`χ^j(i) = χ(i³) = i³ = -i ≠ χ(i)`, this induced representation is irreducible, hence *the*
(unique up to iso) 2-dimensional irreducible of `Q₈`. The two nontrivial characters
`χ(i) = ±i` are conjugate and induce the same 2-dim irrep, so the specific sign of `√-1`
is immaterial to which representation is realized. Faithful rendering of the exercise's
mathematical intent. (Recorded transparently for human review: the formalized *set of
functions* is the equivalent left-covariant convention, not the book's literal
right-covariant symbols.)

## Conclusion faithfulness

"Realize the 2-dimensional irreducible representation" decomposes into three obligations,
each discharged:

1. **It is a subrepresentation** — `covariantSubspace_invariant`: closed under
   `rightRegular g` for every `g`. Genuine subrep (the `Submodule` bundles `add`/`zero`/
   `smul` closure). ✓
2. **It is 2-dimensional** — `covariantSubspace_finrank`: `finrank ℂ = 2`, via the
   explicit linear equiv `covEquiv : covariantSubspace ≃ₗ[ℂ] (Fin 2 → ℂ)`,
   `f ↦ ![f (a 0), f (xa 0)]`, whose inverse is the genuinely-constructed
   `liftFun` (no sorry in the `def`; `liftFun_mem` proves membership). The two free
   values `f(a 0)`, `f(xa 0)` with the other six determined by covariance
   (`covariantSubspace_values`, `covariantSubspace_eq_liftFun`) faithfully give dim 2. ✓
3. **It is irreducible** — `covariantSubspace_irreducible`: every `Q₈`-invariant
   `U ≤ covariantSubspace` is `⊥` or all of it. `hUinv` is genuine `G`-invariance under
   `rightRegular`. The proof extracts a nonzero `f`, and from any nonzero member produces
   a second linearly-independent member inside `U` (via a nonzero `2×2` coordinate
   determinant using `rightRegular (xa 0) f` or `rightRegular (a 1) f`), forcing
   `finrank U ≥ 2 = finrank covariantSubspace` and hence `U = covariantSubspace`. This is
   the real irreducibility statement, not "indecomposable" or "no *scalar*-invariant
   subspace". ✓

Together (2-dimensional + irreducible + `Q₈` has a unique 2-dim irrep) these pin down the
object as *the* 2-dim irreducible, so `covered_full`. An explicit isomorphism to the
concrete `Example4_3_Q8.repLin` (mentioned in the docstring) is not stated, but is not
required by the exercise and is implied by uniqueness of the 2-dim irrep.

## Non-vacuity

- **The space is genuinely nonzero.** `covariantSubspace_finrank = 2` rests on the real
  equiv `covEquiv` with `invFun` built from `liftFun` (a constructed `def`, not sorry),
  so `covariantSubspace ≅ ℂ²` is a genuine 2-dim space, not the zero module. The
  invariance and irreducibility statements are therefore about a nontrivial object. ✓
- **`covariantSubspace_invariant`** — hypothesis `f ∈ covariantSubspace` is satisfiable
  (e.g. `liftFun 1 0`), not vacuous; conclusion is a genuine membership. ✓
- **`covariantSubspace_irreducible`** — the `U = covariantSubspace` disjunct is genuinely
  reachable (`U = covariantSubspace` itself satisfies the hypotheses), and the `U = ⊥`
  disjunct is reached by an actual argument, not vacuously; `hUle` and `hUinv` are real
  constraints, both used. Not a `True`-typed or trivially-dischargeable hypothesis
  anywhere. ✓
- No hypothesis is over-strong or degenerate; `Complex.I ≠ 0` (used at line 254) keeps the
  covariance character nontrivial. ✓

## Verdict

**VERIFIED**, `covered_full`. The three theorems faithfully and non-vacuously establish
that the 2-dimensional irreducible representation of `Q₈` is realized in a covariant
function space under the right-translation action: subrepresentation + 2-dimensional +
irreducible. The one deviation from the book's literal symbols — left-covariance
`f(i·g) = √-1·f(g)` in place of the written right-covariance `f(g·i) = √-1·f(g)` — is not
a gap but a **mathematically necessary correction**: the book's literal right-covariance /
right-action pairing is not even invariant (machine-verified sign flip
`j⁻¹ i j = -i`), and the left-covariant space is the correct realization of the same
induced representation `Ind_{⟨i⟩}^{Q₈} χ`. No `sorryAx`; no repair issue filed; no `.lean`
edits.
