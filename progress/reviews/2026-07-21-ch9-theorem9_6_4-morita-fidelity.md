# Ch9 review: Theorem 9.6.4 (Morita equivalence) — statement fidelity + non-vacuity

**Issue:** #7145 (review) · **Date:** 2026-07-21 (UTC) · **Verdict: FAITHFUL**

Report-only statement-fidelity and non-vacuity audit of Chapter 9's categorical
flagship, **Theorem 9.6.4 (Morita equivalence)**, in
`EtingofRepresentationTheory/Chapter9/Theorem9_6_4.lean` (538 lines, sorry-free on
`main`). Checked against `blobs/Chapter9/Theorem9.6.4.md`,
`blobs/Chapter9/Discussion_before_Theorem9.6.4.md`,
`blobs/Chapter9/Definition9.6.1.md`, `blobs/Chapter9/Definition9.6.2.md`, and
`blobs/Chapter9/Problem9.6.5.md`. `lake build
EtingofRepresentationTheory.Chapter9.Theorem9_6_4` exits 0 (only pre-existing
unrelated lint). **No Lean changes made; no defect found.**

## The book statement

- **Setup (`Discussion_before_Theorem9.6.4`):** `𝒞` a finite abelian category with a
  projective generator `P`; `B = End(P)ᵒᵖ` (a finite dimensional algebra acting on the
  right on `P`); `B‑fmod` the category of finite dimensional left `B`-modules; the
  functor `F : 𝒞 → B‑fmod`, `F(M) = Hom(P, M)`.
- **Theorem 9.6.4:** *`F` is an equivalence of categories. Thus any finite abelian
  category over a field `k` is equivalent to the category of modules over a finite
  dimensional `k`-algebra.*
- **Definition 9.6.1 (finite):** enough projectives + finitely many simples (with the
  §9.6 standing finite-length assumption).
- **Definition 9.6.2 (progenerator):** projective + every object is a quotient of a
  multiple of `P`.

## 1. Axiom cleanliness (non-vacuity)

`#print axioms` on all eleven headline declarations named in the issue. **Every one
reports exactly `[propext, Classical.choice, Quot.sound]`** — no `sorryAx`, no custom
`axiom`. Because a sorried `def`/`instance`/`noncomputable def` body injects `sorryAx`,
the clean result on the data constructions directly certifies their bodies are genuinely
built, not stubbed. In particular the load-bearing functor `preadditiveCoyonedaObjFG`
(a sorried body here would make the whole equivalence vacuous) is axiom-clean.

| Declaration | Kind | Axioms |
|---|---|---|
| `Etingof.Theorem_9_6_4` | theorem | propext, Classical.choice, Quot.sound |
| `Etingof.Theorem_9_6_4_corollary` | theorem | propext, Classical.choice, Quot.sound |
| `Etingof.Theorem_9_6_4_of_isNoetherian` | theorem | propext, Classical.choice, Quot.sound |
| `Etingof.Theorem_9_6_4_corollary_of_isNoetherian` | theorem | propext, Classical.choice, Quot.sound |
| `Etingof.isNoetherianRing_endOp_of_overField` | theorem | propext, Classical.choice, Quot.sound |
| `Etingof.IsProgenerator.preadditiveCoyonedaObjFG` | noncomputable def | propext, Classical.choice, Quot.sound |
| `Etingof.IsProgenerator.essSurj_preadditiveCoyonedaObjFG` | instance | propext, Classical.choice, Quot.sound |
| `Etingof.IsProgenerator.full_preadditiveCoyonedaObj` | instance | propext, Classical.choice, Quot.sound |
| `Etingof.IsProgenerator.faithful_preadditiveCoyonedaObj` | instance | propext, Classical.choice, Quot.sound |
| `Etingof.IsProgenerator.finite_hom_module` | instance | propext, Classical.choice, Quot.sound |
| `Etingof.IsProgenerator.isSeparator` | theorem | propext, Classical.choice, Quot.sound |

No `sorry`/`admit` appears in `Theorem9_6_4.lean` or its Ch9 dependency files
(`Definition9_6_1.lean`, `Definition9_6_2.lean`, `Introduction_9_6.lean`).

## 2. Statement fidelity

### (a) The functor is genuinely `Hom(P, −)` into f.g. `B`-modules

`preadditiveCoyonedaObjFG` (lines 216–231) has object `X ↦ ⟨(preadditiveCoyonedaObj
P).obj X, finite_hom_module X⟩` and `map f ↦ (preadditiveCoyonedaObj P).map f`. The
underlying module is exactly Mathlib's `preadditiveCoyonedaObj P`, i.e. `Hom(P, X)` with
its `(End P)ᵐᵒᵖ`-action; the FG version only *restricts the codomain* to
`FGModuleCat (End P)ᵐᵒᵖ` (finitely generated modules), which is legitimate because
`finite_hom_module` proves `Module.Finite (End P)ᵐᵒᵖ (P ⟶ X)` for every `X` (via
`P^n ↠ X`, projectivity, and `Hom(P,P^n) ≅ (End P)^n`). This is faithfully `F(M) =
Hom(P, M)`. The header's own "cannot be essentially surjective" remark correctly
motivates restricting to `FGModuleCat` rather than all modules — matching the book's
`B‑fmod` (finite dimensional `B`-modules), which for a finite dimensional `B` coincide
with finitely generated `B`-modules.

### (b) `ᵒᵖ` vs `ᵐᵒᵖ`: `B = End(P)ᵒᵖ` is faithfully `(End P)ᵐᵒᵖ`

The linearity lemma `hlin` (lines 83–89) discharges `f.hom.map_smul (op s) g` as a proof
that `op s • g = s ≫ g` — i.e. an element `op s : (End P)ᵐᵒᵖ` acts on `g : Hom(P, X)` by
**precomposition** `s ≫ g`. That is precisely the right `End(P)`-module = left
`End(P)ᵒᵖ`-module structure the book puts on `Hom(P, M)` (the book says `B` acts on the
right on `P`). Mathlib's multiplicative opposite `(End P)ᵐᵒᵖ` is the ring-opposite
`End(P)ᵒᵖ`, so the algebra `B` is rendered faithfully. (This typechecks/compiles, so the
`op s • g = s ≫ g` defeq is real, not asserted.)

### (c) The conclusion is a genuine equivalence, not full+faithful only

`Theorem_9_6_4` (and the `_of_isNoetherian` engine it wraps) concludes
`hp.preadditiveCoyonedaObjFG.IsEquivalence`, whose fields are `essSurj`, `faithful`, and
`full` (lines 482–495) — the full `CategoryTheory.Functor.IsEquivalence`, from which an
actual `C ≌ FGModuleCat (End P)ᵐᵒᵖ` is produced by `asEquivalence` in the corollaries.
This is a genuine equivalence of categories, matching the book's "F is an equivalence,"
not a weaker claim. The three components mirror the book's Problem 9.6.5 proof
(faithful/full from `P` a projective separator; essential surjectivity from lifting a
presentation `R^m → R^n → M → 0` through `Hom(P,−)` and taking a cokernel in `𝒞`).

### (d) The corollary's "some finite dimensional `k`-algebra" is honestly witnessed

`Theorem_9_6_4_corollary` concludes `Nonempty (C ≌ FGModuleCat (End P)ᵐᵒᵖ)`. The witness
algebra is the **concrete** ring `(End P)ᵐᵒᵖ` — not `True` and not an opaque/vacuous
existential. It is a genuine finite dimensional `k`-algebra in this setting:
`isNoetherianRing_endOp_of_overField` (lines 456–466) uses
`FiniteDimensional k (End P)` from
`IsFiniteAbelianCategoryOverField.finiteDimensional_hom P P` (the §9.6 "check it!",
itself a real proof from finite length + `End(simple) = k`), and `FGModuleCat` of a
finite dimensional algebra is exactly the book's `B‑fmod`. Faithful.

### Hypothesis correspondence

- **`IsFiniteAbelianCategory`** (Definition 9.6.1): `extends Abelian C, EnoughProjectives
  C` + a `Fintype`-indexed family of simple representatives with `iso_of_simple` +
  `FiniteDimensionalOrder (Subobject X)` (finite length). This faithfully renders "enough
  projectives + finitely many simples," with the §9.6 finite-length standing assumption
  folded in and documented in the file.
- **`IsProgenerator`** (Definition 9.6.2): `extends Projective P` + `epiFromBiproduct`:
  every `X` admits an epi from a *finite* biproduct `⊕_{Fin n} P`. The book's "quotient
  of a multiple of `P`" is read as a finite multiple `Pⁿ`. In the finite abelian /
  finite-length setting this is the operative notion (and it is exactly what
  `exists_progenerator` below constructs), so it is a faithful specialization, not a
  weakening.
- **Over-a-field / Noetherian.** The book assumes only "finite abelian category over a
  field `k`," never a separate Noetherian hypothesis. The Lean flagship `Theorem_9_6_4`
  matches this: it takes `[IsFiniteAbelianCategoryOverField k C]` and *derives*
  `IsNoetherianRing (End P)ᵐᵒᵖ` internally (via `isNoetherianRing_endOp_of_overField`),
  delegating the mathematics to the more general ring-level engine
  `Theorem_9_6_4_of_isNoetherian`. The engine's bare `[IsNoetherianRing (End P)ᵐᵒᵖ]`
  hypothesis is a *generalization* (§9.7 reuse), not a hidden extra assumption on the
  book's theorem. Faithful.

## 3. Scope nuance (not a defect)

The book's second sentence — "*thus any finite abelian category over a field `k` is
equivalent to the category of modules over a finite dimensional `k`-algebra*" — is a
universally-quantified statement over finite abelian categories. The Lean
`Theorem_9_6_4_corollary` takes the progenerator `P` as an explicit input rather than
quantifying "there exists a fd algebra `B` with `C ≌ B‑fmod`." The missing
existential-over-`𝒞` half — that a finite abelian category *has* a progenerator — is
formalized **separately and completely** as `Etingof.exists_progenerator`
(`Chapter9/Exercise9_6_3.lean:189`, `∃ P, Nonempty (IsProgenerator P)`, witnessed by
`⊕ᵢ Projective.over (simpleObj i)`). Composing `exists_progenerator` with
`Theorem_9_6_4_corollary` yields the book's universal statement in full. This is a
modularity choice (existence proved in the Exercise that carries the book's own proof of
it), not an absent piece — worth recording so a reader does not mistake the `P`-as-input
corollary for a strictly weaker claim.

## Verdict

**FAITHFUL.** All eleven headline declarations are axiom-clean
(`[propext, Classical.choice, Quot.sound]`), no `def`/`instance`/`noncomputable def`
body is sorried, and no proposition is weakened to `True`. The functor is genuinely
`Hom(P, −)` into finitely generated `(End P)ᵐᵒᵖ = End(P)ᵒᵖ`-modules; the conclusion is a
genuine `IsEquivalence` (yielding an actual `C ≌ FGModuleCat (End P)ᵐᵒᵖ`); the corollary's
algebra witness is the concrete, honestly-finite-dimensional ring `(End P)ᵐᵒᵖ`. The one
scope nuance — the universal corollary takes `P` as input while progenerator existence
lives in `exists_progenerator` — is documented and fully covered. No defect; no feature
issue filed.
