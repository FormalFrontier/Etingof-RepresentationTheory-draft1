# Stage 3.7 fidelity re-audit: last 2 unchecked remarks + 9 non-canonical values

Issue: #7184. Session: `/review` (e4352d38).

Re-audited 11 `progress/items.json` entries against their blobs using Stage 3.2
steps 6–7 (statement-fidelity + non-vacuity). All 10 formalized items **build**
(`lake build`, exit 0, one style long-line warning only) and every headline
declaration is **axiom-clean** (`#print axioms` → `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`). Item 11 (`Chapter2/Remark2.9.14`) is
`non_formalizable` (no Lean file, correctly).

## Part 1 — first-pass audit of the last two `unchecked` remarks

| Item | Headline decl | Verdict | before → after |
|---|---|---|---|
| `Chapter3/Remark3.1.3` | `Etingof.evalDirectSumEquiv` | FAITHFUL | (unset) → `verified` |
| `Chapter4/Remark4.5.3` | `Etingof.Remark4_5_3.renormChar_isPrimitiveIdempotent` + `character_recovery` | FAITHFUL | (unset) → `verified` |

- **Remark 3.1.3** (canonical decomposition of a semisimple rep). `evalDirectSumEquiv`
  builds the *genuine* evaluation map `⨁ᵢ Hom_A(Xᵢ,V) ⊗_k Xᵢ → V`, `g ⊗ x ↦ g(x)`
  (`evalTensor`/`evalDirectSum` are real data, not sorried) and proves it a `k`-linear
  isomorphism, given a complete pairwise-non-isomorphic family `{Xᵢ}`. This is exactly
  the book's map `f` and its iso claim. Non-vacuous: the completeness/pairwise-non-iso
  hypotheses are the honest rendering of "X runs over all irreducibles."
- **Remark 4.5.3** (Frobenius's convolution-algebra definition of characters). Genuine
  constructions of the convolution algebra (`MonoidAlgebra ℂ G`), class-function
  subalgebra (= centre), and the renormalized character as a **primitive idempotent**;
  plus proofs of centre ↔ class-functions, primitive-idempotency, and the recovery
  formula `χ_V(g) = √(|G|/χ̃_V(1))·χ̃_V(g)`. Faithful and non-vacuous.

## Part 2 — normalize nine non-canonical `fidelity` values

| Item | Headline decl | Verdict | before → after |
|---|---|---|---|
| `Chapter2/Remark2.9.4` | `Etingof.Remark2_9_4.expDerivAut` (+ `hasDerivAt_leibniz`) | FAITHFUL | `faithful` → `verified` |
| `Chapter3/Definition3.4.1` | `Etingof.Filtration` (structure) | FAITHFUL | `faithful` → `verified` |
| `Chapter3/Theorem3.10.2` | `tensor_product_irreducible` (i) + `..._classification`/`..._unique` (ii) | FAITHFUL | `faithful` → `verified` |
| `Chapter9/Definition9.5.1` | `Etingof.AreLinked`, `Etingof.Block` | FAITHFUL | `faithful` → `verified` |
| `Chapter3/Remark3.10.3` | `ratFunc_tensor_ratFunc_not_isField` | FAITHFUL | `covered` → `verified` |
| `Chapter4/Definition4.10.1` | `Etingof.FrobeniusDeterminant` | FAITHFUL | `ok` → `verified` |
| `Chapter7/Example7.5.3` | `Etingof.Example753.forgetful_not_representable` | FAITHFUL | `resolved` → `verified` |
| `Chapter2/Remark2.9.14` | — (non_formalizable) | FAITHFUL by convention | `n/a` → `verified` |
| `Chapter3/Remark3.8.6` | `exists_indecomposable_decomposition` (+ Fitting / local-ring) | **GAP** | `partial` → `gap` |

Notes on the non-trivial calls:

- **Remark 2.9.4** — both directions present: `hasDerivAt_leibniz` (forward, `D=g'(0)`
  is a derivation) and `expDerivAut` (converse, `e^{tD}` is an algebra automorphism,
  built as a real `A ≃ₐ[ℝ] A`).
- **Definition 3.4.1** — `Filtration` structure records the strictly ascending
  `RelSeries` of submodules with `head = ⊥`, `last = ⊤`: faithful to `0 = V₀ ⊂ ⋯ ⊂ Vₙ = V`.
- **Theorem 3.10.2** — part (i) (`V ⊗ W` irreducible over `A ⊗ B`) and part (ii)
  (every irreducible `M` is `V ⊗ W` for **unique** `V`, `W`) are both present, including
  the uniqueness decl.
- **Definition 9.5.1** — the linking relation (`AreLinked` = equivalence closure of
  simplicity-gated Ext¹-adjacency) and the block partition (`Block = Quotient blockSetoid`,
  `InBlock`) are genuine data, faithful to the book's chain/linked/block definitions.
- **Remark 2.9.14** — non-formalizable historical/geometric remark (Lie groups, `Lie(G)`,
  Lie's bijection). Asserts no formal mathematical claim the pipeline formalizes; `verified`
  by the sweep's convention that a non-formalizable blob correctly asserting nothing is faithful.

### The one genuine gap: `Chapter3/Remark3.8.6` → `gap`

Remark 3.8.6 asserts **"the Krull-Schmidt theorem holds for modules of finite length."**
The Lean file proves Fitting's lemma, that the endomorphism ring of a finite-length
indecomposable is local, and the **existence** of an indecomposable decomposition — but
the **uniqueness** half (the substance of Krull-Schmidt) is, by the file's own docstring,
"left as follow-up work." Since a real, central claim of the remark is unformalized, this
is a genuine `gap`, not `verified`. The item stays `sorry_free` (the existing decls are
honestly sorry-free; the gap is *missing content*, not a sorry). Filed **feature issue
#7185** for the uniqueness half; `fidelity_issue` updated `5662 → 7185`.

## Bookkeeping outcome

`git diff progress/items.json` touches only `fidelity`/`fidelity_issue` on the 11 listed
items. File-wide tally after the edit: **261 `verified`, 19 `gap`, 0 non-canonical** — the
vocabulary is now entirely `unchecked | verified | gap`. The two remaining `unchecked`
claim-bearing items named in #7184 are cleared. The 19 `gap` items are the 18 stale-marker
entries owned by the companion batches #7182 (Ch2–4) and #7183 (Ch5 & 7), plus the newly
classified Remark 3.8.6 (#7185).
