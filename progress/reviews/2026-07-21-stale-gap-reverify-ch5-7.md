# Stage 3.7 stale-gap re-verification — Chapter 5 & 7 batch (issue #7183)

Date: 2026-07-21 · Session type: review · Branch: `agent/87873498`

Re-audit of 9 claim-bearing items marked `fidelity: gap` in `progress/items.json`
whose original repair issues are all CLOSED. Each was re-checked against its blob
using the Stage 3.2 steps 6–7 fidelity tests: (a) builds, (b) `#print axioms` free of
`sorryAx`, (c) faithfully and non-vacuously asserts the book's claim. This was a genuine
re-audit, not a rubber stamp — the `fidelity_note` fields recorded the *original*
(pre-repair) gap reasons, and the current Lean state was read directly.

All 9 target modules build (`lake build` of the nine modules, exit 0). Axiom checks on
every VERIFIED headline declaration show only `[propext, Classical.choice, Quot.sound]`
— no `sorryAx`.

## Verdicts

| Item | Verdict | Notes |
|------|---------|-------|
| Chapter5/Theorem5.6.1 | **VERIFIED** | `[IsAlgClosed k]` is faithful to Ch5's standing assumptions (result is false over ℝ; book's proof routes through Thm 3.10.2, which lives in the alg-closed context). Both directions of the G×H classification present as an equivariant iso. |
| Chapter5/Theorem5.10.1 | **GAP** | Reversed adjunction direction — see below. Repair issue **#7187**. |
| Chapter5/Example5.12.3 | **GAP** (partial) | Trivial/sign now faithful at rep level; ℂ³₋/ℂ³₊ only by dimension — see below. Repair issue **#7188**. |
| Chapter5/Example5.19.3 | **VERIFIED** | Repaired: isos are now proved GL(V)-equivariant (not merely k-linear), plus irreducibility of SⁿV and ∧ⁿV, plus the n>dim V vanishing caveat. |
| Chapter5/Theorem5.27.1 | **VERIFIED** | Repaired: part (ii) now states the full pairwise-non-isomorphism/orbit classification and part (iii) exhaustiveness; character formula faithful term-by-term. (Note: item title is "semidirect products G ⋉ A"; the issue's "sl₂" label is a typo — the actual content is the orbit-method classification.) |
| Chapter7/Example7.3.2 | **VERIFIED** | Matches existing PASS report `2026-07-21-ch7-example7_3_2-fidelity.md`. All four sub-items formalized; the previously-deferred sub-item (2) non-naturality is now present (`not_natIso_id_contragredientFunctor`, `IsEmpty (𝟭 ≅ F)`). |
| Chapter7/Definition7.8.1 | **VERIFIED** | Repaired docstring/decl mismatch: `Etingof.differential`, `cohomology`, `ExactAt`, `IsExactSequence` are now real abbrevs alongside `CochainComplex'`, all five book notions declared. |
| Chapter7/Definition7.8.2 | **VERIFIED** | Repaired: `Etingof.ShortExactSequence := {S : ShortComplex C // S.ShortExact}` bundles the exactness predicate (was previously the bare `ShortComplex`, satisfied by non-exact complexes). |
| Chapter7/Example7.9.6 | **VERIFIED** | Repaired: part (i) Ind/Res exactness now via `PreservesFiniteLimits`/`PreservesFiniteColimits` (Ind exact under `f.Flat`), parts (ii)/(iii) left/right exactness + the book's concrete counterexamples. Commutativity/flatness caveats are documented, not fidelity defects. |

**Result: 7 flipped to `verified`, 2 left `gap` with new repair issues.**

## The two genuine gaps

### Chapter5/Theorem5.10.1 — reversed adjunction direction (repair #7187)

Book (`blobs/Chapter5/Theorem5.10.1.md`, line 1, read directly by the reviewer):
`Hom_G(V, Ind_H^G W) ≅ Hom_H(Res_H^G V, W)`, with `Ind` the function-space (coinduced)
representation `{f : G → W | f(hx)=h·f(x)}` — the right-adjoint form `Res ⊣ Coind`
(the proof builds `F(α)v=(αv)(e)` for `α : V → Ind W`).

Current Lean headline `Etingof.Theorem5_10_1`:
`(Rep.ind H.subtype W ⟶ V) ≃ₗ[k] (W ⟶ res V)`, i.e. `Hom_G(Ind W, V) ≅ Hom_H(W, Res V)`
— the left-adjoint form `Ind ⊣ Res`, using Mathlib's tensor `Rep.ind = (k[H] ⊗ A)_G`.
Both Hom-spaces have source and target swapped versus the book, and for infinite index the
tensor `Rep.ind` is not the book's function-space `Ind`. The proof is sorry-free and
axiom-clean but faithfully proves a *different* (transposed) theorem. Left `gap`; status
kept `sorry_free` (the proof is genuinely sorry-free).

### Chapter5/Example5.12.3 — ℂ³₋ vs ℂ³₊ not distinguished (repair #7188)

Repaired since the original note: `Example5_12_3_trivial_rep`/`_sign_rep` now pin the
trivial and sign reps at the ℂ[Sₙ]-module level (every σ acts as id / as sign σ), not just
by dimension. Residual gap: the book identifies the n=4 Specht modules λ=(3,1)→ℂ³₋ and
λ=(2,1,1)→ℂ³₊ (the two distinct 3-dim irreps of S₄), but Lean captures both only as
`finrank = 3` (`Example5_12_3_dim_31`, `Example5_12_3_dim_211`). Dimension 3 cannot
distinguish the two non-isomorphic 3-dim irreps; the ±content lives only in doc-comment
prose. Left `gap`. (The (2,1)/(2,2)→ℂ² cases are acceptable as dimension-only since each
Sₙ has a unique 2-dim irrep.)

## Method note

Audits were fanned out one-per-item to parallel subagents, each given the item's original
`fidelity_note`, the blob path, and the Lean file, with instructions to re-verify the
*current* state rather than trust the (pre-repair) note. The 5.10.1 GAP was independently
confirmed by the reviewer reading `blobs/Chapter5/Theorem5.10.1.md` directly, given its
high stakes (a headline theorem). Axiom-cleanliness of all VERIFIED headline decls was
checked centrally via `#print axioms`.
