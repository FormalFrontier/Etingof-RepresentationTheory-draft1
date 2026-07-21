# Fidelity audit: Chapter 4, Problem 4.12.1 — dihedral group irreps + V⊗V (#7219)

**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 3954c428)
**Scope:** `EtingofRepresentationTheory/Chapter4/Problem4_12_1.lean`
(headline decls `irreducible_dim`, `tensor_square_character`; supporting defs
`zeta`, `chiStd`, `chiSign`, `chiRot2`; namespace `Etingof.Problem4_12_1`).
**Method:** book statement first (`blobs/Chapter4/Problem4.12.1.md`, parts (a)–(b)),
then statement-vs-blob fidelity of each headline (Stage 3.2 steps 6–7: no silent
weakening, non-vacuity), then axioms/build. Calibrated against the confirmed gap
`Chapter4/Problem4.12.2` part (d) (#7204/#7211) and the 2.16.2 char-0 gap (#7207).

## Overall verdict: **gap (part (a) classification silently reduced to a dimension bound)**

Part **(b) is a faithful, non-vacuous character-level rendering.** Part **(a) is a
`gap`**: the book asks to *describe all* irreducibles (with odd/even `N` split and
counts); the Lean headline `irreducible_dim` proves only the *necessary condition*
`finrank ∈ {1, 2}`. Unlike 4.12.2 — whose full enumeration was proved *inside* the
proof and merely not exposed — here the classification content (construction of the
irreps, exhaustiveness, non-isomorphism, odd/even counts) is **entirely absent**, not
just unsurfaced. This is the exact silent-weakening failure mode the sweep targets.

---

## Part (a) — book vs Lean

**Book (a):** "Describe all irreducible complex representations of this group
(consider the cases of odd and even `N`)." The intended answer (standard `D_N`
character theory): for **odd `N`**, 2 one-dimensional irreps (trivial, sign) and
`(N−1)/2` two-dimensional irreps `V_j` (`1 ≤ j ≤ (N−1)/2`); for **even `N`**, 4
one-dimensional irreps and `(N−2)/2` two-dimensional irreps.

**Lean:** `irreducible_dim [NeZero N] (ρ : Representation ℂ (DihedralGroup N) W)
(hρ : IsSimpleModule …) : finrank ℂ W = 1 ∨ finrank ℂ W = 2`.

**Assessment — silent weakening (steps 6–7):**
- The theorem asserts only a **dimension dichotomy** — a necessary condition every
  irrep satisfies. It does **not** enumerate the irreps, construct any of them, show
  they are pairwise non-isomorphic, show they are exhaustive, split the odd/even
  cases, or give the counts.
- The proof (eigenvector `v` of `ρ (r 1)`; the `≤ 2`-dimensional subrep
  `span{v, ρ(sr 0) v}` forced to `⊤` by irreducibility) contains **no** enumeration
  content whatsoever — nothing internal to salvage into a headline. Contrast
  `Chapter4/Problem4.12.2` part (d), where the full sum-of-squares classification
  *was* proved inside `irreducible_dim` and the gap was only "not exposed."
- The docstring records the counts ("2 and `(N−1)/2`" / "4 and `(N−2)/2`"), but a
  **docstring comment is not a checked mathematical assertion** — it carries no
  formal content and cannot stand in for a theorem.

Per the issue's explicit calibration ("A dimension-only bound standing in for a full
'describe all irreps' classification is exactly the kind of silent weakening this
sweep exists to catch"), part (a) is a **gap**.

*Non-vacuity of what is present:* `irreducible_dim` itself is non-vacuous — the
hypothesis `IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) ρ.asModule` is
satisfiable (`DihedralGroup N` has genuine irreps for every `N ≥ 1`), and `[NeZero N]`
is consistent. So the theorem is a true, non-vacuous *necessary condition* — just far
weaker than the book's claim.

## Part (b) — book vs Lean

**Book (b):** `V` = complexified standard 2-dim rep; decompose `V ⊗ V` into
irreducibles. Intended answer: `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂` (trivial, sign, and the 2-dim
rep with rotation by `4π/N`).

**Lean:** `tensor_square_character (g) : chiStd N g ^ 2 = 1 + chiSign N g + chiRot2 N g`,
with `chiStd(r k) = ζ^k + ζ^{-k}`, `chiSign(r)=1, chiSign(sr)=-1`,
`chiRot2(r k) = ζ^{2k} + ζ^{-2k}` (`ζ = exp(2πi/N)`).

**Assessment — faithful at the character level:**
- The character values are correct: `χ_V(r k) = ζ^k + ζ^{-k}` (rotation eigenvalues
  `ζ^{±k}`), `χ_ε` the sign/determinant character, `χ_{V₂}(r k) = ζ^{2k} + ζ^{-2k}`,
  trivial `= 1`; all reflection values `0`/`-1` correct.
- The identity is exactly the tensor decomposition since `χ_{V⊗V} = χ_V²`:
  `(ζ^k+ζ^{-k})² = ζ^{2k} + 2 + ζ^{-2k} = 1 + 1 + (ζ^{2k}+ζ^{-2k})`, i.e.
  `χ_V² = χ_𝟙 + χ_ε + χ_{V₂}`; on reflections `0 = 1 + (−1) + 0`. Verified.
- Stating a decomposition at the character level is an accepted rendering in this
  project. The identity is genuine and non-vacuous (a real equality of `ℂ`-valued
  functions on `DihedralGroup N`, proved for all `N`, not vacuous).
- **Noted limitation (not a gap for (b)):** `chiStd/chiSign/chiRot2` are hand-defined
  class functions, not tied to actual `Representation` objects, and the theorem does
  not establish that `V₂` is irreducible (`V₂` is irreducible iff `2·2 ≢ 0 mod N`,
  i.e. `N ∉ {1,2,4}`; `V` itself is the genuine standard irrep for `N ≥ 3`). The
  character identity holds for all `N`; its reading as "sum of *irreducibles*" is the
  standard large-`N` statement. This is the accepted character-level modelling and is
  recorded, not counted against (b).

---

## Axioms & build

- No Lean files were modified in this audit (verdict is recorded in
  `progress/items.json` only), so the build state is identical to `origin/main`
  (green as of merge `c2f6621c`).
- The file is sorry-free (`grep -nE '\bsorry\b|\badmit\b'` → none), consistent with
  the item's recorded `#print axioms` (propext/Classical.choice/Quot.sound).

## Actions

- `progress/items.json` `Chapter4/Problem4.12.1`: `fidelity → gap`,
  `fidelity_issue → #<follow-up>`, `fidelity_note` added, `status` reverted from
  `sorry_free` to `partially_formalized` (part (a)'s classification is not merely
  unproven but **not stated**).
- Follow-up `feature` issue filed to formalize the full part (a) classification
  (construct the 1-/2-dim irreps, prove exhaustiveness + non-isomorphism, split
  odd/even with counts) as named headlines.
