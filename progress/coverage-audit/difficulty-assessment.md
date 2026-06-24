# Difficulty assessment: True-stubs + newly-discovered gaps

Best-effort estimates (one agent per cluster, verified spot-checks where it mattered).
Rubric: **T** <1hr / **E** hours / **M** 1-3 days / **H** 1-2 weeks / **R** research-level, weeks+.

Caveat: estimates assume a competent Lean+Mathlib formalizer and may be off by a tier.
Single-agent judgments; the prose-gap verdicts they build on were not adversarially re-verified.

---

## Part 1: the 13 vacuous `True`-stub statements (highest priority)

These are book theorems/definitions currently stated as `... : True := by trivial`, marked
`sorry_free`, asserting nothing.

| item | what it should say | diff | notes |
|---|---|---|---|
| `Theorem4_1_1` (sum-of-squares half) | `Σ (dim Vᵢ)² = \|G\|` | **T** | **The real result is ALREADY PROVEN** in-project as `IrrepDecomp.sum_sq_eq_card`. The stub just fails to cite it. Pure plumbing. Part (i) semisimplicity is a genuine theorem already. |
| `Theorem4_6_2` existence | every f.d. complex rep of finite G has a G-invariant pos-def Hermitian form (Weyl unitarian trick) | **M** | Build averaged inner product on the rep carrier; Mathlib has all pieces but no inner-product instance on `FDRep`. |
| `Theorem4_6_2` uniqueness | for irreducible V, invariant pos-def forms are proportional (Schur) | **M** | Schur available; Hermitian-form↔operator API thin; positivity fiddly. |
| `Theorem4_6_3` | f.d. unitary rep is completely reducible (W has invariant W^⊥) | **E-M** | `Submodule.orthogonal` + show W^⊥ is G-invariant. Mostly routine. |
| `Corollary5_1_6` | all irreps real ⟹ `Σ dim Vᵢ = #{g : g²=1}` | **E** | Specialize the already-proven Theorem 5.1.5 (real `frobeniusSchurIndicator`). Cheap win. |
| `Definition5_8_1` (Ind_H^G V) | the induced representation, as a real `Representation` | **E** ⟵ corrected | Mathlib **v4.32 has `Rep.ind H.subtype`** (verified: `Mathlib/RepresentationTheory/Induced.lean:77`). Replace the `True` stub with it. NOT a multi-day build. Unblocks 5.9.1, Remark 5.8.2. |
| `Example5_1_3` | FS types of ℤ/n, S₃, S₄, A₅, Q₈ | **H** | Needs character-table infrastructure for several specific groups + quaternionic-type criterion + Q₈ 2-dim irrep. |
| `Example5_12_3` | Specht module dims for small partitions | **M-H** | Easy given a real Specht-module construction; cost depends on §5.12 state. |
| `Lemma5_4_7` | ∃ nontrivial irrep with p∤dim and χ_V(g)≠0 (Burnside support) | **M** | Needs Prop 5.3.2 first; then short algebraic-integer argument. |
| `Lemma5_7_2` | virtual rep with (χ,χ)=1, χ(1)>0 is ±an irreducible | **M** | Needs a virtual-rep / character-ring notion; proof short given orthonormality. |
| `Proposition5_3_2` | `χ_V(g)·\|C\|/dim V` is an algebraic integer | **M** | ℤ[G] f.g. over ℤ ⟹ integral; identify scalar via Schur. Depended on by 5.3.1. |
| `Theorem5_3_1` | **`dim V ∣ \|G\|`** | **M** | Famous classical result; the most embarrassing *theorem* left vacuous. Needs 5.3.2 + ℚ∩ℤ̄=ℤ. |
| `Theorem5_6_1` | irreps of G×H are exactly `Vᵢ ⊗ Wⱼ` | **M-H** | Cites Thm 3.10.2 (simple modules of A⊗B); reuse if present else build. |
| `Theorem5_9_1` | Frobenius character formula for `Ind V` | **H** | Unblocked now that `Rep.ind` exists; then a genuine coset block-trace computation. |

**Headline:** none of these is research-level. The standout is that `Theorem4_1_1`'s
sum-of-squares is **already proven** (trivial fix), and `Definition5_8_1` (the induced
representation, which looked like the scariest one) is now an **easy** swap to Mathlib's
`Rep.ind`. The most embarrassing genuinely-open theorem is **`dim V ∣ |G|` (5.3.1)**,
Moderate. The Chapter 4 unitarizability pair (4.6.2/4.6.3, Weyl's unitarian trick) is
Moderate. Realistic total for clearing the stubs: a couple of focused weeks, most of it
on Example 5.1.3 (per-group character tables) and the 5.3.1/5.3.2/5.4.7 algebraic-integer chain.

---

## Part 2: the 34 prose-claim gaps, by difficulty

**Trivial / Easy (≈14):** Ch2 quotients (A/I, V/W) [T], Ch2 k[t] char-0 faithful [E, reuses
existing `polyRep`], Ch2 k[G] comm⟺G comm [E], Ch2 End/free noncommutative [E], Ch3 free-module
surjection [E], Ch3 character tracial [E], Ch4 irreducibility criterion ⟨χ,χ⟩=1 [T-E, near-verbatim
Mathlib], Ch4 dual/conjugate character formulas [E], Ch5 Ind≅Hom_H coind [E, = Mathlib `indCoindIso`],
Ch7 FSet≃skeleton [T, in Mathlib], Ch7 adjunction-as-representability [T, Mathlib `Adjunction.corepresentableBy`],
Ch7 Example-7.7.2 k-linear [T, Mathlib instance], Ch7 toy-groupoid equivalence [E].

**Moderate (≈11):** Ch3 isotypic decomposition iso [M], Ch3 length=max-strict-filtration [M],
Ch4 conjugate rep V̄≅V* [M-H, needs V̄ defined], Ch5 S₃-from-Z₂/Z₃ induced decompositions [M×2,
need an S₃ irrep catalogue], Ch5 U_λ=ℂ[S_n]·a_λ [M], Ch5 ½q(q-1) count [M, character-group combinatorics],
Ch7 iso-classes-of-functors bijection [M, quotient/Setoid plumbing], Ch9 Hom-spaces finite-dim [M],
Ch9 dim Bₙ=Σcᵢⱼnᵢnⱼ [M, needs rep-theoretic Cartan matrix defined], Ch9 minimal basic algebra dim [M].

**Hard (≈9):** Ch2 quiver-reps ≃ path-algebra-modules [H] AND Ch2 Σpᵢ=1 unital [M] — both gated on
**building a ring/module structure on `PathAlgebra`, which is currently only a `Finsupp` type** (Mathlib
has no path algebra). Ch2 char-free faithful Laurent-Weyl module tᵃk[a][t,t⁻¹] [H]. Ch4 Frobenius
convolution-idempotent characters [H]. Ch5 semidirect x-independence iso [H, bespoke `inducedRepV`].
Ch9 **the entire B_n-family cluster** (projective-generator classification, Morita-class enumeration) —
one coherent 1-2 week development whose critical path is Krull-Schmidt-style progenerator classification
plus completing the already-sorry'd `MoritaStructural`; Mathlib's Morita theory does not meaningfully help.

**Research-level:** none among these gaps. (The genuinely research-level items in the book, e.g.
Weyl complete reducibility for the full sl(2) problem, were already known-open and are tracked separately.)

---

## Cross-cutting observations

1. **`PathAlgebra` has no algebra structure** — it is a bare `Finsupp` type (Ch2). Several Ch2 gaps
   and arguably Definition 2.8.4 itself depend on fixing this. This is a definition-integrity issue
   in the same family as the `True`-stubs.
2. **`MoritaStructural` still carries sorries** and is the critical-path dependency for all of Ch9's
   B_n gaps.
3. **Mathlib caught up on induced representations** (`Rep.ind`/`coind`/`indCoindIso`, v4.32). Re-checking
   "not in Mathlib" assumptions from earlier waves is worthwhile; at least the Ind cluster benefits.
