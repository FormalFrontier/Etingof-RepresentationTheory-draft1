# Stage 3.7 fidelity & non-vacuity audit — Problem 4.12.11 (elasticity / Hooke's law)

**Issue:** #7302 (report-only). **Lean file:**
`EtingofRepresentationTheory/Chapter4/Problem4_12_11.lean` (1504 lines, sorry-free).
**Verdict:** `fidelity: verified`, `coverage: covered_full`.

Build: `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_11` exits 0 (only
`linter.style.longLine` / deprecation-of-`push_neg` warnings, no errors). All ten headline
theorems `#print axioms`-clean: `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.

## Book statement (recap)

`V = ℝ³` with its inner product; `SO(3)` acts on `V`, hence on `S²V` and `End(V)`.
- **(a)** `End(V) = ℝ ⊕ V ⊕ W` (trivial ⊕ standard-3-dim ⊕ 5-dim), and `S²V = ℝ ⊕ W`.
- **(b)** `V`, `W` irreducible even after complexification; deduce via Schur that a
  Galileo-invariant Hooke's law `f` satisfies `f(x + y) = Kx + μy` (`x ∈ ℝ`, `y ∈ W`)
  and that `S_P` is always symmetric.

## Hypothesis faithfulness

- **`SO3` is the genuine special orthogonal group.** `SO3 :=
  specialOrthogonalGroup (Fin 3) ℝ` (line 51). Nontrivial: `Dz, Dy, Dx, Pc, Rz45, Ry45`
  are explicit non-identity members. `coe_mul_star`/`star_mul_coe` (126, 130) extract
  `A·Aᵀ = Aᵀ·A = 1` from `mem_specialOrthogonalGroup_iff`.
- **`conjRep` is the real conjugation representation.** `conjRep A M = A · M · star A`
  (`conjRep_apply`, 71); over ℝ `star A = Aᵀ` (`star_coe_eq_transpose`, 121) and `Aᵀ = A⁻¹`,
  so this is genuine conjugation. It is a bona fide `Representation ℝ SO3 EndV` with real
  `map_one'`/`map_mul'` proofs (58–68), not a placeholder. `EndV = Matrix (Fin 3)(Fin 3) ℝ`.
- **The three summands are the intended `ℝ`/`V`/`W`.** `scalarSub = span ℝ {1}` (trivial
  rep, `ℝ`), `skewSub = {M | Mᵀ = -M}` (identified with the standard rep `V`; for `SO(3)`
  the adjoint/skew rep `so(3)` is isomorphic to the standard `ℝ³` via the hat map — a
  standard, faithful identification), `tracelessSymSub = {M | Mᵀ = M ∧ trace M = 0}`
  (the 5-dim `W`), `symSub = {M | Mᵀ = M}` (`S²V`). All are genuine `Submodule`s with real
  closure proofs; each is `SO(3)`-invariant (`conjRep_invariant`, 136).
- **The `hooke_law` intertwiner hypothesis is faithful.** `hf : ∀ A : SO3,
  f.comp (conjRep A) = (conjRep A).comp f` (1408) is exactly "`f` is a homomorphism of
  `SO(3)`-representations" (Galileo invariance), pointwise `f (conjRep A M) = conjRep A (f M)`.

## Statement fidelity, part by part

**(a) Decomposition.** `endV_isInternal` (187):
`DirectSum.IsInternal ![scalarSub, skewSub, tracelessSymSub]`, i.e. `End(V)` is the internal
direct sum `ℝ ⊕ V ⊕ W`, proved via `iSupIndep` (pairwise `Disjoint`) + `iSup = ⊤` (explicit
scalar/skew/traceless-symmetric splitting). Dimensions match the book exactly:
`scalarSub_finrank = 1`, `skewSub_finrank = 3`, `tracelessSymSub_finrank = 5` (294/297/337).
`symSub_eq_scalar_sup_tracelessSym` (270): `scalarSub ⊔ tracelessSymSub = symSub` **and**
`scalarSub ⊓ tracelessSymSub = ⊥`, delivering `S²V = ℝ ⊕ W` as an internal direct sum.
Faithful.

**(b) Irreducibility.** All four theorems use the genuine irreducibility conclusion
"`U = ⊥ ∨ U = <ambient>`" for an arbitrary invariant sub-`U`:
- `skewSub_irreducible` (647), `tracelessSymSub_irreducible` (720) over ℝ, hypothesis
  `U ≤ skewSub`/`≤ tracelessSymSub` invariant under `conjRep` ⇒ `⊥` or whole.
- `skewSub_irreducible_complexified` (1041), `tracelessSymSub_irreducible_complexified`
  (1110) over ℂ. Phrased over the **correct** complexified object: `EndVc =
  Matrix (Fin 3)(Fin 3) ℂ`, `conjRepc` the complexified conjugation, `skewSubc`/
  `tracelessSymSubc` the complex skew/traceless-symmetric matrices (3-/5-dim over ℂ, the
  genuine complexifications), transported through the ring hom `cx = (algebraMap ℝ ℂ).mapMatrix`
  via `cx_conjRep` (894). Matches "irreducible even after complexification".

**(b) Hooke's law.** `hooke_law` (1407): for equivariant `f`, `∃ K μ : ℝ`,
`(∀ x ∈ scalarSub, f x = K • x) ∧ (∀ y ∈ tracelessSymSub, f y = μ • y) ∧
(∀ x ∈ symSub, f x ∈ symSub)`. By linearity the first two conjuncts give the book's
`f(x + y) = Kx + μy` on `S²V = ℝ ⊕ W`; the third is "`S_P = f(d_P)` is symmetric whenever
the deformation tensor `d_P ∈ S²V` is symmetric". Proof is the book's route: `f 1` is
invariant hence scalar `K` (`invariant_matrix_scalar`, 1324); on `W`, `scalarProj∘f` and
`skewProj∘f` vanish by Schur (`equivMap_eq_zero_of_finrank_lt`, 1287, using irreducibility +
strict `finrank` drop), so `f` preserves `W`; the restriction `f|_W` on the odd-dim `W` has a
real eigenvalue `μ` (`exists_isRoot_of_odd_natDegree` via IVT), whose eigenspace is a nonzero
invariant sub, hence all of `W` by irreducibility ⇒ `f = μ` on `W`. Faithful to Schur's-lemma
argument.

## Non-vacuity

- `SO3` nontrivial (explicit non-identity elements). `skewSub`, `tracelessSymSub` nonzero
  (finrank 3, 5); complexified subspaces contain `cx (sbasis i) ≠ 0`. Irreducibility
  theorems therefore non-vacuous (ambient spaces nonzero).
- `hooke_law`'s intertwiner hypothesis is satisfiable by genuine invariant maps
  (`f = id`, scalar multiples, the projections `scalarProj`/`skewProj`), so the conclusion
  is not vacuous.
- No `True`-typed or trivially-dischargeable hypothesis anywhere; every submodule is a real
  construction, `conjRep`/`conjRepc` are real `Representation`s.

## Fidelity note (transparent modeling choice, not a gap)

The book's Hooke's law is a map `f : S²V → End(V)`; the Lean models it as an equivariant
self-map `f : End(V) →ₗ[ℝ] End(V)`. This is a **faithful, equivalent** rendering, not a
weakening: `S²V = symSub` is an `SO(3)`-invariant direct summand of `End(V)` (complement the
skew part `V`), so any equivariant `S²V → End(V)` extends to an equivariant self-map (via the
equivariant projection `End(V) ↠ S²V`), and conversely `hooke_law`'s conclusions on
`scalarSub`/`tracelessSymSub`/`symSub` restrict back to the book's statement on `S²V`. Hence
the theorem *implies* the book claim (it is if anything slightly more general). Recorded here
for completeness; no repair issue is warranted.

## Verdict

`fidelity: verified`, `coverage: covered_full`. Part (a) (both `End(V) = ℝ⊕V⊕W` and
`S²V = ℝ⊕W` with correct dims), part (b) irreducibility (real **and** complex), and Hooke's
law (`f(x+y)=Kx+μy` + symmetry of `S_P`) are all faithfully and non-vacuously formalized and
axiom-clean. No Lean statement edits; no follow-up repair issue.
