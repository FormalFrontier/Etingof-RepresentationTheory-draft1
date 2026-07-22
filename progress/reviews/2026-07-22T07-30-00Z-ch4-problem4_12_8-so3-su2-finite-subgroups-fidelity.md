# Stage 3.7 audit — Problem 4.12.8 (finite subgroups of SO(3) and SU(2))

**Issue:** #7280 (statement-fidelity & non-vacuity audit; report-only).
**File:** `EtingofRepresentationTheory/Chapter4/Problem4_12_8.lean` (3530 lines).
**Blob:** `blobs/Chapter4/Problem4.12.8.md`.
**HEAD:** `3b166a4d`.
**Verdict:**
- **Part (a)** `so3_finite_subgroup_classification` — **VERIFIED**: full, faithful,
  genuinely-derived classification; non-vacuous; axiom-clean.
- **Part (b)** `su2_finite_subgroup_double_cover` — **VERIFIED-AS-STATED but PARTIAL**:
  the theorem it states (the double-cover order relation) is faithful and non-vacuous,
  but it is a *proper sub-statement* of the book's part (b) "classify finite subgroups
  of SU(2)". The explicit SU(2) classification list (cyclic / binary dihedral / binary
  tetrahedral-octahedral-icosahedral) is documented in the file docstring but not
  formalized. Recommended follow-up feature issue (below), not a patch in this PR.

## Build / axiom check

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_8` exits 0 (8580 jobs).
  Only style warnings (three deprecated `push_neg`, one long line at 3270); no errors.
- The file is `sorry`-free (0 `sorry` tokens outside docstrings).
- `#print axioms`:
  - `so3_finite_subgroup_classification` → `[propext, Classical.choice, Quot.sound]`
  - `su2_finite_subgroup_double_cover` → `[propext, Classical.choice, Quot.sound]`

  Both axiom-clean; no `sorryAx`.

## Book text

> **Problem 4.12.8.** It is known that the classification of finite subgroups of SO(3)
> is as follows: 1) cyclic ℤ/nℤ, n ≥ 1; 2) dihedral Dₙ of order 2n, n ≥ 2 (a regular
> 2-gon is a line segment); 3) rotations of a regular tetrahedron (A₄); 4) rotations of
> a cube/octahedron (S₄); 5) rotations of a dodecahedron/icosahedron (A₅). (a) Derive
> this classification [pole counting, 2(1−1/n) = Σᵢ(1−1/mᵢ)]. (b) Using this
> classification, classify finite subgroups of SU(2) (use the homomorphism SU(2)→SO(3)).

## Part (a): `so3_finite_subgroup_classification`

```lean
theorem so3_finite_subgroup_classification
    (G : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite G] :
    IsCyclic G ∨
    (∃ n : ℕ, Nonempty (G ≃* DihedralGroup n)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
    Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 5))
```

### Statement faithfulness — VERIFIED

- **Ambient group.** `Subgroup (specialOrthogonalGroup (Fin 3) ℝ)` with `[Finite G]`
  is exactly "a finite subgroup of SO(3)". `specialOrthogonalGroup (Fin 3) ℝ` is
  Mathlib's `{M | Mᵀ M = 1 ∧ det M = 1}`, the genuine SO(3). ✓
- **The five targets match the book's five families:**
  1. `IsCyclic G` = "cyclic ℤ/nℤ". The book's family (1) is all cyclic groups; `IsCyclic`
     is the faithful, index-free rendering (a specific `n` is unnecessary — cyclicity is
     the invariant). ✓
  2. `∃ n, Nonempty (G ≃* DihedralGroup n)` = "dihedral Dₙ". **Cardinality convention
     checked:** Mathlib `DihedralGroup.nat_card : Nat.card (DihedralGroup n) = 2 * n`
     (and `DihedralGroup.card [NeZero n] : Fintype.card = 2 * n`), so `DihedralGroup n`
     has order 2n for n ≥ 1, matching the book's "Dₙ of order 2n". `DihedralGroup 0` is
     the *infinite* dihedral group, so it can never satisfy `G ≃* DihedralGroup 0` for a
     finite `G` — the unconstrained `∃ n` admits **no** degenerate finite member of the
     wrong order. Moreover the disjunct is only produced in `so3_classification_aux` from
     `so3_dihedral_of_poleData G k hk …` where `hk : 2 ≤ k`, so the actual witness
     satisfies n ≥ 2, exactly the book's D_n, n ≥ 2. (A hypothetical n = 1 witness would
     describe an order-2 group, itself cyclic and already covered by the inclusive `∨`;
     this is a sound over-approximation, never a false claim.) ✓
  3. `alternatingGroup (Fin 4)` = A₄, the tetrahedral rotation group (order 12). ✓
  4. `Equiv.Perm (Fin 4)` = S₄, the cube/octahedron rotation group (order 24). ✓
  5. `alternatingGroup (Fin 5)` = A₅, the dodecahedron/icosahedron rotation group
     (order 60). ✓
- **Not vacuous, and genuinely derived (not merely asserted).** The disjunction is not
  a bare `It is known` restatement: it is *proved* from the pole-counting method the
  book prescribes. `so3_classification_aux` invokes `pole_order_data` (which builds the
  pole multiset and the Diophantine identity `2(1−1/n)=Σ(1−1/mᵢ)` via the milestones
  `exists_fixed_vector`, `isCyclic_of_common_fixed_vector`, `nontrivial_fixed_unit_vectors`,
  `finite_poleSet`), then `pole_order_diophantine` reduces the multiset to one of
  `{n,n}`, `{2,2,k}`, `{2,3,3}`, `{2,3,4}`, `{2,3,5}`, and each family is realized as an
  actual `MulEquiv` (`so3_cyclic/dihedral/tetrahedral/octahedral/icosahedral_of_poleData`).
  The icosahedral crux is a real construction (`so3_icosahedral_exists_faithful_perm5`
  via the simple-group / index-5 coset route, `A₅` landing via index-2). The trivial
  `|G| = 1` case is handled separately (`isCyclic_of_subsingleton`). So every disjunct
  carries genuine content and none of the `Nonempty (G ≃* …)` is vacuously inhabited. ✓

**Part (a) verdict: VERIFIED** — a complete and faithful formalization of the SO(3)
classification, derived by the book's own pole-counting argument.

## Part (b): `su2_finite_subgroup_double_cover`

```lean
theorem su2_finite_subgroup_double_cover
    (h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ)
    (hker : ∀ A : specialUnitaryGroup (Fin 2) ℂ,
      A ∈ h.ker ↔ ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
                    (A : Matrix (Fin 2) (Fin 2) ℂ) = -1))
    (H : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite H] :
    ((∃ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) →
        Nat.card H = 2 * Nat.card (H.map h)) ∧
    ((∀ A ∈ H, (A : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) →
        Nat.card H = Nat.card (H.map h))
```

### Is the hypothesized `h` a fidelity risk? — RESOLVED: no vacuity

The theorem takes `h` and its kernel-`{±1}` property `hker` as *hypotheses* rather than
constructing the double cover. The issue flags the risk that this is "vacuously about a
possibly-nonexistent `h`". **This risk does not materialize:**

- Such an `h` is **constructed inside the repository**. Problem 4.12.7
  (`EtingofRepresentationTheory/Chapter4/Problem4_12_7.lean`,
  `exists_surjective_hom_to_SO3`, lines 899–940) produces
  `h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ` that is
  surjective and satisfies exactly
  `A ∈ h.ker ↔ (A : Matrix) = 1 ∨ (A : Matrix) = -1` — i.e. precisely the `hker`
  hypothesis of part (b). (Built via the unit-quaternion conjugation `rotHom` transported
  along the iso `unitary ℍ[ℝ] ≃* SU(2)`; kernel via `rotMat_eq_one_iff`.)
- Consequently the hypotheses are **simultaneously satisfiable by a repo-internal
  witness**, so the theorem is genuinely non-vacuous, not merely non-vacuous in principle.
  (`su2_finite_subgroup_double_cover` requires only `hker`; 4.12.7 supplies both `hker`
  and surjectivity, so the hypothesis set is fully dischargeable.)
- **Minor structural note:** the two results are not yet linked — part (b) re-hypothesizes
  `h` instead of importing `exists_surjective_hom_to_SO3` from 4.12.7. Wiring them (so
  part (b) is stated/instantiated unconditionally) would remove the last trace of the
  "conditional on an abstract `h`" concern. This is a cleanliness/linkage gap, not a
  correctness or vacuity gap.

### Conclusion faithfulness — VERIFIED as stated, but a PARTIAL rendering of the book

- **What is proved is correct.** Given the double cover `h` with kernel `{±1}`, for any
  finite `H ≤ SU(2)`: if `-1 ∈ H` then `|H| = 2·|h(H)|`, else `|H| = |h(H)|`. The proof
  is the first isomorphism theorem (`|H| = |h(H)|·|ker h'|` via
  `QuotientGroup.quotientKerEquivRange`) plus the case split on whether `-1 ∈ H` makes
  `ker(h|_H)` have order 2 or 1. This is exactly the double-cover order/index relation,
  correctly formalized and non-vacuous (`Nat.card H` values are genuine; the two cases
  are exhaustive and mutually exclusive). ✓
- **But it is not the full "classification".** The book's part (b) asks to *classify* the
  finite subgroups of SU(2) — i.e. to produce the explicit list: cyclic, binary dihedral
  (dicyclic), binary tetrahedral (2·A₄, order 24), binary octahedral (2·S₄, order 48),
  binary icosahedral (2·A₅, order 120), plus the odd-order groups that map isomorphically.
  The Lean theorem delivers only the *mechanism* (the order relation between `H` and its
  image `h(H)`, the latter classified by part (a)), not the enumerated list. The file
  docstring is explicit and honest about this: "The corresponding subgroups of SU(2) …
  (recorded here in the docstring rather than formalized)."
- **Assessment.** Phrasing part (b) as the double-cover order relation is a *faithful but
  proper sub-statement* of the book's request: it is the load-bearing lemma from which
  the classification list follows (each finite `H ≤ SU(2)` is the full or index-2 preimage
  of one of the five SO(3) families), but the list-producing theorem is absent. This is a
  genuine, bounded scope gap — analogous to how part (a)'s Diophantine identity is "the
  method"; here the order relation is "the method" for (b), and unlike (a) the final
  enumerated classification was not carried through to a theorem.

**Part (b) verdict: VERIFIED-AS-STATED, PARTIAL vs. the book.** The stated theorem is
faithful and non-vacuous; the book's full part (b) classification list is not formalized.

## Group-name confirmations (issue checklist)

- `A₄ = alternatingGroup (Fin 4)` (order 12) — tetrahedral rotation group. ✓
- `S₄ = Equiv.Perm (Fin 4)` (order 24) — cube/octahedron rotation group. ✓
- `A₅ = alternatingGroup (Fin 5)` (order 60) — dodecahedron/icosahedron rotation group. ✓
- `DihedralGroup n` has order 2n (n ≥ 1) — matches "Dₙ of order 2n". ✓

## Recommendation

Open a follow-up **feature** issue to formalize the full part (b) classification list of
finite subgroups of SU(2), wiring `Problem4_12_8.su2_finite_subgroup_double_cover` and
`Problem4_12_8.so3_finite_subgroup_classification` to
`Problem4_12_7.exists_surjective_hom_to_SO3`, so that:
1. part (b) is instantiated on the concrete repo-internal double cover (removing the
   abstract-`h` hypothesis), and
2. the enumerated binary-polyhedral classification is a theorem, not only a docstring.

No `.lean` edits made in this PR (report-only Stage 3.7 audit).
