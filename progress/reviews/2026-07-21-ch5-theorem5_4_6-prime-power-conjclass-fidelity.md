# Statement-fidelity & non-vacuity audit — Theorem 5.4.6 (prime-power conjugacy class ⇒ not simple)

**Issue:** #7140
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session fdfdfdba)
**Scope:** report-only fidelity + non-vacuity audit of `Etingof.Theorem5_4_6`
**Verdict: FAITHFUL — axiom-clean, no defect. Nothing filed.**

## Sources compared

- **Book statement** (`blobs/Chapter5/Theorem5.4.6.md`):
  > **Theorem 5.4.6.** *Let $G$ be a finite group, and let $C$ be a conjugacy
  > class in $G$ of size $p^k$ where $p$ is a prime and $k > 0$. Then $G$ has a
  > proper nontrivial normal subgroup (i.e., $G$ is not simple).*
- **Book proof** (`blobs/Chapter5/Theorem5.4.6.md` +
  `blobs/Chapter5/Discussion_proof_of_Theorem5.4.6.md`): choose `g ∈ C`, `g ≠ e`;
  column orthogonality (5.4.1) `∑_{V∈Irr G} dim V · χ_V(g) = 0`; split `Irr G` into
  (1) trivial, (2) `D` = reps with `p ∣ dim`, (3) `N` = nontrivial reps with
  `p ∤ dim`; pick `V ∈ N` with `χ_V(g) ≠ 0` (Lemma 5.4.7); Theorem 5.4.4 makes `g`
  act by a scalar on `V`; then `H = ⟨ab⁻¹ : a,b ∈ C⟩` is normal, acts trivially on
  `V`, so `H ≠ G` (as `V` is nontrivial) and `H ≠ 1` (as `|C| > 1`).
- **Lean statement** (`EtingofRepresentationTheory/Chapter5/Theorem5_4_6.lean:342`):

```lean
theorem Etingof.Theorem5_4_6
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G)
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
```

## Fidelity checks (per issue deliverable 1)

### Conclusion faithfully renders "proper nontrivial normal subgroup / not simple"
- `∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤` is exactly "there is a normal
  subgroup that is neither trivial (`≠ ⊥`) nor the whole group (`≠ ⊤`)", i.e. a
  proper nontrivial normal subgroup. This is the standard negation of
  `IsSimpleGroup` (a group is simple iff every normal subgroup is `⊥` or `⊤`, in
  the presence of `Nontrivial`), so it correctly encodes "not simple". ✓
- **Not off-by-a-triviality / not vacuous on trivial `G`.** The `⊥ ≠`, `⊤ ≠`
  framing is the genuine "proper nontrivial" statement. For a trivial group the
  conclusion would be **false** (`⊥ = ⊤`, so no `N` can satisfy both `≠`), but the
  hypothesis is simultaneously **unsatisfiable** there: the proof opens
  (`Theorem5_4_6.lean:348-352`) by proving `g ≠ 1` from `hconj` — if `g = 1` then
  `card {h // IsConj 1 h} = 1` (local `card_conjClass_one`, line 201) while
  `p^k ≥ 2` (since `p ≥ 2`, `k ≥ 1`), a contradiction. So `k > 0` forces
  `|C| = p^k ≥ 2 > 1`, `g ≠ 1`, and `Nontrivial G` (derived at line 354). The
  theorem is therefore never applied to a trivial `G`, and the `⊥/⊤` framing is
  correct, not a hidden vacuity. ✓

### Hypothesis faithfully renders "conjugacy class `C` of size `pᵏ`, `p` prime, `k > 0`"
- `{ h : G // IsConj g h }` is the conjugacy class of `g`: `IsConj g h` unfolds to
  `∃ c, c * g * c⁻¹ = h`, so the subtype is exactly `{h : h is conjugate to g}`,
  and its `Fintype.card` is the conjugacy-class size `|C|`. Confirmed consistent
  with the local `card_conjClass_one` lemma, which computes this cardinality as `1`
  for `g = 1`. ✓
- `hp : Nat.Prime p` gives "`p` a prime"; `hk : 0 < k` gives "`k > 0`" — **strict**,
  not `k ≥ 0`. Strictness is load-bearing: it is what yields `|C| = p^k ≥ 2 > 1`
  (used both for `g ≠ 1` above and, inside the core lemma, to derive non-commutativity
  at lines 265-277 and `H ≠ 1` in the book). With `k = 0` the class could be `{g}`
  (size `1`) and the theorem would be false, so `0 < k` is correctly enforced. ✓
- `hconj : ... = p ^ k` pins the class size to `p^k` on the nose, with no extra
  clause. ✓

### The proof genuinely follows the book (not a short-circuit)
The mathematical core is the local `private lemma
IsSimpleGroup.no_prime_power_conjClass` (`Theorem5_4_6.lean:213`): *a simple finite
group has no conjugacy class of prime-power size*. The final theorem
(`:342`) is a by-contradiction wrapper — assume no proper nontrivial normal
subgroup exists, synthesize an `IsSimpleGroup G` instance (lines 355-359), and
apply the core lemma to get `False`.

The core lemma implements the book's ingredients, in order:

1. **Column orthogonality (5.4.1) appears explicitly.** Line 226 establishes
   `hsum : ∑ i : Fin D.n, (D.d i : ℂ) * (D.columnFDRep i).character g = 0` via the
   infrastructure lemma `sum_dim_character_eq_zero`
   (`Infrastructure/RegularCharacter.lean:160`), whose statement is
   `∑ i, (finrank (V i) : k) * (V i).character g = 0` for `g ≠ 1` over the irrep
   decomposition. This is identity (5.4.1) `∑_{V∈Irr G} dim V · χ_V(g) = 0`. ✓
2. **Three-way split.** The trivial rep is located (`i₀`, line 232, via a genuine
   `Simple` isomorphism from `trivialFDRep_simple`); its term is `1` (lines 235-245,
   `d_{i₀}=1`, `χ_{i₀}(g)=1`). For nontrivial reps with `p ∤ d_i`, line 247's
   `hcoprime_vanish` shows `χ(g) = 0`: it invokes **Theorem 5.4.4** (line 255,
   `Etingof.Theorem5_4_4`), which gives "either `χ = 0` or `g` acts by a scalar";
   the scalar branch is killed by `scalar_contradicts_simplicity` (line 278) using
   `IsSimpleGroup G` and `dim ≥ 2`. So only `p ∣ d_i` terms survive.
3. **Algebraic-integer contradiction.** The surviving sum is `-1` (line 294), and
   factoring out `p` gives `p · S = -1` (line 317) with `S` an algebraic integer
   (line 319, built from the local `character_isIntegral`). Hence `S = -1/p`, a
   rational algebraic integer, contradicting **Proposition 5.2.5**
   (`Etingof.Proposition5_2_5`, line 330, `ℤ̄ ∩ ℚ = ℤ`) via `p ∣ 1` (lines 335-338).

   `character_isIntegral` (`Theorem5_4_6.lean:26`) is a **local `private lemma**,
   *not* a Mathlib import: it proves character values are integral over `ℤ` from
   scratch (trace = sum of charpoly roots, each root an `|G|`-th root of unity,
   hence a root of the monic `Xⁿ - 1`). ✓ `no_prime_power_conjClass` is likewise a
   local `private lemma`, not a Mathlib result. ✓

This is a **faithful** rendering of the book's method, not a short-circuit to an
unrelated group-theoretic fact: it uses precisely the book's column orthogonality
(5.4.1), Theorem 5.4.4 (scalar action of coprime-dimension irreps), and Proposition
5.2.5 (rational algebraic integers are integers).

**Proof-shape nuance (not a defect).** The book's *Discussion* proof is
constructive — it builds the explicit normal subgroup `H = ⟨ab⁻¹ : a,b ∈ C⟩` and
uses **Lemma 5.4.7** to find a nonzero-character rep in `N`. The Lean proof instead
runs the classical *by-contradiction* form of the same Burnside argument: it assumes
`G` simple and derives the `S = -1/p` contradiction directly, so it does **not**
construct `H` and does **not** cite Lemma 5.4.7. Both are standard proofs of the
identical statement, and the Lean route's contradiction (`p · S = -1`, `S` an
algebraic integer) is the mathematical heart of the book's argument. The
existential conclusion `∃ N, ...` is recovered non-constructively from the negated
hypothesis; this affects only the *shape* of the proof, not statement fidelity or
non-vacuity. Recording it here for transparency; it is **not** a generalization or
a defect.

## Non-vacuity check (per issue deliverable 2)

**Axioms.** `#print axioms Etingof.Theorem5_4_6` reports exactly:

```
'Etingof.Theorem5_4_6' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` — the theorem and its **entire transitive dependency chain**
(`character_isIntegral`, `no_prime_power_conjClass`, `sum_dim_character_eq_zero`,
`Theorem5_4_4`, `Proposition5_2_5`, and all helper lemmas) are sorry-free. ✓

**Concrete non-vacuous instance.** Take `G = S₃` (the symmetric group on three
letters, `Equiv.Perm (Fin 3)`). Its conjugacy classes are `{e}` (size 1), the three
transpositions (size `3 = 3¹`), and the two 3-cycles (size `2 = 2¹`). Pick `g` a
transposition: then `Fintype.card {h // IsConj g h} = 3 = p^k` with `p = 3`,
`k = 1 > 0`, so every hypothesis is satisfied. `S₃` is genuinely **not** simple —
`A₃` is a proper nontrivial normal subgroup (index 2) — so the conclusion `∃ N,
N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤` holds non-vacuously (witnessed by `N = A₃`). The
hypothesis set is therefore inhabited and the theorem is not vacuously true. (The
3-cycle class, size `2 = 2¹`, gives a second witness with `p = 2`.)

## Build & verification

- `lake exe cache get` — cache present, no rebuild.
- `lake build EtingofRepresentationTheory.Chapter5.Theorem5_4_6` — **exit 0**
  ("Build completed successfully"). Two non-blocking lint warnings only:
  an `overlappingInstances` note on `nontrivial_irrep_dim_ge_two` (line 168,
  `[IsSimpleGroup G]` subsumes `[Nontrivial G]`) and a `push_neg` deprecation
  (line 353). Neither affects correctness; both are cosmetic.
- `#print axioms Etingof.Theorem5_4_6` — clean triple, reported above.

## Verdict

**FAITHFUL.** The Lean statement faithfully renders Theorem 5.4.6: the conclusion
is the genuine "proper nontrivial normal subgroup / not simple", the hypotheses are
exactly "conjugacy class of size `p^k`, `p` prime, `k > 0`" with the `⊥/⊤` framing
and `k > 0` strictness both load-bearing and correct (no trivial-group vacuity). The
proof genuinely uses the book's column orthogonality (5.4.1), Theorem 5.4.4, and
Proposition 5.2.5 through local, sorry-free lemmas; the only nuance is the classical
by-contradiction proof shape in place of the book's explicit `H = ⟨ab⁻¹⟩`
construction, which does not affect fidelity or non-vacuity. Axiom-clean, non-vacuous
(`S₃` witness). **No defect; no issue filed.**
