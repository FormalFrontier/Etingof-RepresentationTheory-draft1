import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar
import EtingofRepresentationTheory.Chapter6.FieldGenericETilde6
import EtingofRepresentationTheory.Chapter6.FieldGenericTube

/-!
# Orientation-Generic Ẽ₇ Construction (#2792)

F-generic, orientation-generic version of the Ẽ₇ representation for
T_{1,3,3}. This file provides `etilde7Rep_kQ`, its dimension-vector
lemma, an indecomposability stub (a single `sorry`, of a now-*true*
statement), and the per-(F, Q) infinite-type theorem.

Ẽ₇ is the affine `E₇` Dynkin diagram T_{1,3,3}: 8 vertices forming
three arms meeting at the center (vertex 0).

- Arm 1 (length 1): `0 — 1`
- Arm 2 (length 3): `0 — 2 — 3 — 4`
- Arm 3 (length 3): `0 — 5 — 6 — 7`

The canonical orientation (`etilde7Quiver`) directs all arrows toward
the center: `1 → 0`, `4 → 3 → 2 → 0`, `7 → 6 → 5 → 0`. For an
arbitrary orientation `Q` of `etilde7Adj`, each of the seven edges
may point either way, so the construction provides a forward and
reverse map per edge.

**Corrected homogeneous-tube construction (#4568).** The earlier
single-nilpotent-twist family was decomposable for every `m ≥ 1`
(audit #4542). `etilde7Rep_kQ` is now the genuine homogeneous tube
`R_λ^{(m+1)}` of the regular simple `S_λ` at `δ = (4;2;3,2,1;3,2,1)`:
arm 2 is the coordinate *prefix* flag, arm 3 the opposite *suffix*
flag, and arm 1 the eigenvalue 2-plane carrying `Λ = λ·id + J`. See
`progress/etilde7-tube-design.md` §7 for the explicit matrices and the
paper brick-proof (`End(S_λ) = F` for generic `λ`). The eigenvalue is
`etilde7TubeLam F`, a generic element of the infinite field `F`.

`etilde7Rep_kQ_isIndecomposable` is still a single `sorry`, but now of a
**true** statement (the soundness win of #4568); the assembly is sub-C
(#4570), modelled on `starTubeRepGen_isIndecomposable`.

See the "Naming conventions" section of
`Chapter6/FieldGenericInfiniteType.lean` for the meaning of the
`_F` / `_kQ` / `_per_kQ` suffixes used throughout this file.
-/

open scoped Matrix

namespace Etingof

/-! ## Section 0.5: Generic eigenvalue for the homogeneous tube

The homogeneous tube `R_λ^{(m+1)}` is a brick only at the *homogeneous*
points of `P¹`, i.e. for `λ` with `1, λ, λ², λ³` pairwise distinct (see
`progress/etilde7-tube-design.md` §7.2). Such `λ` exist in any infinite
field — in particular any algebraically closed `F` — because the bad set
is the finite root set of `∏_{i<j}(X^j − X^i)`. -/

/-- Some eigenvalue `λ` of the infinite field `F` with `1, λ, λ², λ³`
pairwise distinct (the homogeneity / brick condition of §7.2). -/
theorem exists_lam_distinct_powers (F : Type) [Field F] [IsAlgClosed F] :
    ∃ lam : F, ∀ i j : Fin 4, i ≠ j → lam ^ (i : ℕ) ≠ lam ^ (j : ℕ) := by
  classical
  set X := (Polynomial.X : Polynomial F) with hX
  have hfac : ∀ i j : ℕ, i < j → (X ^ j - X ^ i : Polynomial F) ≠ 0 := by
    intro i j hij hzero
    have hpow : (X ^ j : Polynomial F) = X ^ i := sub_eq_zero.mp hzero
    have hdeg := congrArg Polynomial.natDegree hpow
    rw [hX, Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hdeg
    omega
  set f : Polynomial F :=
    (X ^ 1 - X ^ 0) * (X ^ 2 - X ^ 0) * (X ^ 3 - X ^ 0) *
      (X ^ 2 - X ^ 1) * (X ^ 3 - X ^ 1) * (X ^ 3 - X ^ 2) with hf_def
  have hf : f ≠ 0 := by
    rw [hf_def]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (hfac 0 1 (by norm_num)) (hfac 0 2 (by norm_num))) (hfac 0 3 (by norm_num)))
      (hfac 1 2 (by norm_num))) (hfac 1 3 (by norm_num))) (hfac 2 3 (by norm_num))
  have hcard : (f.natDegree : Cardinal) < Cardinal.mk F :=
    lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.infinite_iff.mp inferInstance)
  obtain ⟨lam, hlam⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f hf hcard
  rw [hf_def] at hlam
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    hX, Polynomial.eval_X] at hlam
  rw [mul_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff,
    mul_ne_zero_iff] at hlam
  obtain ⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩ := hlam
  have key : ∀ a b : ℕ, a < b → b < 4 → lam ^ a ≠ lam ^ b := by
    intro a b hab hb
    have ha : a < 4 := by omega
    interval_cases a <;> interval_cases b <;>
      first
        | exact (sub_ne_zero.mp h01).symm
        | exact (sub_ne_zero.mp h02).symm
        | exact (sub_ne_zero.mp h03).symm
        | exact (sub_ne_zero.mp h12).symm
        | exact (sub_ne_zero.mp h13).symm
        | exact (sub_ne_zero.mp h23).symm
        | omega
  refine ⟨lam, fun i j hij => ?_⟩
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · exact key i j h j.isLt
  · exact absurd (Fin.ext h) hij
  · exact fun hpow => key j i h i.isLt hpow.symm

/-- A generic eigenvalue for the Ẽ₇ homogeneous tube: an element of the
infinite field `F` with `1, λ, λ², λ³` pairwise distinct (§7.2). -/
noncomputable def etilde7TubeLam (F : Type) [Field F] [IsAlgClosed F] : F :=
  Classical.choose (exists_lam_distinct_powers F)

/-- The defining property of `etilde7TubeLam`: its first four powers are
pairwise distinct. This is the brick / homogeneity hypothesis used by the
indecomposability assembly (sub-C, #4570). -/
theorem etilde7TubeLam_distinct (F : Type) [Field F] [IsAlgClosed F] :
    ∀ i j : Fin 4, i ≠ j →
      etilde7TubeLam F ^ (i : ℕ) ≠ etilde7TubeLam F ^ (j : ℕ) :=
  Classical.choose_spec (exists_lam_distinct_powers F)

/-! ## Section 1: F-generic forward maps for the Ẽ₇ homogeneous tube

Arm 2 enters the center `F^{4(m+1)}` as a coordinate **prefix** flag
(via `starEmbed1_F`, `prefixBlockEmbed_F`), arm 3 as the opposite
coordinate **suffix** flag (via `starEmbed2_F`, `suffixBlockEmbed_F`),
and arm 1 as the eigenvalue 2-plane carrying `Λ = λ·id + J`
(`etilde7Arm1Tube_F`). See `progress/etilde7-tube-design.md` §7.
-/

/-- Single-block placement `F^{m+1} → F^{4(m+1)}` at offset `o`:
`x ↦ (…, 0, x, 0, …)` with `x` occupying coordinates `[o, o + (m+1))`.
Used to assemble the four center blocks of the arm-1 tube map. -/
noncomputable def blockEmbedAt_F (F : Type) [Field F] (o m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (4 * (m + 1)) → F) where
  toFun x i := if h : o ≤ i.val ∧ i.val < o + (m + 1) then x ⟨i.val - o, by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- F-generic suffix-block embedding `F^{a(m+1)} → F^{b(m+1)}` placing the
input into the **last** `a` blocks: `x ↦ (0, …, 0, x)`. The opposite of
`prefixBlockEmbed_F`; realizes the arm-3 (suffix) flag. -/
noncomputable def suffixBlockEmbed_F (F : Type) [Field F] (a b m : ℕ) :
    (Fin (a * (m + 1)) → F) →ₗ[F] (Fin (b * (m + 1)) → F) where
  toFun x i :=
    if h : (b - a) * (m + 1) ≤ i.val ∧ i.val - (b - a) * (m + 1) < a * (m + 1) then
      x ⟨i.val - (b - a) * (m + 1), h.2⟩
    else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- F-generic last-`a`-blocks projection `F^{b(m+1)} → F^{a(m+1)}`:
`w ↦ (w_{(b-a)(m+1)}, …, w_{b(m+1)-1})`. Reverse map for the arm-3
suffix embeddings. -/
noncomputable def suffixBlockProj_F (F : Type) [Field F]
    (a b m : ℕ) (hab : a ≤ b) :
    (Fin (b * (m + 1)) → F) →ₗ[F] (Fin (a * (m + 1)) → F) where
  toFun w i :=
    w ⟨i.val + (b - a) * (m + 1), by
      have h2 : a * (m + 1) + (b - a) * (m + 1) = b * (m + 1) := by
        rw [← Nat.add_mul]; congr 1; omega
      have := i.isLt; omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Ẽ₇ arm-1 eigenvalue tube embedding `F^{2(m+1)} → F^{4(m+1)}`:
`(P, Q) ↦ (P + Q, P + ΛQ, P + Λ²Q, P + Λ³Q)`, where `Λ = λ·id + J`
(`jordanShiftLinGen`). The single λ-bearing map of the tube; full column
rank for `λ ≠ 1`, full-rank-coupling block D (`e4`) to block C
(`e3 = q`) through the eigenvalue site (defeating the §1 peeling —
design §7.3). -/
noncomputable def etilde7Arm1Tube_F (F : Type) [Field F] (lam : F) (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (4 * (m + 1)) → F) :=
  let Λ := jordanShiftLinGen F lam m
  let P := starFirst_F F m
  let Q := starSecond_F F m
  (blockEmbedAt_F F 0 m).comp (P + Q)
    + (blockEmbedAt_F F (m + 1) m).comp (P + Λ.comp Q)
    + (blockEmbedAt_F F (2 * (m + 1)) m).comp (P + (Λ.comp Λ).comp Q)
    + (blockEmbedAt_F F (3 * (m + 1)) m).comp (P + (Λ.comp (Λ.comp Λ)).comp Q)

/-! ## Section 2: Orientation-independent flag-collapse foundation (sub-B1, #4569)

The 4-block analogue of the Ẽ₆ Section 0c/0d infrastructure
(`FieldGenericETilde6.lean`). The center `F^{4(m+1)}` splits as four
coordinate blocks `(c₀, c₁, c₂, c₃)`, each a copy of `F^{m+1}` placed by
`blockEmbedAt_F` at offsets `0, m+1, 2(m+1), 3(m+1)`. The canonical arm-2
prefix flag (`4→3→2→0`) deposits the leaf-4 datum into center **block 0**;
the canonical arm-3 suffix flag (`7→6→5→0`) deposits the leaf-7 datum into
center **block 3**. The arm-1 eigenvalue site (`etilde7Arm1Tube_F`) is the
only coupling between block 0 and block 3 (design §7.3) and is handled
separately by the orientation case-tree assembly (sub-B2, #4642), which
consumes the block-projection, center-decomposition, and arm leaf→center
membership criteria below. -/

/-- Single-block projection `F^{4(m+1)} → F^{m+1}` reading the block at
offset `o`: `w ↦ (w_o, …, w_{o+m})`. Left inverse of `blockEmbedAt_F o`
when the block fits (`o + (m+1) ≤ 4(m+1)`). The projection counterpart of
`blockEmbedAt_F`. -/
noncomputable def blockProjAt_F (F : Type) [Field F] (o m : ℕ)
    (ho : o + (m + 1) ≤ 4 * (m + 1)) :
    (Fin (4 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨o + i.val, by have := i.isLt; omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- `blockProjAt_F o` is a left inverse of `blockEmbedAt_F o`: reading back
the block just deposited returns the original datum. -/
theorem blockProjAt_comp_embedAt_F (F : Type) [Field F] (o m : ℕ)
    (ho : o + (m + 1) ≤ 4 * (m + 1)) (x : Fin (m + 1) → F) :
    blockProjAt_F F o m ho (blockEmbedAt_F F o m x) = x := by
  funext ⟨i, hi⟩
  simp only [blockProjAt_F, blockEmbedAt_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (show o ≤ o + i ∧ o + i < o + (m + 1) from ⟨Nat.le_add_right _ _, by omega⟩)]
  congr 1
  simp only [Fin.mk.injEq]; omega

/-- Off-diagonal block projection vanishes: reading block `o` of a datum
deposited in a disjoint block `o'` returns zero. -/
theorem blockProjAt_embedAt_disjoint_F (F : Type) [Field F] (o o' m : ℕ)
    (ho : o + (m + 1) ≤ 4 * (m + 1))
    (hd : o + (m + 1) ≤ o' ∨ o' + (m + 1) ≤ o) (x : Fin (m + 1) → F) :
    blockProjAt_F F o m ho (blockEmbedAt_F F o' m x) = 0 := by
  funext ⟨i, hi⟩
  simp only [blockProjAt_F, blockEmbedAt_F, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  rw [dif_neg (show ¬(o' ≤ o + i ∧ o + i < o' + (m + 1)) from by omega)]

/-- Every center vector decomposes as the sum of its four single-block
embeddings via the four block projections. The 4-block analogue of
`center3_decomp_F` (`FieldGenericETilde6.lean`). -/
theorem etilde7_center_decomp_F (F : Type) [Field F] (m : ℕ)
    (w : Fin (4 * (m + 1)) → F) :
    w = blockEmbedAt_F F 0 m (blockProjAt_F F 0 m (by omega) w) +
        blockEmbedAt_F F (m + 1) m (blockProjAt_F F (m + 1) m (by omega) w) +
        blockEmbedAt_F F (2 * (m + 1)) m (blockProjAt_F F (2 * (m + 1)) m (by omega) w) +
        blockEmbedAt_F F (3 * (m + 1)) m (blockProjAt_F F (3 * (m + 1)) m (by omega) w) := by
  ext ⟨j, hj⟩
  simp only [Pi.add_apply, blockEmbedAt_F, blockProjAt_F, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h0 : j < m + 1
  · rw [dif_pos (show 0 ≤ j ∧ j < 0 + (m + 1) from ⟨Nat.zero_le _, by omega⟩),
        dif_neg (show ¬(m + 1 ≤ j ∧ j < m + 1 + (m + 1)) from by omega),
        dif_neg (show ¬(2 * (m + 1) ≤ j ∧ j < 2 * (m + 1) + (m + 1)) from by omega),
        dif_neg (show ¬(3 * (m + 1) ≤ j ∧ j < 3 * (m + 1) + (m + 1)) from by omega),
        add_zero, add_zero, add_zero]
    congr 1; simp only [Fin.mk.injEq]; omega
  · by_cases h1 : j < 2 * (m + 1)
    · rw [dif_neg (show ¬(0 ≤ j ∧ j < 0 + (m + 1)) from by omega),
          dif_pos (show m + 1 ≤ j ∧ j < m + 1 + (m + 1) from by omega),
          dif_neg (show ¬(2 * (m + 1) ≤ j ∧ j < 2 * (m + 1) + (m + 1)) from by omega),
          dif_neg (show ¬(3 * (m + 1) ≤ j ∧ j < 3 * (m + 1) + (m + 1)) from by omega),
          add_zero, add_zero, zero_add]
      congr 1; simp only [Fin.mk.injEq]; omega
    · by_cases h2 : j < 3 * (m + 1)
      · rw [dif_neg (show ¬(0 ≤ j ∧ j < 0 + (m + 1)) from by omega),
            dif_neg (show ¬(m + 1 ≤ j ∧ j < m + 1 + (m + 1)) from by omega),
            dif_pos (show 2 * (m + 1) ≤ j ∧ j < 2 * (m + 1) + (m + 1) from by omega),
            dif_neg (show ¬(3 * (m + 1) ≤ j ∧ j < 3 * (m + 1) + (m + 1)) from by omega),
            add_zero, zero_add, zero_add]
        congr 1; simp only [Fin.mk.injEq]; omega
      · rw [dif_neg (show ¬(0 ≤ j ∧ j < 0 + (m + 1)) from by omega),
            dif_neg (show ¬(m + 1 ≤ j ∧ j < m + 1 + (m + 1)) from by omega),
            dif_neg (show ¬(2 * (m + 1) ≤ j ∧ j < 2 * (m + 1) + (m + 1)) from by omega),
            dif_pos (show 3 * (m + 1) ≤ j ∧ j < 3 * (m + 1) + (m + 1) from by omega),
            zero_add, zero_add, zero_add]
        congr 1; simp only [Fin.mk.injEq]; omega

/-- The four single-block embeddings are disjoint at the center:
`blockEmbedAt 0 x₀ + blockEmbedAt (m+1) x₁ + blockEmbedAt 2(m+1) x₂ +
blockEmbedAt 3(m+1) x₃ = 0 → x₀ = x₁ = x₂ = x₃ = 0`. The 4-block analogue
of `center3_sum_zero_F` (`FieldGenericETilde6.lean`). -/
theorem etilde7_center_sum_zero_F (F : Type) [Field F] (m : ℕ)
    (x0 x1 x2 x3 : Fin (m + 1) → F)
    (h : blockEmbedAt_F F 0 m x0 + blockEmbedAt_F F (m + 1) m x1
        + blockEmbedAt_F F (2 * (m + 1)) m x2 + blockEmbedAt_F F (3 * (m + 1)) m x3 = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hp := congrArg (blockProjAt_F F 0 m (by omega)) h
    simpa only [map_add, map_zero, blockProjAt_comp_embedAt_F,
      blockProjAt_embedAt_disjoint_F F 0 (m + 1) m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F 0 (2 * (m + 1)) m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F 0 (3 * (m + 1)) m (by omega) (by omega),
      add_zero] using hp
  · have hp := congrArg (blockProjAt_F F (m + 1) m (by omega)) h
    simpa only [map_add, map_zero, blockProjAt_comp_embedAt_F,
      blockProjAt_embedAt_disjoint_F F (m + 1) 0 m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F (m + 1) (2 * (m + 1)) m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F (m + 1) (3 * (m + 1)) m (by omega) (by omega),
      add_zero, zero_add] using hp
  · have hp := congrArg (blockProjAt_F F (2 * (m + 1)) m (by omega)) h
    simpa only [map_add, map_zero, blockProjAt_comp_embedAt_F,
      blockProjAt_embedAt_disjoint_F F (2 * (m + 1)) 0 m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F (2 * (m + 1)) (m + 1) m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F (2 * (m + 1)) (3 * (m + 1)) m (by omega) (by omega),
      add_zero, zero_add] using hp
  · have hp := congrArg (blockProjAt_F F (3 * (m + 1)) m (by omega)) h
    simpa only [map_add, map_zero, blockProjAt_comp_embedAt_F,
      blockProjAt_embedAt_disjoint_F F (3 * (m + 1)) 0 m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F (3 * (m + 1)) (m + 1) m (by omega) (by omega),
      blockProjAt_embedAt_disjoint_F F (3 * (m + 1)) (2 * (m + 1)) m (by omega) (by omega),
      add_zero, zero_add] using hp

/-- Arm-2 (prefix flag) leaf-4 → center composite for the canonical
orientation `4→3→2→0`:
`x ↦ (x, 0, 0, 0)`, i.e. the chain
`prefixBlockEmbed_F 3 4 ∘ prefixBlockEmbed_F 2 3 ∘ starEmbed1_F`. Its image
is the leaf-4 line in center block 0. -/
noncomputable def etilde7PrefixArmComp_F (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (4 * (m + 1)) → F) :=
  (prefixBlockEmbed_F F 3 4 m).comp ((prefixBlockEmbed_F F 2 3 m).comp (starEmbed1_F F m))

/-- Arm-3 (suffix flag) leaf-7 → center composite for the canonical
orientation `7→6→5→0`:
`x ↦ (0, 0, 0, x)`, i.e. the chain
`suffixBlockEmbed_F 3 4 ∘ suffixBlockEmbed_F 2 3 ∘ starEmbed2_F`. Its image
is the leaf-7 line in center block 3. -/
noncomputable def etilde7SuffixArmComp_F (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (4 * (m + 1)) → F) :=
  (suffixBlockEmbed_F F 3 4 m).comp ((suffixBlockEmbed_F F 2 3 m).comp (starEmbed2_F F m))

/-- The arm-2 prefix composite deposits the leaf-4 datum into center
**block 0**: `etilde7PrefixArmComp_F = blockEmbedAt_F 0`. -/
theorem etilde7_prefixArm_comp_F (F : Type) [Field F] (m : ℕ) (x : Fin (m + 1) → F) :
    etilde7PrefixArmComp_F F m x = blockEmbedAt_F F 0 m x := by
  funext ⟨i, hi⟩
  simp only [etilde7PrefixArmComp_F, LinearMap.comp_apply, prefixBlockEmbed_F, starEmbed1_F,
    blockEmbedAt_F, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h0 : i < m + 1
  · rw [dif_pos (show i < 3 * (m + 1) from by omega), dif_pos (show i < 2 * (m + 1) from by omega),
        dif_pos (show i < m + 1 from h0),
        dif_pos (show 0 ≤ i ∧ i < 0 + (m + 1) from ⟨Nat.zero_le _, by omega⟩)]
    simp only [Nat.sub_zero]
  · rw [dif_neg (show ¬(0 ≤ i ∧ i < 0 + (m + 1)) from by omega)]
    by_cases h1 : i < 3 * (m + 1)
    · rw [dif_pos h1]
      by_cases h2 : i < 2 * (m + 1)
      · rw [dif_pos h2, dif_neg (show ¬ i < m + 1 from h0)]
      · rw [dif_neg h2]
    · rw [dif_neg h1]

/-- The arm-3 suffix composite deposits the leaf-7 datum into center
**block 3**: `etilde7SuffixArmComp_F = blockEmbedAt_F 3(m+1)`. -/
theorem etilde7_suffixArm_comp_F (F : Type) [Field F] (m : ℕ) (x : Fin (m + 1) → F) :
    etilde7SuffixArmComp_F F m x = blockEmbedAt_F F (3 * (m + 1)) m x := by
  funext ⟨i, hi⟩
  simp only [etilde7SuffixArmComp_F, LinearMap.comp_apply, suffixBlockEmbed_F, starEmbed2_F,
    blockEmbedAt_F, LinearMap.coe_mk, AddHom.coe_mk]
  -- suffixBlockEmbed 3 4: offset (4-3)(m+1) = m+1; suffixBlockEmbed 2 3: offset (3-2)(m+1) = m+1
  by_cases h3 : 3 * (m + 1) ≤ i
  · -- top block: both suffix conditions hold, starEmbed2 condition holds
    rw [dif_pos (show (4 - 3) * (m + 1) ≤ i ∧ i - (4 - 3) * (m + 1) < 3 * (m + 1) from by omega),
        dif_pos (show (3 - 2) * (m + 1) ≤ i - (4 - 3) * (m + 1)
          ∧ i - (4 - 3) * (m + 1) - (3 - 2) * (m + 1) < 2 * (m + 1) from by omega),
        dif_pos (show m + 1 ≤ i - (4 - 3) * (m + 1) - (3 - 2) * (m + 1) from by omega),
        dif_pos (show 3 * (m + 1) ≤ i ∧ i < 3 * (m + 1) + (m + 1) from by omega)]
    congr 1; simp only [Fin.mk.injEq]; omega
  · rw [dif_neg (show ¬(3 * (m + 1) ≤ i ∧ i < 3 * (m + 1) + (m + 1)) from by omega)]
    by_cases h2 : (4 - 3) * (m + 1) ≤ i ∧ i - (4 - 3) * (m + 1) < 3 * (m + 1)
    · rw [dif_pos h2]
      by_cases h1 : (3 - 2) * (m + 1) ≤ i - (4 - 3) * (m + 1)
          ∧ i - (4 - 3) * (m + 1) - (3 - 2) * (m + 1) < 2 * (m + 1)
      · rw [dif_pos h1,
          dif_neg (show ¬(m + 1 ≤ i - (4 - 3) * (m + 1) - (3 - 2) * (m + 1)) from by omega)]
      · rw [dif_neg h1]
    · rw [dif_neg h2]

/-- The arm-2 prefix leaf→center composite is injective (left inverse
`blockProjAt_F 0`). -/
theorem etilde7PrefixArmComp_F_injective (F : Type) [Field F] (m : ℕ) :
    Function.Injective (etilde7PrefixArmComp_F F m) := by
  apply Function.LeftInverse.injective (g := blockProjAt_F F 0 m (by omega))
  intro x
  rw [etilde7_prefixArm_comp_F]
  exact blockProjAt_comp_embedAt_F F 0 m (by omega) x

/-- The arm-3 suffix leaf→center composite is injective (left inverse
`blockProjAt_F 3(m+1)`). -/
theorem etilde7SuffixArmComp_F_injective (F : Type) [Field F] (m : ℕ) :
    Function.Injective (etilde7SuffixArmComp_F F m) := by
  apply Function.LeftInverse.injective (g := blockProjAt_F F (3 * (m + 1)) m (by omega))
  intro x
  rw [etilde7_suffixArm_comp_F]
  exact blockProjAt_comp_embedAt_F F (3 * (m + 1)) m (by omega) x

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Arm-2 three-level membership criterion (canonical `4→3→2→0`): for a
complementary invariant pair, the leaf-4 datum lies in `W₁(leaf 4)` iff its
center deposit `(x,0,0,0)` lies in `W₁(center 0)`. The arm-2 analogue of
`etilde6_armB_criterion` with the extra prefix hop. -/
theorem etilde7_prefixArm_collapse_F
    (F : Type) [Field F] (m : ℕ)
    (W0₁ W0₂ : Submodule F (Fin (4 * (m + 1)) → F))
    (W2₁ W2₂ : Submodule F (Fin (3 * (m + 1)) → F))
    (W3₁ W3₂ : Submodule F (Fin (2 * (m + 1)) → F))
    (W4₁ W4₂ : Submodule F (Fin (m + 1) → F))
    (hc0 : IsCompl W0₁ W0₂) (hc4 : IsCompl W4₁ W4₂)
    (h43₁ : ∀ x ∈ W4₁, starEmbed1_F F m x ∈ W3₁)
    (h32₁ : ∀ y ∈ W3₁, prefixBlockEmbed_F F 2 3 m y ∈ W2₁)
    (h20₁ : ∀ z ∈ W2₁, prefixBlockEmbed_F F 3 4 m z ∈ W0₁)
    (h43₂ : ∀ x ∈ W4₂, starEmbed1_F F m x ∈ W3₂)
    (h32₂ : ∀ y ∈ W3₂, prefixBlockEmbed_F F 2 3 m y ∈ W2₂)
    (h20₂ : ∀ z ∈ W2₂, prefixBlockEmbed_F F 3 4 m z ∈ W0₂)
    (x : Fin (m + 1) → F) :
    x ∈ W4₁ ↔ etilde7PrefixArmComp_F F m x ∈ W0₁ := by
  refine leaf_center_mem_iff_of_forward (etilde7PrefixArmComp_F F m)
    (etilde7PrefixArmComp_F_injective F m) W4₁ W4₂ W0₁ W0₂ hc4 hc0 ?_ ?_ x
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [etilde7PrefixArmComp_F, LinearMap.comp_apply] using h20₁ _ (h32₁ _ (h43₁ z hz))
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [etilde7PrefixArmComp_F, LinearMap.comp_apply] using h20₂ _ (h32₂ _ (h43₂ z hz))

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Arm-3 three-level membership criterion (canonical `7→6→5→0`): for a
complementary invariant pair, the leaf-7 datum lies in `W₁(leaf 7)` iff its
center deposit `(0,0,0,x)` lies in `W₁(center 0)`. The arm-3 (suffix-flag)
analogue of `etilde7_prefixArm_collapse_F`. -/
theorem etilde7_suffixArm_collapse_F
    (F : Type) [Field F] (m : ℕ)
    (W0₁ W0₂ : Submodule F (Fin (4 * (m + 1)) → F))
    (W5₁ W5₂ : Submodule F (Fin (3 * (m + 1)) → F))
    (W6₁ W6₂ : Submodule F (Fin (2 * (m + 1)) → F))
    (W7₁ W7₂ : Submodule F (Fin (m + 1) → F))
    (hc0 : IsCompl W0₁ W0₂) (hc7 : IsCompl W7₁ W7₂)
    (h76₁ : ∀ x ∈ W7₁, starEmbed2_F F m x ∈ W6₁)
    (h65₁ : ∀ y ∈ W6₁, suffixBlockEmbed_F F 2 3 m y ∈ W5₁)
    (h50₁ : ∀ z ∈ W5₁, suffixBlockEmbed_F F 3 4 m z ∈ W0₁)
    (h76₂ : ∀ x ∈ W7₂, starEmbed2_F F m x ∈ W6₂)
    (h65₂ : ∀ y ∈ W6₂, suffixBlockEmbed_F F 2 3 m y ∈ W5₂)
    (h50₂ : ∀ z ∈ W5₂, suffixBlockEmbed_F F 3 4 m z ∈ W0₂)
    (x : Fin (m + 1) → F) :
    x ∈ W7₁ ↔ etilde7SuffixArmComp_F F m x ∈ W0₁ := by
  refine leaf_center_mem_iff_of_forward (etilde7SuffixArmComp_F F m)
    (etilde7SuffixArmComp_F_injective F m) W7₁ W7₂ W0₁ W0₂ hc7 hc0 ?_ ?_ x
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [etilde7SuffixArmComp_F, LinearMap.comp_apply] using h50₁ _ (h65₁ _ (h76₁ z hz))
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [etilde7SuffixArmComp_F, LinearMap.comp_apply] using h50₂ _ (h65₂ _ (h76₂ z hz))

/-! ## Section 3: Orientation-generic Ẽ₇ homogeneous-tube representation

The map function is a match on `(a.val, b.val)` over the seven canonical
edges (arrow toward the center) plus the seven reversed edges. Arm 1 is
the eigenvalue tube; arm 2 the prefix flag; arm 3 the suffix flag.
Outside those 14 edge pairs the map is `0` (these arrows do not exist in
any orientation of `etilde7Adj`).
-/

/-- Direction-aware match-based map function for the orientation-generic
Ẽ₇ homogeneous-tube representation at eigenvalue `lam`. -/
private noncomputable def etilde7RepMap_kQ (F : Type) [Field F] (lam : F)
    (m : ℕ) (a b : Fin 8) :
    (Fin (etilde7Dim m a) → F) →ₗ[F] (Fin (etilde7Dim m b) → F) :=
  match a, b with
  -- Arm 1 (eigenvalue 2-plane): edge {0, 1}
  | ⟨1, _⟩, ⟨0, _⟩ => etilde7Arm1Tube_F F lam m
  | ⟨0, _⟩, ⟨1, _⟩ => prefixBlockProj_F F 2 4 m (by omega)
  -- Arm 2 (prefix flag): edge {3, 4}
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1_F F m
  | ⟨3, _⟩, ⟨4, _⟩ => starFirst_F F m
  -- Arm 2 (prefix flag): edge {2, 3}
  | ⟨3, _⟩, ⟨2, _⟩ => prefixBlockEmbed_F F 2 3 m
  | ⟨2, _⟩, ⟨3, _⟩ => prefixBlockProj_F F 2 3 m (by omega)
  -- Arm 2 (prefix flag): edge {0, 2}
  | ⟨2, _⟩, ⟨0, _⟩ => prefixBlockEmbed_F F 3 4 m
  | ⟨0, _⟩, ⟨2, _⟩ => prefixBlockProj_F F 3 4 m (by omega)
  -- Arm 3 (suffix flag): edge {6, 7}
  | ⟨7, _⟩, ⟨6, _⟩ => starEmbed2_F F m
  | ⟨6, _⟩, ⟨7, _⟩ => starSecond_F F m
  -- Arm 3 (suffix flag): edge {5, 6}
  | ⟨6, _⟩, ⟨5, _⟩ => suffixBlockEmbed_F F 2 3 m
  | ⟨5, _⟩, ⟨6, _⟩ => suffixBlockProj_F F 2 3 m (by omega)
  -- Arm 3 (suffix flag): edge {0, 5}
  | ⟨5, _⟩, ⟨0, _⟩ => suffixBlockEmbed_F F 3 4 m
  | ⟨0, _⟩, ⟨5, _⟩ => suffixBlockProj_F F 3 4 m (by omega)
  -- Non-edge or impossible (ruled out by `hOrient`); placeholder
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic Ẽ₇ (= T_{1,3,3}) representation over an arbitrary
field `F` with arbitrary orientation `Q` of `etilde7Adj`. Dimension vector
follows `etilde7Dim`: vertex 0 has dim `4(m+1)`, vertices 2/5 have dim
`3(m+1)`, vertices 1/3/6 have dim `2(m+1)`, vertices 4/7 have dim `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the seven
edges of `etilde7Adj` contributes one canonical map (matching
`etilde7RepMap`) and one reverse map (defined in Section 2). The
orientation hypothesis `hOrient` is not used by the construction
itself; it is recorded so that downstream lemmas (the
indecomposability proof for the inherited framework wall) can
pattern-match on which arrows exist. -/
noncomputable def etilde7Rep_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 8) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (etilde7Dim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => etilde7RepMap_kQ F (etilde7TubeLam F) m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic Ẽ₇ rep has the expected dimension vector
`etilde7Dim m` at each vertex. -/
theorem etilde7Rep_kQ_dimVec
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ) (v : Fin 8) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 8) _ Q
      (etilde7Rep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (etilde7Dim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 3b: Obj-form canonical flag-collapse criteria (sub-B2, #4642)

The two foundation membership criteria (`etilde7_prefixArm_collapse_F`,
`etilde7_suffixArm_collapse_F`) are stated over the **concrete** carrier spaces
`Fin (k·(m+1)) → F`. The leaf-equality assembly works with the **obj-typed**
invariant pair `W₁ W₂ : ∀ v, Submodule F ((etilde7Rep_kQ …).obj v)`. The two
lemmas below bridge the gap for the canonical (all-toward-center) orientation:
given the three canonical prefix-arm arrows `4→3→2→0` (resp. suffix-arm arrows
`7→6→5→0`), the leaf-4 datum lies in `W₁⟨4⟩` iff its center-block-0 deposit lies
in `W₁⟨0⟩` (resp. leaf-7 ↔ block-3). The chain containments the concrete
criteria need are derived from obj-typed invariance by reducing the rep's
`mapLinear` along each arrow (`simp only [etilde7Rep_kQ, etilde7RepMap_kQ]`, the
d6tilde `chain_collapse` pattern). These are the orientation-independent half of
the canonical leaf-equality branch; the eigenvalue-coupled arm-1 core that links
block 0 to block 3 is left to the follow-up. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- **Obj-form arm-2 (prefix flag) leaf→center collapse criterion** for the
canonical orientation `4→3→2→0`. Given a complementary invariant pair
`(W₁, W₂)` over `etilde7Rep_kQ` and the three canonical prefix-arm arrows, the
leaf-4 datum lies in `W₁⟨4⟩` iff its leaf→center deposit (the obj-typed
`mapLinear` composite along `4→3→2→0`, concretely `blockEmbedAt_F 0`) lies in
`W₁⟨0⟩`. Obj-form criterion built directly from `leaf_center_mem_iff_of_forward`:
the `.map`-containments come from `W`-invariance along the arrows, injectivity
descends through `etilde7PrefixArmComp_F_injective` after reducing the composite
to its concrete prefix-flag form. Stays obj-typed to sidestep the `etilde7Dim`
match-reduction wall (obstacle #1 of the sub-B2 investigation). -/
theorem etilde7Rep_kQ_prefixArm_collapse
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((etilde7Rep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (etilde7Rep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (etilde7Rep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v))
    (a43 : @Quiver.Hom _ Q ⟨4, by omega⟩ ⟨3, by omega⟩)
    (a32 : @Quiver.Hom _ Q ⟨3, by omega⟩ ⟨2, by omega⟩)
    (a20 : @Quiver.Hom _ Q ⟨2, by omega⟩ ⟨0, by omega⟩)
    (x : (etilde7Rep_kQ F Q hOrient m).obj ⟨4, by omega⟩) :
    x ∈ W₁ _ ↔
      (etilde7Rep_kQ F Q hOrient m).mapLinear a20
        ((etilde7Rep_kQ F Q hOrient m).mapLinear a32
          ((etilde7Rep_kQ F Q hOrient m).mapLinear a43 x)) ∈ W₁ _ := by
  letI := Q
  -- Work with the rep's own obj-typed leaf→center composite, avoiding the
  -- `etilde7Dim` match-reduction wall (instance synthesis won't unfold it, but
  -- term-mode defeq at the leaves does). Containments come from invariance;
  -- injectivity descends through `etilde7PrefixArmComp_F` after reducing the
  -- composite to its concrete prefix-flag form. The leaf/center obj-types are a
  -- stuck `match` so their algebraic instances are not found by synthesis; we
  -- pin them by `inferInstanceAs` (default-transparency defeq reduces the match).
  letI : AddCommGroup ((etilde7Rep_kQ F Q hOrient m).obj ⟨4, by omega⟩) :=
    inferInstanceAs (AddCommGroup (Fin (etilde7Dim m ⟨4, by omega⟩) → F))
  letI : Module F ((etilde7Rep_kQ F Q hOrient m).obj ⟨4, by omega⟩) :=
    inferInstanceAs (Module F (Fin (etilde7Dim m ⟨4, by omega⟩) → F))
  letI : AddCommGroup ((etilde7Rep_kQ F Q hOrient m).obj ⟨0, by omega⟩) :=
    inferInstanceAs (AddCommGroup (Fin (etilde7Dim m ⟨0, by omega⟩) → F))
  letI : Module F ((etilde7Rep_kQ F Q hOrient m).obj ⟨0, by omega⟩) :=
    inferInstanceAs (Module F (Fin (etilde7Dim m ⟨0, by omega⟩) → F))
  refine leaf_center_mem_iff_of_forward
    (((etilde7Rep_kQ F Q hOrient m).mapLinear a20).comp
      (((etilde7Rep_kQ F Q hOrient m).mapLinear a32).comp
        ((etilde7Rep_kQ F Q hOrient m).mapLinear a43)))
    ?hinj (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩) (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
    (hcompl ⟨4, by omega⟩) (hcompl ⟨0, by omega⟩) ?h1 ?h2 x
  case hinj =>
    intro p q hpq
    simp only [LinearMap.comp_apply, etilde7Rep_kQ, etilde7RepMap_kQ] at hpq
    exact etilde7PrefixArmComp_F_injective F m
      (by simpa only [etilde7PrefixArmComp_F, LinearMap.comp_apply] using hpq)
  case h1 =>
    rintro _ ⟨p, hp, rfl⟩
    exact hW₁_inv a20 _ (hW₁_inv a32 _ (hW₁_inv a43 p hp))
  case h2 =>
    rintro _ ⟨p, hp, rfl⟩
    exact hW₂_inv a20 _ (hW₂_inv a32 _ (hW₂_inv a43 p hp))

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- **Obj-form arm-3 (suffix flag) leaf→center collapse criterion** for the
canonical orientation `7→6→5→0`. Given a complementary invariant pair
`(W₁, W₂)` over `etilde7Rep_kQ` and the three canonical suffix-arm arrows, the
leaf-7 datum lies in `W₁⟨7⟩` iff its leaf→center deposit (the obj-typed
`mapLinear` composite along `7→6→5→0`, concretely `blockEmbedAt_F 3(m+1)`) lies
in `W₁⟨0⟩`. Obj-form criterion built directly from
`leaf_center_mem_iff_of_forward`, the arm-3 (suffix-flag) analogue of
`etilde7Rep_kQ_prefixArm_collapse`. -/
theorem etilde7Rep_kQ_suffixArm_collapse
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((etilde7Rep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (etilde7Rep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (etilde7Rep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v))
    (a76 : @Quiver.Hom _ Q ⟨7, by omega⟩ ⟨6, by omega⟩)
    (a65 : @Quiver.Hom _ Q ⟨6, by omega⟩ ⟨5, by omega⟩)
    (a50 : @Quiver.Hom _ Q ⟨5, by omega⟩ ⟨0, by omega⟩)
    (x : (etilde7Rep_kQ F Q hOrient m).obj ⟨7, by omega⟩) :
    x ∈ W₁ _ ↔
      (etilde7Rep_kQ F Q hOrient m).mapLinear a50
        ((etilde7Rep_kQ F Q hOrient m).mapLinear a65
          ((etilde7Rep_kQ F Q hOrient m).mapLinear a76 x)) ∈ W₁ _ := by
  letI := Q
  letI : AddCommGroup ((etilde7Rep_kQ F Q hOrient m).obj ⟨7, by omega⟩) :=
    inferInstanceAs (AddCommGroup (Fin (etilde7Dim m ⟨7, by omega⟩) → F))
  letI : Module F ((etilde7Rep_kQ F Q hOrient m).obj ⟨7, by omega⟩) :=
    inferInstanceAs (Module F (Fin (etilde7Dim m ⟨7, by omega⟩) → F))
  letI : AddCommGroup ((etilde7Rep_kQ F Q hOrient m).obj ⟨0, by omega⟩) :=
    inferInstanceAs (AddCommGroup (Fin (etilde7Dim m ⟨0, by omega⟩) → F))
  letI : Module F ((etilde7Rep_kQ F Q hOrient m).obj ⟨0, by omega⟩) :=
    inferInstanceAs (Module F (Fin (etilde7Dim m ⟨0, by omega⟩) → F))
  refine leaf_center_mem_iff_of_forward
    (((etilde7Rep_kQ F Q hOrient m).mapLinear a50).comp
      (((etilde7Rep_kQ F Q hOrient m).mapLinear a65).comp
        ((etilde7Rep_kQ F Q hOrient m).mapLinear a76)))
    ?hinj (W₁ ⟨7, by omega⟩) (W₂ ⟨7, by omega⟩) (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
    (hcompl ⟨7, by omega⟩) (hcompl ⟨0, by omega⟩) ?h1 ?h2 x
  case hinj =>
    intro p q hpq
    simp only [LinearMap.comp_apply, etilde7Rep_kQ, etilde7RepMap_kQ] at hpq
    exact etilde7SuffixArmComp_F_injective F m
      (by simpa only [etilde7SuffixArmComp_F, LinearMap.comp_apply] using hpq)
  case h1 =>
    rintro _ ⟨p, hp, rfl⟩
    exact hW₁_inv a50 _ (hW₁_inv a65 _ (hW₁_inv a76 p hp))
  case h2 =>
    rintro _ ⟨p, hp, rfl⟩
    exact hW₂_inv a50 _ (hW₂_inv a65 _ (hW₂_inv a76 p hp))

/-! ## Section 4: Indecomposability (corrected homogeneous tube)

`etilde7Rep_kQ` is now the genuine homogeneous tube `R_λ^{(m+1)}` at the
generic eigenvalue `etilde7TubeLam F` (§7 of
`progress/etilde7-tube-design.md`), so the statement below is **true**.
The single `sorry` is the indecomposability *proof*, deferred to sub-C
(#4570), which assembles it via the `core` / `propagate` collapse and
`eigenvalue_jordan_invariant_compl_trivial_gen` reduction — the template
is `starTubeRepGen_isIndecomposable` (`FieldGenericTube.lean`). The
earlier refuted single-twist construction (audit #4542) has been
replaced; the §1 peeling pair is defeated (design §7.3).
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of the corrected Ẽ₇
homogeneous-tube representation `etilde7Rep_kQ`.

This is now a **true** statement: `etilde7Rep_kQ` is the homogeneous tube
`R_λ^{(m+1)}` of the regular simple `S_λ` (a brick for the generic
eigenvalue `etilde7TubeLam F`; see `etilde7TubeLam_distinct` and
`progress/etilde7-tube-design.md` §7.2). The proof is a single `sorry`,
deferred to the sub-C assembly (#4570) modelled on
`starTubeRepGen_isIndecomposable`: the arm-2 prefix flag and arm-3 suffix
flag collapse every vertex onto a common `F^{m+1}`, where arm 1 deposits
the `(λ•id + J)`-invariant complementary pair killed by
`eigenvalue_jordan_invariant_compl_trivial_gen`.

The `1 ≤ m` hypothesis is retained: for `m = 0` the Jordan block is a
scalar and there is no eigenvalue-site nilpotent to drive the splitting
(the `m = 0` regular simple `S_λ` is itself the dimension-`δ` brick, but
the infinite-type argument ranges over `m + 1 ≥ 1`). -/
theorem etilde7Rep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ) (hm : 1 ≤ m) :
    (etilde7Rep_kQ F Q hOrient m).IsIndecomposable := by
  let _ := hm  -- retain `hm` in the signature for the sub-C proof
  sorry

/-! ## Section 5: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `etilde7_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `etilde7Adj`,
the set of dimension vectors of indecomposable representations is
infinite.

Mirrors the proof of `etilde7_not_finite_type`
(`InfiniteTypeConstructions.lean:3608`): we range over `m + 1` (not `m`)
because `etilde7Rep_kQ_isIndecomposable` requires `1 ≤ m` (the `m = 0`
case is provably decomposable). Injectivity comes from vertex `4`, where
`etilde7Dim m 4 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`etilde7Rep_kQ_isIndecomposable`, which inherits the wave-54 framework
wall — see its docstring. -/
theorem etilde7_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj) :
    ¬ Set.Finite
      {d : Fin 8 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 8) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, (fun v : Fin 8 => etilde7Dim (m + 1) v) ∈
      {d : Fin 8 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 8) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨etilde7Rep_kQ F Q hOrient (m + 1),
      etilde7Rep_kQ_isIndecomposable F Q hOrient (m + 1) (Nat.succ_le_succ m.zero_le),
      etilde7Rep_kQ_dimVec F Q hOrient (m + 1)⟩
  have hinj : Function.Injective (fun m : ℕ => fun v : Fin 8 => etilde7Dim (m + 1) v) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨4, by omega⟩
    simp only [etilde7Dim] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

set_option maxHeartbeats 3200000 in
-- reason: matches the `set_option maxHeartbeats` budget on
-- `embed_t125_in_tree_per_kQ` (`FieldGenericT125.lean:55`), which the
-- proof body mirrors — the ~30 distinctness facts and the 64-case
-- `fin_cases` adjacency check through the `Fin 8 ↪ Fin n` embedding
-- need the larger budget.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) Ẽ₇ = T(1, 3, 3) embedding helper: given
eight vertices forming a `T(1, 3, 3)` shape inside an acyclic simple
graph, embed and dispatch to `etilde7_not_finite_type_per_kQ` via
`subgraph_infinite_type_transfer_per_kQ`.

Mirrors the pattern of `embed_t125_in_tree_per_kQ`
(`FieldGenericT125.lean:71`). Vertex roles match `etilde7Adj`: `v₀`
(center, vertex `0`); `u₁` (length-1 arm, vertex `1`); `(c₂, d₂, e₂)`
(length-3 arm, vertices `2`-`3`-`4`); `(c₃, d₃, e₃)` (length-3 arm,
vertices `5`-`6`-`7`). Embedding map:
`0→v₀, 1→u₁, 2→c₂, 3→d₂, 4→e₂, 5→c₃, 6→d₃, 7→e₃`.

Shared helper introduced for the non-adjacent-branches leaf case
(issue #2932). Body filled in #2938 following the
`embed_t125_in_tree_per_kQ` pattern: build the distinctness lattice
via `acyclic_no_triangle` (seven triangle non-edges) and
`acyclic_path_nonadj` (six distance-3, five distance-4, two
distance-5, and one distance-6 non-edges), define a
`Fin 8 ↪ Fin n` embedding, verify `etilde7Adj i j = adj (φ i) (φ j)`
by 64-case split, then dispatch via
`subgraph_infinite_type_transfer_per_kQ`. -/
theorem embed_etilde7_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ u₁ c₂ d₂ e₂ c₃ d₃ e₃ : Fin n)
    (hu₁ : adj v₀ u₁ = 1)
    (hc₂ : adj v₀ c₂ = 1) (hd₂ : adj c₂ d₂ = 1) (he₂ : adj d₂ e₂ = 1)
    (hc₃ : adj v₀ c₃ = 1) (hd₃ : adj c₃ d₃ = 1) (he₃ : adj d₃ e₃ = 1)
    (hu₁_ne_c₂ : u₁ ≠ c₂) (hu₁_ne_c₃ : u₁ ≠ c₃) (hc₂_ne_c₃ : c₂ ≠ c₃)
    (hd₂_ne_v₀ : d₂ ≠ v₀) (hd₃_ne_v₀ : d₃ ≠ v₀)
    (he₂_ne_c₂ : e₂ ≠ c₂) (he₃_ne_c₃ : e₃ ≠ c₃)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  -- Same-arm distinctness (from adjacency)
  have hv₀_ne_u₁ := ne_of_adj' v₀ u₁ hu₁
  have hv₀_ne_c₂ := ne_of_adj' v₀ c₂ hc₂
  have hv₀_ne_c₃ := ne_of_adj' v₀ c₃ hc₃
  have hc₂_ne_d₂ := ne_of_adj' c₂ d₂ hd₂
  have hc₃_ne_d₃ := ne_of_adj' c₃ d₃ hd₃
  have hd₂_ne_e₂ := ne_of_adj' d₂ e₂ he₂
  have hd₃_ne_e₃ := ne_of_adj' d₃ e₃ he₃
  -- Reversed edges
  have hu₁_v₀ : adj u₁ v₀ = 1 := (adj_comm u₁ v₀).trans hu₁
  have hc₂_v₀ : adj c₂ v₀ = 1 := (adj_comm c₂ v₀).trans hc₂
  have hc₃_v₀ : adj c₃ v₀ = 1 := (adj_comm c₃ v₀).trans hc₃
  have hd₂_c₂ : adj d₂ c₂ = 1 := (adj_comm d₂ c₂).trans hd₂
  have hd₃_c₃ : adj d₃ c₃ = 1 := (adj_comm d₃ c₃).trans hd₃
  have he₂_d₂ : adj e₂ d₂ = 1 := (adj_comm e₂ d₂).trans he₂
  have he₃_d₃ : adj e₃ d₃ = 1 := (adj_comm e₃ d₃).trans he₃
  -- Triangle non-edges (acyclic_no_triangle)
  -- u₁-cᵢ via apex v₀; cᵢ-cⱼ via apex v₀
  have hu₁c₂ : adj u₁ c₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ c₂
      hu₁_ne_c₂ hv₀_ne_u₁.symm hv₀_ne_c₂.symm hu₁ hc₂
  have hu₁c₃ : adj u₁ c₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ c₃
      hu₁_ne_c₃ hv₀_ne_u₁.symm hv₀_ne_c₃.symm hu₁ hc₃
  have hc₂c₃ : adj c₂ c₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ c₂ c₃
      hc₂_ne_c₃ hv₀_ne_c₂.symm hv₀_ne_c₃.symm hc₂ hc₃
  -- v₀-dᵢ via apex cᵢ
  have hv₀d₂ : adj v₀ d₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic c₂ v₀ d₂
      hd₂_ne_v₀.symm hv₀_ne_c₂ hc₂_ne_d₂.symm hc₂_v₀ hd₂
  have hv₀d₃ : adj v₀ d₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic c₃ v₀ d₃
      hd₃_ne_v₀.symm hv₀_ne_c₃ hc₃_ne_d₃.symm hc₃_v₀ hd₃
  -- cᵢ-eᵢ via apex dᵢ
  have hc₂e₂ : adj c₂ e₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic d₂ c₂ e₂
      he₂_ne_c₂.symm hc₂_ne_d₂ hd₂_ne_e₂.symm hd₂_c₂ he₂
  have hc₃e₃ : adj c₃ e₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic d₃ c₃ e₃
      he₃_ne_c₃.symm hc₃_ne_d₃ hd₃_ne_e₃.symm hd₃_c₃ he₃
  -- Cross-arm ne (level 1): from triangle non-edges
  have hu₁_ne_d₂ : u₁ ≠ d₂ := by intro h; rw [h] at hu₁; linarith [hv₀d₂]
  have hu₁_ne_d₃ : u₁ ≠ d₃ := by intro h; rw [h] at hu₁; linarith [hv₀d₃]
  have hc₂_ne_d₃ : c₂ ≠ d₃ := by intro h; rw [h] at hc₂; linarith [hv₀d₃]
  have hc₃_ne_d₂ : c₃ ≠ d₂ := by intro h; rw [h] at hc₃; linarith [hv₀d₂]
  have hv₀_ne_e₂ : v₀ ≠ e₂ := by
    intro h; rw [← h] at he₂; linarith [adj_comm d₂ v₀, hv₀d₂]
  have hv₀_ne_e₃ : v₀ ≠ e₃ := by
    intro h; rw [← h] at he₃; linarith [adj_comm d₃ v₀, hv₀d₃]
  -- Path nodup helpers
  have path_nodup4 : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
    intro a b c d hab hac had hbc hbd hcd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  have path_nodup5 : ∀ (a b c d e : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e →
      b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      [a, b, c, d, e].Nodup := by
    intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
  have path_nodup6 : ∀ (a b c d e f : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f →
      c ≠ d → c ≠ e → c ≠ f → d ≠ e → d ≠ f → e ≠ f →
      [a, b, c, d, e, f].Nodup := by
    intro a b c d e f hab hac had hae haf hbc hbd hbe hbf
      hcd hce hcf hde hdf hef
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩,
      ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩
  have path_nodup7 : ∀ (a b c d e f g : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f → a ≠ g →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f → b ≠ g →
      c ≠ d → c ≠ e → c ≠ f → c ≠ g →
      d ≠ e → d ≠ f → d ≠ g → e ≠ f → e ≠ g → f ≠ g →
      [a, b, c, d, e, f, g].Nodup := by
    intro a b c d e f g hab hac had hae haf hag hbc hbd hbe hbf hbg
      hcd hce hcf hcg hde hdf hdg hef heg hfg
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf, hag⟩, ⟨hbc, hbd, hbe, hbf, hbg⟩,
      ⟨hcd, hce, hcf, hcg⟩, ⟨hde, hdf, hdg⟩, ⟨hef, heg⟩, hfg⟩
  -- Path edges helpers
  have path_edges4 : ∀ (a b c d : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d].length) →
        adj ([a, b, c, d].get ⟨k, by omega⟩)
          ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d h₁ h₂ h₃ k hk
    have : k + 1 < 4 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  have path_edges5 : ∀ (a b c d e : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e].length) →
        adj ([a, b, c, d, e].get ⟨k, by omega⟩)
          ([a, b, c, d, e].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e h₁ h₂ h₃ h₄ k hk
    have : k + 1 < 5 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> assumption
  have path_edges6 : ∀ (a b c d e f : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      adj d e = 1 → adj e f = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f].length) →
        adj ([a, b, c, d, e, f].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f h₁ h₂ h₃ h₄ h₅ k hk
    have : k + 1 < 6 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption
  have path_edges7 : ∀ (a b c d e f g : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      adj e f = 1 → adj f g = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f, g].length) →
        adj ([a, b, c, d, e, f, g].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f, g].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f g h₁ h₂ h₃ h₄ h₅ h₆ k hk
    have : k + 1 < 7 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- Distance-3 non-edges (4-vertex paths)
  have hu₁d₂ : adj u₁ d₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₂, c₂, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hc₂_ne_d₂.symm hd₂_ne_v₀ hu₁_ne_d₂.symm
        hv₀_ne_c₂.symm hu₁_ne_c₂.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hd₂_c₂ hc₂_v₀ hu₁)
  have hu₁d₃ : adj u₁ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hu₁_ne_d₃.symm
        hv₀_ne_c₃.symm hu₁_ne_c₃.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hd₃_c₃ hc₃_v₀ hu₁)
  have hd₂c₃ : adj d₂ c₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [c₃, v₀, c₂, d₂] (by simp)
      (path_nodup4 _ _ _ _ hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hc₂_ne_d₂)
      (path_edges4 _ _ _ _ hc₃_v₀ hc₂ hd₂)
  have hc₂d₃ : adj c₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂] (by simp)
      (path_nodup4 _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hv₀_ne_c₂)
      (path_edges4 _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂)
  have hv₀e₂ : adj v₀ e₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₂, d₂, c₂, v₀] (by simp)
      (path_nodup4 _ _ _ _ hd₂_ne_e₂.symm he₂_ne_c₂ hv₀_ne_e₂.symm
        hc₂_ne_d₂.symm hd₂_ne_v₀ hv₀_ne_c₂.symm)
      (path_edges4 _ _ _ _ he₂_d₂ hd₂_c₂ hc₂_v₀)
  have hv₀e₃ : adj v₀ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀] (by simp)
      (path_nodup4 _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hv₀_ne_c₃.symm)
      (path_edges4 _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀)
  -- Cross-arm ne (level 2): from distance-3 non-edges
  have hu₁_ne_e₂ : u₁ ≠ e₂ := by intro h; rw [h] at hu₁; linarith [hv₀e₂]
  have hu₁_ne_e₃ : u₁ ≠ e₃ := by intro h; rw [h] at hu₁; linarith [hv₀e₃]
  have hc₂_ne_e₃ : c₂ ≠ e₃ := by intro h; rw [h] at hc₂; linarith [hv₀e₃]
  have hc₃_ne_e₂ : c₃ ≠ e₂ := by intro h; rw [h] at hc₃; linarith [hv₀e₂]
  have hd₂_ne_d₃ : d₂ ≠ d₃ := by intro h; rw [h] at hd₂; linarith [hc₂d₃]
  -- Distance-4 non-edges (5-vertex paths)
  have hu₁e₂ : adj u₁ e₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₂, d₂, c₂, v₀, u₁] (by simp)
      (path_nodup5 _ _ _ _ _ hd₂_ne_e₂.symm he₂_ne_c₂ hv₀_ne_e₂.symm hu₁_ne_e₂.symm
        hc₂_ne_d₂.symm hd₂_ne_v₀ hu₁_ne_d₂.symm hv₀_ne_c₂.symm hu₁_ne_c₂.symm hv₀_ne_u₁)
      (path_edges5 _ _ _ _ _ he₂_d₂ hd₂_c₂ hc₂_v₀ hu₁)
  have hu₁e₃ : adj u₁ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, u₁] (by simp)
      (path_nodup5 _ _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hu₁_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hu₁_ne_d₃.symm hv₀_ne_c₃.symm hu₁_ne_c₃.symm hv₀_ne_u₁)
      (path_edges5 _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hu₁)
  have hd₂d₃ : adj d₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂, d₂] (by simp)
      (path_nodup5 _ _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hv₀_ne_c₂ hd₂_ne_v₀.symm hc₂_ne_d₂)
      (path_edges5 _ _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂ hd₂)
  have hc₂e₃ : adj c₂ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, c₂] (by simp)
      (path_nodup5 _ _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hc₂_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hv₀_ne_c₃.symm hc₂_ne_c₃.symm hv₀_ne_c₂)
      (path_edges5 _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hc₂)
  have he₂c₃ : adj e₂ c₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [c₃, v₀, c₂, d₂, e₂] (by simp)
      (path_nodup5 _ _ _ _ _ hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hc₃_ne_e₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hv₀_ne_e₂ hc₂_ne_d₂ he₂_ne_c₂.symm hd₂_ne_e₂)
      (path_edges5 _ _ _ _ _ hc₃_v₀ hc₂ hd₂ he₂)
  -- Cross-arm ne (level 3): from distance-4 non-edges
  have hd₂_ne_e₃ : d₂ ≠ e₃ := by intro h; rw [h] at hd₂; linarith [hc₂e₃]
  have hd₃_ne_e₂ : d₃ ≠ e₂ := by
    intro h; rw [← h] at he₂; linarith [adj_comm d₂ d₃, hd₂d₃]
  -- Distance-5 non-edges (6-vertex paths)
  have hd₂e₃ : adj d₂ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, c₂, d₂] (by simp)
      (path_nodup6 _ _ _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hc₂_ne_e₃.symm hd₂_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hv₀_ne_c₂ hd₂_ne_v₀.symm hc₂_ne_d₂)
      (path_edges6 _ _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hc₂ hd₂)
  have he₂d₃ : adj e₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂, d₂, e₂] (by simp)
      (path_nodup6 _ _ _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm hd₃_ne_e₂
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hc₃_ne_e₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hv₀_ne_e₂ hc₂_ne_d₂ he₂_ne_c₂.symm hd₂_ne_e₂)
      (path_edges6 _ _ _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂ hd₂ he₂)
  -- Cross-arm ne (level 4): from distance-5 non-edge
  have he₂_ne_e₃ : e₂ ≠ e₃ := by intro h; rw [h] at he₂; linarith [hd₂e₃]
  -- Distance-6 non-edge (7-vertex path)
  have he₂e₃ : adj e₂ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, c₂, d₂, e₂] (by simp)
      (path_nodup7 _ _ _ _ _ _ _
        hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hc₂_ne_e₃.symm hd₂_ne_e₃.symm he₂_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm hd₃_ne_e₂
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hc₃_ne_e₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hv₀_ne_e₂ hc₂_ne_d₂ he₂_ne_c₂.symm hd₂_ne_e₂)
      (path_edges7 _ _ _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hc₂ hd₂ he₂)
  -- Construct the embedding φ : Fin 8 ↪ Fin n for T(1, 3, 3)
  -- Map: 0→v₀, 1→u₁, 2→c₂, 3→d₂, 4→e₂, 5→c₃, 6→d₃, 7→e₃
  let φ_fun : Fin 8 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => u₁  | ⟨2, _⟩ => c₂
    | ⟨3, _⟩ => d₂  | ⟨4, _⟩ => e₂  | ⟨5, _⟩ => c₃
    | ⟨6, _⟩ => d₃  | ⟨7, _⟩ => e₃
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 8 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, etilde7Adj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [etilde7Adj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag v₀, hdiag u₁, hdiag c₂, hdiag d₂, hdiag e₂,
        hdiag c₃, hdiag d₃, hdiag e₃,
        hu₁, hc₂, hd₂, he₂, hc₃, hd₃, he₃,
        adj_comm v₀ u₁, adj_comm v₀ c₂, adj_comm v₀ d₂, adj_comm v₀ e₂,
        adj_comm v₀ c₃, adj_comm v₀ d₃, adj_comm v₀ e₃,
        adj_comm u₁ c₂, adj_comm u₁ d₂, adj_comm u₁ e₂,
        adj_comm u₁ c₃, adj_comm u₁ d₃, adj_comm u₁ e₃,
        adj_comm c₂ d₂, adj_comm c₂ e₂, adj_comm c₂ c₃,
        adj_comm c₂ d₃, adj_comm c₂ e₃,
        adj_comm d₂ e₂, adj_comm d₂ c₃, adj_comm d₂ d₃, adj_comm d₂ e₃,
        adj_comm e₂ c₃, adj_comm e₂ d₃, adj_comm e₂ e₃,
        adj_comm c₃ d₃, adj_comm c₃ e₃,
        adj_comm d₃ e₃,
        hu₁c₂, hu₁c₃, hc₂c₃, hv₀d₂, hv₀d₃, hc₂e₂, hc₃e₃,
        hu₁d₂, hu₁d₃, hd₂c₃, hc₂d₃, hv₀e₂, hv₀e₃,
        hu₁e₂, hu₁e₃, hd₂d₃, hc₂e₃, he₂c₃,
        hd₂e₃, he₂d₃,
        he₂e₃]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (etilde7_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
