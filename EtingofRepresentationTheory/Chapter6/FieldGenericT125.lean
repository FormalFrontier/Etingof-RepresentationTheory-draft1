import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericETilde7

/-!
# Orientation-Generic T(1, 2, 5) = Ẽ₈ Construction (#4559)

F-generic, orientation-generic homogeneous-tube representation of the
affine `E₈` Dynkin diagram `T(1, 2, 5)`. This file provides `t125Rep_kQ`,
its dimension-vector lemma, an indecomposability stub (a single `sorry`,
of a now-*true* statement), and the per-(F, Q) infinite-type theorem
`t125_not_finite_type_per_kQ`, plus the tree-embedding helper
`embed_t125_in_tree_per_kQ` (consumed by `FieldGenericTpqr` /
`FieldGenericNonAdjacentBranches`).

T(1, 2, 5) is the affine `E₈` Dynkin diagram: 9 vertices forming three
arms meeting at the center (vertex 0).

- Arm 1 (length 1): `0 — 1`
- Arm 2 (length 2): `0 — 2 — 3`
- Arm 3 (length 5): `0 — 4 — 5 — 6 — 7 — 8`

The null root is `δ = (6, 3, 4, 2, 5, 4, 3, 2, 1)` (`t125Dim`,
`InfiniteTypeConstructions.lean:3484`): center dim `6(m+1)`, and the three
arm flags entering it.

**Homogeneous-tube construction (#4559, mirrors #4568 for Ẽ₇).** The naive
"mirror etilde6" single-nilpotent-twist family is decomposable for every
`m ≥ 1` (audit #4542). `t125Rep_kQ` is instead the genuine homogeneous
tube `R_λ^{(m+1)}` of the regular simple `S_λ` at `δ`: arm 2 is the
coordinate *prefix* flag, arm 3 the opposite *suffix* flag, and arm 1 the
eigenvalue 3-plane carrying `Λ = λ·id + J`. The eigenvalue is
`t125TubeLam F`, a generic element of the infinite field `F` with
`1, λ, …, λ⁵` pairwise distinct (the brick / homogeneity condition;
see `t125TubeLam_distinct`).

`t125Rep_kQ_isIndecomposable` is a single `sorry`, but now of a **true**
statement (the soundness win): the assembly is deferred to a sub-C
follow-up, modelled on `starTubeRepGen_isIndecomposable`
(`FieldGenericTube.lean`). The earlier bare `sorry` on the existential
`t125_not_finite_type_per_kQ` is replaced by an explicit indecomposable
witness plus this isolated, true sub-lemma.

See `FieldGenericInfiniteType.lean` for the naming conventions
(`_F` / `_gen`, `_kQ`, `_per_kQ`).
-/

open scoped Matrix

namespace Etingof

/-! ## Section 0.5: Generic eigenvalue for the homogeneous tube

The homogeneous tube `R_λ^{(m+1)}` is a brick only at the *homogeneous*
points of `P¹`, i.e. for `λ` with `1, λ, …, λ⁵` pairwise distinct (the
moment-curve / Vandermonde condition the brick proof for `δ` needs — the
center is `F⁶` and the eigenvalue 3-plane `⟨u, v, w⟩` with `u_i = 1`,
`v_i = λ^i`, `w_i = λ^{2i}` forces any flag-and-`P`-preserving diagonal to
be scalar via a cubic vanishing at six distinct points). Such `λ` exist in
any infinite field — in particular any algebraically closed `F` — because
the bad set is the finite root set of `∏_{i<j}(X^j − X^i)`. -/

/-- In an algebraically closed (hence infinite) field, there is `λ` whose
first `n` powers `λ^0, …, λ^{n-1}` are pairwise distinct: the bad set is
the finite root set of `∏_{i<j<n}(X^j − X^i)`. Generalizes
`exists_lam_distinct_powers` (which is the `n = 4` case for Ẽ₇). -/
theorem exists_lam_distinct_powers_gen (F : Type) [Field F] [IsAlgClosed F]
    (n : ℕ) :
    ∃ lam : F, ∀ i j : Fin n, i ≠ j → lam ^ (i : ℕ) ≠ lam ^ (j : ℕ) := by
  classical
  set X := (Polynomial.X : Polynomial F) with hX
  set s : Finset (ℕ × ℕ) :=
    (Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 < p.2) with hs
  set f : Polynomial F := ∏ p ∈ s, (X ^ p.2 - X ^ p.1) with hf_def
  have hfac : ∀ p ∈ s, (X ^ p.2 - X ^ p.1 : Polynomial F) ≠ 0 := by
    intro p hp hzero
    simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have hpow : (X ^ p.2 : Polynomial F) = X ^ p.1 := sub_eq_zero.mp hzero
    have hdeg := congrArg Polynomial.natDegree hpow
    rw [hX, Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hdeg
    omega
  have hf : f ≠ 0 := by rw [hf_def]; exact Finset.prod_ne_zero_iff.mpr hfac
  have hcard : (f.natDegree : Cardinal) < Cardinal.mk F :=
    lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.infinite_iff.mp inferInstance)
  obtain ⟨lam, hlam⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f hf hcard
  rw [hf_def, Polynomial.eval_prod, Finset.prod_ne_zero_iff] at hlam
  have key : ∀ a b : ℕ, a < b → b < n → lam ^ a ≠ lam ^ b := by
    intro a b hab hb
    have hmem : (a, b) ∈ s := by
      simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, hb⟩, hab⟩
    have hne := hlam (a, b) hmem
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, hX, Polynomial.eval_X] at hne
    exact fun hpow => (sub_ne_zero.mp hne) hpow.symm
  refine ⟨lam, fun i j hij => ?_⟩
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · exact key i j h j.isLt
  · exact absurd (Fin.ext h) hij
  · exact fun hpow => key j i h i.isLt hpow.symm

/-- A generic eigenvalue for the T(1, 2, 5) = Ẽ₈ homogeneous tube: an
element of the infinite field `F` with `1, λ, …, λ⁵` pairwise distinct. -/
noncomputable def t125TubeLam (F : Type) [Field F] [IsAlgClosed F] : F :=
  Classical.choose (exists_lam_distinct_powers_gen F 6)

/-- The defining property of `t125TubeLam`: its first six powers are
pairwise distinct (the brick / homogeneity hypothesis used by the
indecomposability assembly, sub-C). -/
theorem t125TubeLam_distinct (F : Type) [Field F] [IsAlgClosed F] :
    ∀ i j : Fin 6, i ≠ j →
      t125TubeLam F ^ (i : ℕ) ≠ t125TubeLam F ^ (j : ℕ) :=
  Classical.choose_spec (exists_lam_distinct_powers_gen F 6)

/-! ## Section 1: F-generic forward maps for the Ẽ₈ homogeneous tube

Arm 2 (length 2) enters the center `F^{6(m+1)}` as a coordinate **prefix**
flag (`prefixBlockEmbed_F`), arm 3 (length 5) as the opposite coordinate
**suffix** flag (`suffixBlockEmbed_F`, from `FieldGenericETilde7`), and arm
1 (length 1) as the eigenvalue 3-plane carrying `Λ = λ·id + J`
(`t125Arm1Tube_F`). The center is six `(m+1)`-blocks. -/

/-- General single-block placement `F^{m+1} → F^N` at offset `o`:
`x ↦ (…, 0, x, 0, …)` with `x` occupying coordinates `[o, o + (m+1))`.
Target dimension `N` is an arbitrary `ℕ` (the Ẽ₈ center needs the
`N = 6(m+1)` instances). Generalizes `blockEmbedAt_F`
(`FieldGenericETilde7`, fixed `N = 4(m+1)`). -/
noncomputable def blockEmbedAtN_F (F : Type) [Field F] (o N m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin N → F) where
  toFun x i := if h : o ≤ i.val ∧ i.val < o + (m + 1) then x ⟨i.val - o, by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- General single-block projection `F^N → F^{m+1}` reading the block at
offset `o`: `w ↦ (w_o, …, w_{o+m})`. Requires `o + (m+1) ≤ N` so the
index stays in range. Reverse / extraction counterpart of
`blockEmbedAtN_F`; used to read the three input blocks `(P, Q, R)` of the
arm-1 eigenvalue tube. -/
noncomputable def blockProjAtN_F (F : Type) [Field F] (o N m : ℕ)
    (h : o + (m + 1) ≤ N) :
    (Fin N → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨o + i.val, by have := i.isLt; omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Ẽ₈ arm-1 eigenvalue tube embedding `F^{3(m+1)} → F^{6(m+1)}`. With
`Λ = λ·id + J` (`jordanShiftLinGen`) and input blocks `(P, Q, R)`, block
`k` (for `k = 0, …, 5`) of the center is `P + Λ^k Q + Λ^{2k} R`. The single
λ-bearing map of the tube: the regular simple's eigenvalue 3-plane
`⟨(1)_i, (λ^i)_i, (λ^{2i})_i⟩ ⊆ F⁶` (a moment-curve / rational-normal
configuration), Jordan-thickened at the eigenvalue site. Full column rank
for the generic `λ`; couples all six center blocks through the eigenvalue
site (defeating the single-twist peeling). -/
noncomputable def t125Arm1Tube_F (F : Type) [Field F] (lam : F) (m : ℕ) :
    (Fin (3 * (m + 1)) → F) →ₗ[F] (Fin (6 * (m + 1)) → F) :=
  let Λ := jordanShiftLinGen F lam m
  let Λ2 := Λ.comp Λ
  let Λ3 := Λ.comp Λ2
  let Λ4 := Λ2.comp Λ2
  let Λ5 := Λ.comp Λ4
  let Λ6 := Λ2.comp Λ4
  let Λ8 := Λ4.comp Λ4
  let Λ10 := Λ4.comp Λ6
  let P := blockProjAtN_F F 0 (3 * (m + 1)) m (by omega)
  let Q := blockProjAtN_F F (m + 1) (3 * (m + 1)) m (by omega)
  let R := blockProjAtN_F F (2 * (m + 1)) (3 * (m + 1)) m (by omega)
  (blockEmbedAtN_F F 0 (6 * (m + 1)) m).comp (P + Q + R)
    + (blockEmbedAtN_F F (m + 1) (6 * (m + 1)) m).comp (P + Λ.comp Q + Λ2.comp R)
    + (blockEmbedAtN_F F (2 * (m + 1)) (6 * (m + 1)) m).comp (P + Λ2.comp Q + Λ4.comp R)
    + (blockEmbedAtN_F F (3 * (m + 1)) (6 * (m + 1)) m).comp (P + Λ3.comp Q + Λ6.comp R)
    + (blockEmbedAtN_F F (4 * (m + 1)) (6 * (m + 1)) m).comp (P + Λ4.comp Q + Λ8.comp R)
    + (blockEmbedAtN_F F (5 * (m + 1)) (6 * (m + 1)) m).comp (P + Λ5.comp Q + Λ10.comp R)

/-! ## Section 2: Flag retractions (sub-B1 of #4612)

The prefix/suffix flag projections are left inverses of the corresponding
embeddings, and the single-block projection reads back the block placed by
`blockEmbedAtN_F`. These map-level retractions are the foundational step of
the flag-collapse argument that drives `t125Rep_kQ_leaf_equalities`: they let
the indecomposability proof extract a leaf component from a center membership,
and they hold in every orientation. Mirrors `center_decomp_F` /
`embed_sum_zero_F` (`FieldGenericStar.lean`) for the two-leaf star. -/

/-- `prefixBlockProj_F` is a left inverse of `prefixBlockEmbed_F`: the
prefix-flag embedding `F^{a(m+1)} → F^{b(m+1)}` (`x ↦ (x, 0, …, 0)`) is read
back exactly by the first-`a`-blocks projection. -/
theorem prefixBlockProj_comp_embed_F (F : Type) [Field F] (a b m : ℕ) (hab : a ≤ b)
    (x : Fin (a * (m + 1)) → F) :
    prefixBlockProj_F F a b m hab (prefixBlockEmbed_F F a b m x) = x := by
  ext i
  simp only [prefixBlockProj_F, prefixBlockEmbed_F, LinearMap.coe_mk, AddHom.coe_mk,
    dif_pos i.isLt]

/-- `suffixBlockProj_F` is a left inverse of `suffixBlockEmbed_F`: the
suffix-flag embedding `F^{a(m+1)} → F^{b(m+1)}` (`x ↦ (0, …, 0, x)`) is read
back exactly by the last-`a`-blocks projection. -/
theorem suffixBlockProj_comp_embed_F (F : Type) [Field F] (a b m : ℕ) (hab : a ≤ b)
    (x : Fin (a * (m + 1)) → F) :
    suffixBlockProj_F F a b m hab (suffixBlockEmbed_F F a b m x) = x := by
  ext i
  have hi := i.isLt
  simp only [suffixBlockProj_F, suffixBlockEmbed_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  simp

/-- `blockProjAtN_F` reads back the single block placed by `blockEmbedAtN_F` at
the same offset `o`. The retraction for the eigenvalue-tube input blocks
`(P, Q, R)`. -/
theorem blockProjAtN_comp_embed_F (F : Type) [Field F] (o N m : ℕ)
    (h : o + (m + 1) ≤ N) (x : Fin (m + 1) → F) :
    blockProjAtN_F F o N m h (blockEmbedAtN_F F o N m x) = x := by
  ext i
  have hi := i.isLt
  simp only [blockProjAtN_F, blockEmbedAtN_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  simp

/-- `prefixBlockEmbed_F` is injective (left inverse `prefixBlockProj_F`). -/
theorem prefixBlockEmbed_injective_F (F : Type) [Field F] (a b m : ℕ) (hab : a ≤ b) :
    Function.Injective (prefixBlockEmbed_F F a b m) :=
  Function.LeftInverse.injective (prefixBlockProj_comp_embed_F F a b m hab)

/-- `suffixBlockEmbed_F` is injective (left inverse `suffixBlockProj_F`). -/
theorem suffixBlockEmbed_injective_F (F : Type) [Field F] (a b m : ℕ) (hab : a ≤ b) :
    Function.Injective (suffixBlockEmbed_F F a b m) :=
  Function.LeftInverse.injective (suffixBlockProj_comp_embed_F F a b m hab)

/-- Prefix-flag composition law: embedding into the first `a` blocks of `b`
then into the first `b` blocks of `c` equals embedding into the first `a`
blocks of `c`. The prefix flag `F^{a(m+1)} ↪ F^{b(m+1)} ↪ F^{c(m+1)}` is a
single prefix embedding. -/
theorem prefixBlockEmbed_comp_F (F : Type) [Field F] (a b c m : ℕ) (hab : a ≤ b)
    (x : Fin (a * (m + 1)) → F) :
    prefixBlockEmbed_F F b c m (prefixBlockEmbed_F F a b m x) =
      prefixBlockEmbed_F F a c m x := by
  ext j
  simp only [prefixBlockEmbed_F, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hjb : j.val < b * (m + 1)
  · rw [dif_pos hjb]
  · rw [dif_neg hjb,
      dif_neg (fun hja => hjb (Nat.lt_of_lt_of_le hja (Nat.mul_le_mul_right _ hab)))]

/-- Suffix-flag composition law: embedding into the last `a` blocks of `b`
then into the last `b` blocks of `c` equals embedding into the last `a`
blocks of `c`. The suffix flag `F^{a(m+1)} ↪ F^{b(m+1)} ↪ F^{c(m+1)}` is a
single suffix embedding (the arm-3 flag of T(1,2,5)). -/
theorem suffixBlockEmbed_comp_F (F : Type) [Field F] (a b c m : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (x : Fin (a * (m + 1)) → F) :
    suffixBlockEmbed_F F b c m (suffixBlockEmbed_F F a b m x) =
      suffixBlockEmbed_F F a c m x := by
  ext j
  have hj := j.isLt
  have e1 : (c - b) * (m + 1) + (b - a) * (m + 1) = (c - a) * (m + 1) := by
    rw [← Nat.add_mul]; congr 1; omega
  have e2 : (c - b) * (m + 1) + b * (m + 1) = c * (m + 1) := by
    rw [← Nat.add_mul]; congr 1; omega
  have e3 : (b - a) * (m + 1) + a * (m + 1) = b * (m + 1) := by
    rw [← Nat.add_mul]; congr 1; omega
  simp only [suffixBlockEmbed_F, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hR : (c - a) * (m + 1) ≤ j.val ∧ j.val - (c - a) * (m + 1) < a * (m + 1)
  · rw [dif_pos hR, dif_pos (show (c - b) * (m + 1) ≤ j.val ∧
        j.val - (c - b) * (m + 1) < b * (m + 1) from ⟨by omega, by omega⟩),
      dif_pos (show (b - a) * (m + 1) ≤ j.val - (c - b) * (m + 1) ∧
        j.val - (c - b) * (m + 1) - (b - a) * (m + 1) < a * (m + 1) from
        ⟨by omega, by omega⟩)]
    congr 1
    ext
    simp only
    omega
  · rw [dif_neg hR]
    by_cases hO : (c - b) * (m + 1) ≤ j.val ∧ j.val - (c - b) * (m + 1) < b * (m + 1)
    · rw [dif_pos hO, dif_neg (show ¬ ((b - a) * (m + 1) ≤ j.val - (c - b) * (m + 1) ∧
        j.val - (c - b) * (m + 1) - (b - a) * (m + 1) < a * (m + 1)) from
        fun h => hR ⟨by omega, by omega⟩)]
    · rw [dif_neg hO]

/-! ## Section 3: Orientation-generic Ẽ₈ homogeneous-tube representation

The map function is a match on `(a.val, b.val)` over the eight canonical
edges (arrow toward the center) plus their eight reverses. Arm 1 is the
eigenvalue tube; arm 2 the prefix flag; arm 3 the suffix flag. Outside
those 16 edge pairs the map is `0` (these arrows do not exist in any
orientation of `t125Adj`). -/

/-- Direction-aware match-based map function for the orientation-generic
Ẽ₈ homogeneous-tube representation at eigenvalue `lam`. Vertices:
`0` center (`6(m+1)`); `1` arm-1 leaf (`3(m+1)`); `2`-`3` arm-2 prefix flag
(`4(m+1)`, `2(m+1)`); `4`-`8` arm-3 suffix flag
(`5(m+1)`, `4(m+1)`, `3(m+1)`, `2(m+1)`, `m+1`). -/
private noncomputable def t125RepMap_kQ (F : Type) [Field F] (lam : F)
    (m : ℕ) (a b : Fin 9) :
    (Fin (t125Dim m a) → F) →ₗ[F] (Fin (t125Dim m b) → F) :=
  match a, b with
  -- Arm 1 (eigenvalue 3-plane): edge {0, 1}
  | ⟨1, _⟩, ⟨0, _⟩ => t125Arm1Tube_F F lam m
  | ⟨0, _⟩, ⟨1, _⟩ => prefixBlockProj_F F 3 6 m (by omega)
  -- Arm 2 (prefix flag): edge {2, 3}
  | ⟨3, _⟩, ⟨2, _⟩ => prefixBlockEmbed_F F 2 4 m
  | ⟨2, _⟩, ⟨3, _⟩ => prefixBlockProj_F F 2 4 m (by omega)
  -- Arm 2 (prefix flag): edge {0, 2}
  | ⟨2, _⟩, ⟨0, _⟩ => prefixBlockEmbed_F F 4 6 m
  | ⟨0, _⟩, ⟨2, _⟩ => prefixBlockProj_F F 4 6 m (by omega)
  -- Arm 3 (suffix flag): edge {7, 8}. The leaf `v8` has dim `m+1` (not
  -- `1·(m+1)`), so use `starEmbed2_F` / `starSecond_F` — the suffix
  -- embed/proj of a single block into two, with the right `m+1` shape.
  | ⟨8, _⟩, ⟨7, _⟩ => starEmbed2_F F m
  | ⟨7, _⟩, ⟨8, _⟩ => starSecond_F F m
  -- Arm 3 (suffix flag): edge {6, 7}
  | ⟨7, _⟩, ⟨6, _⟩ => suffixBlockEmbed_F F 2 3 m
  | ⟨6, _⟩, ⟨7, _⟩ => suffixBlockProj_F F 2 3 m (by omega)
  -- Arm 3 (suffix flag): edge {5, 6}
  | ⟨6, _⟩, ⟨5, _⟩ => suffixBlockEmbed_F F 3 4 m
  | ⟨5, _⟩, ⟨6, _⟩ => suffixBlockProj_F F 3 4 m (by omega)
  -- Arm 3 (suffix flag): edge {4, 5}
  | ⟨5, _⟩, ⟨4, _⟩ => suffixBlockEmbed_F F 4 5 m
  | ⟨4, _⟩, ⟨5, _⟩ => suffixBlockProj_F F 4 5 m (by omega)
  -- Arm 3 (suffix flag): edge {0, 4}
  | ⟨4, _⟩, ⟨0, _⟩ => suffixBlockEmbed_F F 5 6 m
  | ⟨0, _⟩, ⟨4, _⟩ => suffixBlockProj_F F 5 6 m (by omega)
  -- Non-edge or impossible (ruled out by `hOrient`); placeholder
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic T(1, 2, 5) = Ẽ₈ representation over an arbitrary
algebraically closed field `F` with arbitrary orientation `Q` of
`t125Adj`. Dimension vector follows `t125Dim`: vertex 0 has dim `6(m+1)`,
vertex 4 has `5(m+1)`, vertices 2/5 have `4(m+1)`, vertices 1/6 have
`3(m+1)`, vertices 3/7 have `2(m+1)`, vertex 8 has `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the eight edges
of `t125Adj` contributes one canonical map (arrow toward the center) and
one reverse map. The orientation hypothesis `_hOrient` is not used by the
construction itself; it is recorded so that downstream lemmas (the
indecomposability proof) can pattern-match on which arrows exist. -/
noncomputable def t125Rep_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 9 Q t125Adj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 9) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (t125Dim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => t125RepMap_kQ F (t125TubeLam F) m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic Ẽ₈ rep has the expected dimension vector
`t125Dim m` at each vertex. -/
theorem t125Rep_kQ_dimVec
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q t125Adj)
    (m : ℕ) (v : Fin 9) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 9) _ Q
      (t125Rep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (t125Dim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 3b: Orientation-canonical flag-collapse helpers (sub-B1 of #4612)

The two flag arms enter the center as nested coordinate flags: arm 2 is the
**prefix** flag `3 → 2 → 0`, arm 3 the **suffix** flag `8 → 7 → 6 → 5 → 4 → 0`.
For the *canonical* orientation (every arrow pointing toward the center), a
subrep-invariant family `W` carries each arm vertex into the corresponding
prefix/suffix blocks of the center `W ⟨0⟩`. These helpers fold the per-edge
invariance facts into a single arm→center containment using the landed
composition laws (`prefixBlockEmbed_comp_F` / `suffixBlockEmbed_comp_F`).

They are the orientation-canonical building blocks consumed by the
all-canonical branch of `t125Rep_kQ_leaf_equalities` (sub-B2, #4620): the
flags collapse `W ⟨2⟩, W ⟨3⟩` (resp. `W ⟨4⟩, …, W ⟨8⟩`) onto blocks of
`W ⟨0⟩`, where the arm-1 eigenvalue core deposits the `(λ • id + J)`-invariant
pair (sub-C, #4613). Mirrors the `leaf_sub` shape inside
`starTubeRepGen_isIndecomposable` (`FieldGenericTube.lean`), but the flag is a
single chain (no cross-leaf overlap within an arm), so only forward
composition is needed — the cross-arm disentangling lives at the center. -/

/-- **Prefix-flag forward containment (arm 2, canonical `3 → 2 → 0`).** Given
the two canonical prefix-edge invariance facts (`3 → 2` via
`prefixBlockEmbed_F 2 4`, `2 → 0` via `prefixBlockEmbed_F 4 6`), the arm-2 leaf
`W3` lands in the first two blocks of the center: `x ∈ W3` implies
`prefixBlockEmbed_F 2 6 x ∈ W0`. The `2 → 0` containment is the hypothesis
`hW_20`; this lemma supplies the composed `3 → 0` containment.

Stated over explicit center/arm submodules (`W0`, `W2`, `W3`) rather than the
rep family `W`, so it elaborates without unfolding `(t125Rep_kQ …).obj` and is
reusable by the Ẽ₆/Ẽ₇ prefix flags too. Call sites pass `W ⟨0⟩`, `W ⟨2⟩`,
`W ⟨3⟩`; the block dims match `t125Dim` by defeq. -/
theorem t125_prefix_sub
    (F : Type) [Field F] (m : ℕ)
    (W0 : Submodule F (Fin (6 * (m + 1)) → F))
    (W2 : Submodule F (Fin (4 * (m + 1)) → F))
    (W3 : Submodule F (Fin (2 * (m + 1)) → F))
    (hW_32 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ W3 →
        prefixBlockEmbed_F F 2 4 m x ∈ W2)
    (hW_20 : ∀ (y : Fin (4 * (m + 1)) → F), y ∈ W2 →
        prefixBlockEmbed_F F 4 6 m y ∈ W0) :
    ∀ (x : Fin (2 * (m + 1)) → F), x ∈ W3 →
        prefixBlockEmbed_F F 2 6 m x ∈ W0 := by
  intro x hx
  have h0 := hW_20 _ (hW_32 x hx)
  rwa [prefixBlockEmbed_comp_F F 2 4 6 m (by omega)] at h0

/-- **Suffix-flag forward containment (arm 3, canonical `8 → 7 → 6 → 5 → 4 → 0`).**
Given the five canonical suffix-edge invariance facts (`8 → 7` via
`starEmbed2_F`, then `suffixBlockEmbed_F 2 3`, `3 4`, `4 5`, `5 6`), every arm-3
vertex lands in the corresponding suffix blocks of the center. The `4 → 0`
containment is the hypothesis `hW_40`; this lemma folds the remaining hops into
the composed `5 → 0`, `6 → 0`, `7 → 0`, `8 → 0` containments. The leaf `W8`
has dim `m + 1` (not `1 · (m + 1)`), so its hop uses `starEmbed2_F`; the
result is left as the composite `suffixBlockEmbed_F 2 6 (starEmbed2_F x)`.

Stated over explicit center/arm submodules (as `t125_prefix_sub`); call sites
pass `W ⟨0⟩`, `W ⟨4⟩`, …, `W ⟨8⟩`. -/
theorem t125_suffix_sub
    (F : Type) [Field F] (m : ℕ)
    (W0 : Submodule F (Fin (6 * (m + 1)) → F))
    (W4 : Submodule F (Fin (5 * (m + 1)) → F))
    (W5 : Submodule F (Fin (4 * (m + 1)) → F))
    (W6 : Submodule F (Fin (3 * (m + 1)) → F))
    (W7 : Submodule F (Fin (2 * (m + 1)) → F))
    (W8 : Submodule F (Fin (m + 1) → F))
    (hW_87 : ∀ (x : Fin (m + 1) → F), x ∈ W8 →
        starEmbed2_F F m x ∈ W7)
    (hW_76 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ W7 →
        suffixBlockEmbed_F F 2 3 m x ∈ W6)
    (hW_65 : ∀ (x : Fin (3 * (m + 1)) → F), x ∈ W6 →
        suffixBlockEmbed_F F 3 4 m x ∈ W5)
    (hW_54 : ∀ (x : Fin (4 * (m + 1)) → F), x ∈ W5 →
        suffixBlockEmbed_F F 4 5 m x ∈ W4)
    (hW_40 : ∀ (x : Fin (5 * (m + 1)) → F), x ∈ W4 →
        suffixBlockEmbed_F F 5 6 m x ∈ W0) :
    (∀ (x : Fin (4 * (m + 1)) → F), x ∈ W5 →
        suffixBlockEmbed_F F 4 6 m x ∈ W0) ∧
    (∀ (x : Fin (3 * (m + 1)) → F), x ∈ W6 →
        suffixBlockEmbed_F F 3 6 m x ∈ W0) ∧
    (∀ (x : Fin (2 * (m + 1)) → F), x ∈ W7 →
        suffixBlockEmbed_F F 2 6 m x ∈ W0) ∧
    (∀ (x : Fin (m + 1) → F), x ∈ W8 →
        suffixBlockEmbed_F F 2 6 m (starEmbed2_F F m x) ∈ W0) := by
  have h5 : ∀ (x : Fin (4 * (m + 1)) → F), x ∈ W5 →
      suffixBlockEmbed_F F 4 6 m x ∈ W0 := by
    intro x hx
    have h := hW_40 _ (hW_54 x hx)
    rwa [suffixBlockEmbed_comp_F F 4 5 6 m (by omega) (by omega)] at h
  have h6 : ∀ (x : Fin (3 * (m + 1)) → F), x ∈ W6 →
      suffixBlockEmbed_F F 3 6 m x ∈ W0 := by
    intro x hx
    have h := h5 _ (hW_65 x hx)
    rwa [suffixBlockEmbed_comp_F F 3 4 6 m (by omega) (by omega)] at h
  have h7 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ W7 →
      suffixBlockEmbed_F F 2 6 m x ∈ W0 := by
    intro x hx
    have h := h6 _ (hW_76 x hx)
    rwa [suffixBlockEmbed_comp_F F 2 3 6 m (by omega) (by omega)] at h
  exact ⟨h5, h6, h7, fun x hx => h7 _ (hW_87 x hx)⟩

/-! ## Section 3c: All-canonical arm→center collapse spine (sub-B2 of #4612, #4620)

The all-canonical orientation branch of the leaf-collapse: every arm flag
points toward the center (`1→0`, `3→2→0`, `8→7→6→5→4→0`). Given the eight
raw per-edge invariance facts for a single invariant family, every
non-center vertex's subspace lands in the center along its composite arm
embedding. This folds the sub-B1 flag helpers (`t125_prefix_sub`,
`t125_suffix_sub`) over the arm-2 prefix and arm-3 suffix flags, and passes
the arm-1 eigenvalue-tube push through unchanged.

**Why this is stated over explicit `Fin (k·(m+1)) → F` carriers** (not the
rep family `W : ∀ v, Submodule F ((t125Rep_kQ …).obj v)`): the structure
projection `(t125Rep_kQ …).obj ⟨v, …⟩` does not reduce under the
type-class-instance transparency used by `Membership` synthesis, so a
hypothesis or goal of the form `(x : Fin (k·(m+1)) → F) ∈ W ⟨v⟩` fails to
elaborate in a top-level signature (the `obj` carrier and the concrete
`Fin` type never unify, even though they are propositionally — and, with
`t125Dim` kept symbolic, definitionally — equal). The same wall blocks a
rep-level `t125Rep_kQ_leaf_equalities`; the bridge from `W ⟨v⟩` to these
explicit carriers must therefore be performed *inside* the indecomposability
proof (sub-C, #4613), where `simp only [t125Rep_kQ, t125RepMap_kQ]` unfolds
the rep and the per-edge facts elaborate (exactly as the local `core` /
`leaf*_sub` haves do inside `starTubeRepGen_isIndecomposable`,
`FieldGenericTube.lean`). This matches the explicit-carrier style of the
landed sub-B1 helpers. -/

/-- **All-canonical arm→center collapse spine** (explicit-carrier form).
From the eight canonical per-edge containments (arm-1 eigenvalue tube push
`1→0`; arm-2 prefix pushes `3→2`, `2→0`; arm-3 suffix pushes `8→7`, `7→6`,
`6→5`, `5→4`, `4→0`), derive that every non-center vertex embeds into the
center `W0` along its full arm flag. The arm-2 leaf (`W3`) and arm-3 vertices
(`W5`–`W8`) are folded through the flags by `t125_prefix_sub` /
`t125_suffix_sub`; the arm-1 (`W1`), arm-2 inner (`W2`) and arm-3 deepest
(`W4`) containments are the corresponding hypotheses verbatim. -/
theorem t125_canonical_collapse
    (F : Type) [Field F] (lam : F) (m : ℕ)
    (W0 : Submodule F (Fin (6 * (m + 1)) → F))
    (W1 : Submodule F (Fin (3 * (m + 1)) → F))
    (W2 : Submodule F (Fin (4 * (m + 1)) → F))
    (W3 : Submodule F (Fin (2 * (m + 1)) → F))
    (W4 : Submodule F (Fin (5 * (m + 1)) → F))
    (W5 : Submodule F (Fin (4 * (m + 1)) → F))
    (W6 : Submodule F (Fin (3 * (m + 1)) → F))
    (W7 : Submodule F (Fin (2 * (m + 1)) → F))
    (W8 : Submodule F (Fin (m + 1) → F))
    (h10 : ∀ (x : Fin (3 * (m + 1)) → F), x ∈ W1 →
        t125Arm1Tube_F F lam m x ∈ W0)
    (h32 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ W3 →
        prefixBlockEmbed_F F 2 4 m x ∈ W2)
    (h20 : ∀ (x : Fin (4 * (m + 1)) → F), x ∈ W2 →
        prefixBlockEmbed_F F 4 6 m x ∈ W0)
    (h87 : ∀ (x : Fin (m + 1) → F), x ∈ W8 →
        starEmbed2_F F m x ∈ W7)
    (h76 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ W7 →
        suffixBlockEmbed_F F 2 3 m x ∈ W6)
    (h65 : ∀ (x : Fin (3 * (m + 1)) → F), x ∈ W6 →
        suffixBlockEmbed_F F 3 4 m x ∈ W5)
    (h54 : ∀ (x : Fin (4 * (m + 1)) → F), x ∈ W5 →
        suffixBlockEmbed_F F 4 5 m x ∈ W4)
    (h40 : ∀ (x : Fin (5 * (m + 1)) → F), x ∈ W4 →
        suffixBlockEmbed_F F 5 6 m x ∈ W0) :
    -- arm 1 (eigenvalue tube): v1 → center
    (∀ (x : Fin (3 * (m + 1)) → F), x ∈ W1 →
        t125Arm1Tube_F F lam m x ∈ W0) ∧
    -- arm 2 (prefix flag): v2, v3 → center
    (∀ (x : Fin (4 * (m + 1)) → F), x ∈ W2 →
        prefixBlockEmbed_F F 4 6 m x ∈ W0) ∧
    (∀ (x : Fin (2 * (m + 1)) → F), x ∈ W3 →
        prefixBlockEmbed_F F 2 6 m x ∈ W0) ∧
    -- arm 3 (suffix flag): v4, v5, v6, v7, v8 → center
    (∀ (x : Fin (5 * (m + 1)) → F), x ∈ W4 →
        suffixBlockEmbed_F F 5 6 m x ∈ W0) ∧
    (∀ (x : Fin (4 * (m + 1)) → F), x ∈ W5 →
        suffixBlockEmbed_F F 4 6 m x ∈ W0) ∧
    (∀ (x : Fin (3 * (m + 1)) → F), x ∈ W6 →
        suffixBlockEmbed_F F 3 6 m x ∈ W0) ∧
    (∀ (x : Fin (2 * (m + 1)) → F), x ∈ W7 →
        suffixBlockEmbed_F F 2 6 m x ∈ W0) ∧
    (∀ (x : Fin (m + 1) → F), x ∈ W8 →
        suffixBlockEmbed_F F 2 6 m (starEmbed2_F F m x) ∈ W0) := by
  have hpre := t125_prefix_sub F m W0 W2 W3 h32 h20
  obtain ⟨hsuf5, hsuf6, hsuf7, hsuf8⟩ :=
    t125_suffix_sub F m W0 W4 W5 W6 W7 W8 h87 h76 h65 h54 h40
  exact ⟨h10, h20, hpre, h40, hsuf5, hsuf6, hsuf7, hsuf8⟩

/-! ## Section 3d: Arm-1 eigenvalue-site deposit (sub-B1 of #4612, #4633)

The arm-1 eigenvalue tube `t125Arm1Tube_F` couples all six center blocks
through the moment curve `c_k = P + Λ^k Q + Λ^{2k} R` (`Λ = λ•id + J`). The
indecomposability assembly (sub-C, #4613) needs from this arm only the
`(λ•id + J)`-invariance deposit at the common `F^{m+1}` eigenvalue site — the
hypothesis fed to `eigenvalue_jordan_invariant_compl_trivial_gen`.

The key observation that avoids inverting the full block-Vandermonde: feed the
arm-1 leaf the **Q-concentrated** input `(0, x, 0)` (`x` placed in the middle
block). Then every moment-curve coefficient collapses, `c_k = Λ^k x`, so the
center's block-`1` readout is exactly `Λ x = jordanShiftLinGen x`. Combined
with the leaf collapse (the middle leaf block embeds into `W ⟨1⟩`, the arm-1
push lands in `W ⟨0⟩`, and the center block-`1` readout returns to the common
site `U`), this yields `(λ•id + J)`-invariance of `U` directly. -/

/-- Off-diagonal block retraction: `blockProjAtN_F` at offset `o` reads zero
from a single block placed by `blockEmbedAtN_F` at a **disjoint** offset `o'`
(`o + (m+1) ≤ o'` or `o' + (m+1) ≤ o`). Companion of
`blockProjAtN_comp_embed_F` (same-offset readout) for the eigenvalue-tube
block disentangling. -/
theorem blockProjAtN_embedAtN_disjoint_F (F : Type) [Field F] (o o' N m : ℕ)
    (h : o + (m + 1) ≤ N) (hdis : o + (m + 1) ≤ o' ∨ o' + (m + 1) ≤ o)
    (x : Fin (m + 1) → F) :
    blockProjAtN_F F o N m h (blockEmbedAtN_F F o' N m x) = 0 := by
  ext i
  have hi := i.isLt
  simp only [blockProjAtN_F, blockEmbedAtN_F, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply]
  rw [dif_neg (by omega)]

/-- **Q-concentrated moment-curve readout.** The arm-1 tube applied to the
middle-block input `(0, x, 0)` has center block-`1` readout `Λ x`, i.e.
`jordanShiftLinGen F lam m x`. This is the single moment-curve fact the
eigenvalue-site deposit needs: all six blocks are `Λ^k x`, and block `1` is
`Λ x`. -/
theorem t125Arm1Tube_blockProj1_Qonly_F (F : Type) [Field F] (lam : F) (m : ℕ)
    (x : Fin (m + 1) → F) :
    blockProjAtN_F F (m + 1) (6 * (m + 1)) m (by omega)
        (t125Arm1Tube_F F lam m
          (blockEmbedAtN_F F (m + 1) (3 * (m + 1)) m x)) =
      jordanShiftLinGen F lam m x := by
  -- The three input-block projections of `(0, x, 0)`.
  have hP : blockProjAtN_F F 0 (3 * (m + 1)) m (by omega)
      (blockEmbedAtN_F F (m + 1) (3 * (m + 1)) m x) = 0 :=
    blockProjAtN_embedAtN_disjoint_F F 0 (m + 1) (3 * (m + 1)) m (by omega)
      (Or.inl (by omega)) x
  have hQ : blockProjAtN_F F (m + 1) (3 * (m + 1)) m (by omega)
      (blockEmbedAtN_F F (m + 1) (3 * (m + 1)) m x) = x :=
    blockProjAtN_comp_embed_F F (m + 1) (3 * (m + 1)) m (by omega) x
  have hR : blockProjAtN_F F (2 * (m + 1)) (3 * (m + 1)) m (by omega)
      (blockEmbedAtN_F F (m + 1) (3 * (m + 1)) m x) = 0 :=
    blockProjAtN_embedAtN_disjoint_F F (2 * (m + 1)) (m + 1) (3 * (m + 1)) m
      (by omega) (Or.inr (by omega)) x
  rw [t125Arm1Tube_F]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hP, hQ, hR,
    map_zero, zero_add, add_zero]
  -- Now each summand is `blockProjAtN_F (m+1) (blockEmbedAtN_F (k*(m+1)) (Λ^k x))`.
  rw [blockProjAtN_embedAtN_disjoint_F F (m + 1) 0 (6 * (m + 1)) m (by omega)
        (Or.inr (by omega)),
      blockProjAtN_comp_embed_F F (m + 1) (6 * (m + 1)) m (by omega),
      blockProjAtN_embedAtN_disjoint_F F (m + 1) (2 * (m + 1)) (6 * (m + 1)) m
        (by omega) (Or.inl (by omega)),
      blockProjAtN_embedAtN_disjoint_F F (m + 1) (3 * (m + 1)) (6 * (m + 1)) m
        (by omega) (Or.inl (by omega)),
      blockProjAtN_embedAtN_disjoint_F F (m + 1) (4 * (m + 1)) (6 * (m + 1)) m
        (by omega) (Or.inl (by omega)),
      blockProjAtN_embedAtN_disjoint_F F (m + 1) (5 * (m + 1)) (6 * (m + 1)) m
        (by omega) (Or.inl (by omega))]
  simp only [add_zero, zero_add]

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- **Arm-1 eigenvalue-site deposit and complementary-pair finish.** Given a
complementary pair `(U, U')` at the common eigenvalue site `F^{m+1}`, the leaf
collapse (the middle leaf block embeds into the arm-1 leaf subspaces `W1`/`W1'`),
the arm-1 canonical invariance (`W1`/`W1'` push into the centers `W0`/`W0'`
under `t125Arm1Tube_F`), and the center block-`1` readout collapse (the centers
read back into `U`/`U'`), one of `U`, `U'` is trivial.

The deposit step: for `x ∈ U`, the Q-concentrated input `(0, x, 0)` lies in
`W1`, its arm-1 push lies in `W0`, and the block-`1` readout `Λ x` lies in `U`
(`t125Arm1Tube_blockProj1_Qonly_F`) — so `U` is `(λ•id + J)`-invariant, and
symmetrically `U'`. The complementary `J`-invariant pair is then killed by
`eigenvalue_jordan_invariant_compl_trivial_gen` (the eigenvalue `lam` drops
out). This is the arm-1 analogue of `leaf4_sub` inside
`starTubeRepGen_isIndecomposable` (`FieldGenericTube.lean`); sub-C (#4613)
supplies the collapse hypotheses from the flag spine and discharges the pair. -/
theorem t125_arm1_sub
    (F : Type) [Field F] (lam : F) (m : ℕ)
    (W0 W0' : Submodule F (Fin (6 * (m + 1)) → F))
    (W1 W1' : Submodule F (Fin (3 * (m + 1)) → F))
    (U U' : Submodule F (Fin (m + 1) → F))
    (hUemb : ∀ x : Fin (m + 1) → F, x ∈ U →
        blockEmbedAtN_F F (m + 1) (3 * (m + 1)) m x ∈ W1)
    (hU'emb : ∀ x : Fin (m + 1) → F, x ∈ U' →
        blockEmbedAtN_F F (m + 1) (3 * (m + 1)) m x ∈ W1')
    (hpush : ∀ y : Fin (3 * (m + 1)) → F, y ∈ W1 →
        t125Arm1Tube_F F lam m y ∈ W0)
    (hpush' : ∀ y : Fin (3 * (m + 1)) → F, y ∈ W1' →
        t125Arm1Tube_F F lam m y ∈ W0')
    (hread : ∀ w : Fin (6 * (m + 1)) → F, w ∈ W0 →
        blockProjAtN_F F (m + 1) (6 * (m + 1)) m (by omega) w ∈ U)
    (hread' : ∀ w : Fin (6 * (m + 1)) → F, w ∈ W0' →
        blockProjAtN_F F (m + 1) (6 * (m + 1)) m (by omega) w ∈ U')
    (hcompl : IsCompl U U') :
    U = ⊥ ∨ U' = ⊥ := by
  -- The eigenvalue-site invariance deposit, both sides.
  have deposit : ∀ (Wa : Submodule F (Fin (6 * (m + 1)) → F))
      (Wb : Submodule F (Fin (3 * (m + 1)) → F))
      (Ua : Submodule F (Fin (m + 1) → F)),
      (∀ x : Fin (m + 1) → F, x ∈ Ua →
        blockEmbedAtN_F F (m + 1) (3 * (m + 1)) m x ∈ Wb) →
      (∀ y : Fin (3 * (m + 1)) → F, y ∈ Wb →
        t125Arm1Tube_F F lam m y ∈ Wa) →
      (∀ w : Fin (6 * (m + 1)) → F, w ∈ Wa →
        blockProjAtN_F F (m + 1) (6 * (m + 1)) m (by omega) w ∈ Ua) →
      ∀ x : Fin (m + 1) → F, x ∈ Ua → jordanShiftLinGen F lam m x ∈ Ua := by
    intro Wa Wb Ua hemb hp hr x hx
    have h1 := hemb x hx
    have h2 := hp _ h1
    have h3 := hr _ h2
    rwa [t125Arm1Tube_blockProj1_Qonly_F] at h3
  exact eigenvalue_jordan_invariant_compl_trivial_gen
    (nilpotentShiftLinGen F m) (nilpotentShiftLinGen_nilpotent F m)
    (nilpotentShiftLinGen_ker_finrank F m) lam U U'
    (deposit W0 W1 U hUemb hpush hread)
    (deposit W0' W1' U' hU'emb hpush' hread') hcompl

/-! ## Section 3e: Center spanning decomposition (propagation support, #4613)

The indecomposability propagation step needs that the canonical arm-2 and arm-3
images jointly span the center: from `W' ⟨2⟩ = ⊤` (arm-2 prefix top) and
`W' ⟨4⟩ = ⊤` (arm-3 suffix top), the canonical pushes place
`prefixBlockEmbed_F 4 6` (center blocks `0–3`) and `suffixBlockEmbed_F 5 6`
(center blocks `1–5`) entirely in `W' ⟨0⟩`. Since blocks `0–3` and `1–5` cover
all six blocks, this forces `W' ⟨0⟩ = ⊤`. This is the T(1,2,5) analogue of
`center_decomp_F` (`FieldGenericStar.lean`). -/

/-- **Center spanning decomposition** (arm-2 prefix + arm-3 suffix). Every
center vector `w : F^{6(m+1)}` is the sum of an arm-2 prefix embed (image =
blocks `0–3`) and an arm-3 suffix embed (image = blocks `1–5`); the suffix
summand is chosen supported on blocks `4–5` so the two images tile all six
blocks without overlap. The two arm images therefore span the center, which is
the spanning fact the canonical-orientation propagation uses to collapse the
center vertex. -/
theorem t125_center_decomp_F (F : Type) [Field F] (m : ℕ)
    (w : Fin (6 * (m + 1)) → F) :
    ∃ (a : Fin (4 * (m + 1)) → F) (b : Fin (5 * (m + 1)) → F),
      w = prefixBlockEmbed_F F 4 6 m a + suffixBlockEmbed_F F 5 6 m b := by
  refine ⟨fun i => w ⟨i.val, by omega⟩,
    fun i => if 3 * (m + 1) ≤ i.val then w ⟨i.val + (m + 1), by omega⟩ else 0, ?_⟩
  ext j
  have hj := j.isLt
  simp only [Pi.add_apply, prefixBlockEmbed_F, suffixBlockEmbed_F, LinearMap.coe_mk,
    AddHom.coe_mk]
  by_cases hlt : j.val < 4 * (m + 1)
  · rw [dif_pos hlt]
    have hsuf : (if h : (6 - 5) * (m + 1) ≤ j.val ∧
        j.val - (6 - 5) * (m + 1) < 5 * (m + 1) then
        (if 3 * (m + 1) ≤ j.val - (6 - 5) * (m + 1) then
          w ⟨j.val - (6 - 5) * (m + 1) + (m + 1), by omega⟩ else 0)
        else (0 : F)) = 0 := by
      split_ifs with h1 h2
      · exact absurd h2 (by omega)
      · rfl
      · rfl
    rw [hsuf, add_zero]
  · rw [dif_neg hlt,
      dif_pos (show (6 - 5) * (m + 1) ≤ j.val ∧
        j.val - (6 - 5) * (m + 1) < 5 * (m + 1) from ⟨by omega, by omega⟩),
      if_pos (show 3 * (m + 1) ≤ j.val - (6 - 5) * (m + 1) from by omega),
      zero_add]
    have hidx : j.val - (6 - 5) * (m + 1) + (m + 1) = j.val := by omega
    exact congrArg w (Fin.ext hidx.symm)

/-! ## Section 4: Indecomposability (corrected homogeneous tube)

`t125Rep_kQ` is now the genuine homogeneous tube `R_λ^{(m+1)}` at the
generic eigenvalue `t125TubeLam F`, so the statement below is **true**. The
single `sorry` is the indecomposability *proof*, deferred to the sub-C
assembly (the leaf-equality case tree is sub-B), modelled on
`starTubeRepGen_isIndecomposable` (`FieldGenericTube.lean`): the arm-2
prefix flag and arm-3 suffix flag collapse every vertex onto a common
`F^{m+1}`, where arm 1 deposits the `(λ•id + J)`-invariant complementary
pair killed by `eigenvalue_jordan_invariant_compl_trivial_gen`. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of the corrected Ẽ₈
homogeneous-tube representation `t125Rep_kQ`.

This is a **true** statement: `t125Rep_kQ` is the homogeneous tube
`R_λ^{(m+1)}` of the regular simple `S_λ` (a brick for the generic
eigenvalue `t125TubeLam F`; see `t125TubeLam_distinct`). The proof is a
single `sorry`, deferred to the sub-C assembly modelled on
`starTubeRepGen_isIndecomposable`.

The `1 ≤ m` hypothesis is retained: for `m = 0` the Jordan block is a
scalar and there is no eigenvalue-site nilpotent to drive the splitting
(the infinite-type argument ranges over `m + 1 ≥ 1`). -/
theorem t125Rep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q t125Adj)
    (m : ℕ) (hm : 1 ≤ m) :
    (t125Rep_kQ F Q hOrient m).IsIndecomposable := by
  let _ := hm  -- retain `hm` in the signature for the sub-C proof
  sorry

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `t125_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `t125Adj`, the
set of dimension vectors of indecomposable representations of `Q` over
`F` is infinite.

Mirrors `etilde7_not_finite_type_per_kQ`: we range over `m + 1` (not `m`)
because `t125Rep_kQ_isIndecomposable` requires `1 ≤ m`. Injectivity comes
from vertex `8`, where `t125Dim m 8 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`t125Rep_kQ_isIndecomposable`, which is a single `sorry` of a *true*
statement (the corrected homogeneous tube). -/
theorem t125_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q t125Adj) :
    ¬ Set.Finite
      {d : Fin 9 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 9) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, (fun v : Fin 9 => t125Dim (m + 1) v) ∈
      {d : Fin 9 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 9) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨t125Rep_kQ F Q hOrient (m + 1),
      t125Rep_kQ_isIndecomposable F Q hOrient (m + 1) (Nat.succ_le_succ m.zero_le),
      t125Rep_kQ_dimVec F Q hOrient (m + 1)⟩
  have hinj : Function.Injective (fun m : ℕ => fun v : Fin 9 => t125Dim (m + 1) v) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨8, by omega⟩
    simp only [t125Dim] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

set_option maxHeartbeats 3200000 in
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) port of `embed_t125_in_tree`
(`InfiniteTypeConstructions.lean:4918-5279`): given 9 vertices forming
T(1, 2, 5) inside an acyclic simple graph, embed and dispatch to
`t125_not_finite_type_per_kQ` via `subgraph_infinite_type_transfer_per_kQ`.

Vertex roles: `v₀` (center), `u₁` (arm of length 1), `p₁`-`p₂` (arm of
length 2), `q₁`-`q₂`-`q₃`-`q₄`-`q₅` (arm of length 5).
Embedding map: 0→v₀, 1→u₁, 2→p₁, 3→p₂, 4→q₁, 5→q₂, 6→q₃, 7→q₄, 8→q₅.

Shared helper used by both
`single_branch_leaf_both_extend_b3leaf_per_kQ` (sub-B, d₂-extends case,
issue #2913) and `single_branch_leaf_both_extend_b2leaf_per_kQ`
(sub-C, d₃-extends case, issue #2915). -/
theorem embed_t125_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ u₁ p₁ p₂ q₁ q₂ q₃ q₄ q₅ : Fin n)
    (hu₁ : adj v₀ u₁ = 1) (hp₁ : adj v₀ p₁ = 1) (hp₂ : adj p₁ p₂ = 1)
    (hq₁ : adj v₀ q₁ = 1) (hq₂ : adj q₁ q₂ = 1)
    (hq₃ : adj q₂ q₃ = 1) (hq₄ : adj q₃ q₄ = 1) (hq₅ : adj q₄ q₅ = 1)
    (hu₁_ne_p₁ : u₁ ≠ p₁) (hu₁_ne_q₁ : u₁ ≠ q₁) (hp₁_ne_q₁ : p₁ ≠ q₁)
    (hp₂_ne_v₀ : p₂ ≠ v₀) (hq₂_ne_v₀ : q₂ ≠ v₀)
    (hq₃_ne_q₁ : q₃ ≠ q₁) (hq₄_ne_q₂ : q₄ ≠ q₂) (hq₅_ne_q₃ : q₅ ≠ q₃)
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
  have hv₀_ne_p₁ := ne_of_adj' v₀ p₁ hp₁
  have hp₁_ne_p₂ := ne_of_adj' p₁ p₂ hp₂
  have hv₀_ne_q₁ := ne_of_adj' v₀ q₁ hq₁
  have hq₁_ne_q₂ := ne_of_adj' q₁ q₂ hq₂
  have hq₂_ne_q₃ := ne_of_adj' q₂ q₃ hq₃
  have hq₃_ne_q₄ := ne_of_adj' q₃ q₄ hq₄
  have hq₄_ne_q₅ := ne_of_adj' q₄ q₅ hq₅
  -- Reversed edges
  have hp₁_v₀ : adj p₁ v₀ = 1 := (adj_comm p₁ v₀).trans hp₁
  have hp₂_p₁ : adj p₂ p₁ = 1 := (adj_comm p₂ p₁).trans hp₂
  have hq₁_v₀ : adj q₁ v₀ = 1 := (adj_comm q₁ v₀).trans hq₁
  have hq₂_q₁ : adj q₂ q₁ = 1 := (adj_comm q₂ q₁).trans hq₂
  have hq₃_q₂ : adj q₃ q₂ = 1 := (adj_comm q₃ q₂).trans hq₃
  have hq₄_q₃ : adj q₄ q₃ = 1 := (adj_comm q₄ q₃).trans hq₄
  have hq₅_q₄ : adj q₅ q₄ = 1 := (adj_comm q₅ q₄).trans hq₅
  -- Distance-2 non-edges (acyclic_no_triangle)
  have hu₁p₁ : adj u₁ p₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ p₁
      hu₁_ne_p₁ hv₀_ne_u₁.symm hv₀_ne_p₁.symm hu₁ hp₁
  have hu₁q₁ : adj u₁ q₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ q₁
      hu₁_ne_q₁ hv₀_ne_u₁.symm hv₀_ne_q₁.symm hu₁ hq₁
  have hp₁q₁ : adj p₁ q₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ p₁ q₁
      hp₁_ne_q₁ hv₀_ne_p₁.symm hv₀_ne_q₁.symm hp₁ hq₁
  have hv₀p₂ : adj v₀ p₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p₁ v₀ p₂
      hp₂_ne_v₀.symm hv₀_ne_p₁ hp₁_ne_p₂.symm hp₁_v₀ hp₂
  have hv₀q₂ : adj v₀ q₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₁ v₀ q₂
      hq₂_ne_v₀.symm hv₀_ne_q₁ hq₁_ne_q₂.symm hq₁_v₀ hq₂
  have hq₁q₃ : adj q₁ q₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₂ q₁ q₃
      hq₃_ne_q₁.symm hq₁_ne_q₂ hq₂_ne_q₃.symm hq₂_q₁ hq₃
  have hq₂q₄ : adj q₂ q₄ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₃ q₂ q₄
      hq₄_ne_q₂.symm hq₂_ne_q₃ hq₃_ne_q₄.symm hq₃_q₂ hq₄
  have hq₃q₅ : adj q₃ q₅ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₄ q₃ q₅
      hq₅_ne_q₃.symm hq₃_ne_q₄ hq₄_ne_q₅.symm hq₄_q₃ hq₅
  -- Cross-arm ne (level 1)
  have hu₁_ne_p₂ : u₁ ≠ p₂ := by intro h; rw [h] at hu₁; linarith [hv₀p₂]
  have hu₁_ne_q₂ : u₁ ≠ q₂ := by intro h; rw [h] at hu₁; linarith [hv₀q₂]
  have hp₁_ne_q₂ : p₁ ≠ q₂ := by intro h; rw [h] at hp₁; linarith [hv₀q₂]
  have hp₂_ne_q₁ : p₂ ≠ q₁ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₁, hp₁q₁]
  have hv₀_ne_q₃ : v₀ ≠ q₃ := by intro h; rw [← h] at hq₃; linarith [adj_comm q₂ v₀, hv₀q₂]
  have hq₁_ne_q₄ : q₁ ≠ q₄ := by intro h; rw [← h] at hq₄; linarith [adj_comm q₃ q₁, hq₁q₃]
  have hq₂_ne_q₅ : q₂ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ q₂, hq₂q₄]
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
  have path_nodup8 : ∀ (a b c d e f g h : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f → a ≠ g → a ≠ h →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f → b ≠ g → b ≠ h →
      c ≠ d → c ≠ e → c ≠ f → c ≠ g → c ≠ h →
      d ≠ e → d ≠ f → d ≠ g → d ≠ h →
      e ≠ f → e ≠ g → e ≠ h → f ≠ g → f ≠ h → g ≠ h →
      [a, b, c, d, e, f, g, h].Nodup := by
    intro a b c d e f g h₀ hab hac had hae haf hag hah hbc hbd hbe hbf hbg hbh
      hcd hce hcf hcg hch hde hdf hdg hdh hef heg heh hfg hfh hgh
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf, hag, hah⟩,
      ⟨hbc, hbd, hbe, hbf, hbg, hbh⟩,
      ⟨hcd, hce, hcf, hcg, hch⟩, ⟨hde, hdf, hdg, hdh⟩,
      ⟨hef, heg, heh⟩, ⟨hfg, hfh⟩, hgh⟩
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
  have path_edges8 : ∀ (a b c d e f g h : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      adj e f = 1 → adj f g = 1 → adj g h = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f, g, h].length) →
        adj ([a, b, c, d, e, f, g, h].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f, g, h].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f g h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ k hk
    have : k + 1 < 8 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- Distance-3 non-edges (4-vertex paths)
  have hu₁p₂ : adj u₁ p₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [p₂, p₁, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hp₁_ne_p₂.symm hp₂_ne_v₀ hu₁_ne_p₂.symm
        hv₀_ne_p₁.symm hu₁_ne_p₁.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hp₂_p₁ hp₁_v₀ hu₁)
  have hu₁q₂ : adj u₁ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm
        hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₂ : adj p₁ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, p₁] (by simp)
      (path_nodup4 _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges4 _ _ _ _ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂_ne_q₁ : p₂ ≠ q₁ := by
    intro h; rw [h] at hv₀p₂; linarith [hq₁]
  have hp₂q₁ : adj p₂ q₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₁, v₀, p₁, p₂] (by simp)
      (path_nodup4 _ _ _ _ hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm
        hv₀_ne_p₁ hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges4 _ _ _ _ hq₁_v₀ hp₁ hp₂)
  have hq₁_ne_q₃ : q₁ ≠ q₃ := hq₃_ne_q₁.symm
  have hv₀q₃ : adj v₀ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀] (by simp)
      (path_nodup4 _ _ _ _ hq₂_ne_q₃.symm hq₃_ne_q₁ hv₀_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges4 _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  have hq₂_ne_q₄ : q₂ ≠ q₄ := hq₄_ne_q₂.symm
  have hq₁q₄ : adj q₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁] (by simp)
      (path_nodup4 _ _ _ _ hq₃_ne_q₄.symm hq₄_ne_q₂ hq₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₃_ne_q₁ hq₁_ne_q₂.symm)
      (path_edges4 _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁)
  have hq₃_ne_q₅ : q₃ ≠ q₅ := hq₅_ne_q₃.symm
  have hq₂q₅ : adj q₂ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂] (by simp)
      (path_nodup4 _ _ _ _ hq₄_ne_q₅.symm hq₅_ne_q₃ hq₂_ne_q₅.symm
        hq₃_ne_q₄.symm hq₄_ne_q₂ hq₂_ne_q₃.symm)
      (path_edges4 _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂)
  -- Cross-arm ne (level 2)
  have hu₁_ne_q₃ : u₁ ≠ q₃ := by intro h; rw [h] at hu₁; linarith [hv₀q₃]
  have hp₁_ne_q₃ : p₁ ≠ q₃ := by intro h; rw [h] at hp₁; linarith [hv₀q₃]
  have hp₂_ne_q₂ : p₂ ≠ q₂ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₂, hp₁q₂]
  have hv₀_ne_q₄ : v₀ ≠ q₄ := by intro h; rw [← h] at hq₄; linarith [adj_comm q₃ v₀, hv₀q₃]
  have hq₁_ne_q₅ : q₁ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ q₁, hq₁q₄]
  -- Distance-4 non-edges (5-vertex paths)
  have hu₁q₃ : adj u₁ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges5 _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₃ : adj p₁ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges5 _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₂ : adj p₂ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup5 _ _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges5 _ _ _ _ _ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  have hv₀q₄ : adj v₀ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀] (by simp)
      (path_nodup5 _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges5 _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  have hq₁q₅ : adj q₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hq₂_ne_q₃.symm hq₁_ne_q₃.symm hq₁_ne_q₂.symm)
      (path_edges5 _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁)
  -- Cross-arm ne (level 3)
  have hu₁_ne_q₄ : u₁ ≠ q₄ := by intro h; rw [h] at hu₁; linarith [hv₀q₄]
  have hp₁_ne_q₄ : p₁ ≠ q₄ := by intro h; rw [h] at hp₁; linarith [hv₀q₄]
  have hp₂_ne_q₃ : p₂ ≠ q₃ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₃, hp₁q₃]
  have hv₀_ne_q₅ : v₀ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ v₀, hv₀q₄]
  -- Distance-5 non-edges (6-vertex paths)
  have hu₁q₄ : adj u₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hu₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges6 _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₄ : adj p₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges6 _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₃ : adj p₂ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges6 _ _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  have hv₀q₅ : adj v₀ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges6 _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  -- Cross-arm ne (level 4)
  have hu₁_ne_q₅ : u₁ ≠ q₅ := by intro h; rw [h] at hu₁; linarith [hv₀q₅]
  have hp₁_ne_q₅ : p₁ ≠ q₅ := by intro h; rw [h] at hp₁; linarith [hv₀q₅]
  have hp₂_ne_q₄ : p₂ ≠ q₄ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₄, hp₁q₄]
  -- Distance-6 non-edges (7-vertex paths)
  have hu₁q₅ : adj u₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hu₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hu₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges7 _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₅ : adj p₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hp₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges7 _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₄ : adj p₂ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm hp₂_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges7 _ _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  -- Cross-arm ne (level 5)
  have hp₂_ne_q₅ : p₂ ≠ q₅ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₅, hp₁q₅]
  -- Distance-7 non-edge (8-vertex path)
  have hp₂q₅ : adj p₂ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup8 _ _ _ _ _ _ _ _
        hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hp₁_ne_q₅.symm hp₂_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm hp₂_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges8 _ _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  -- Construct the embedding φ : Fin 9 ↪ Fin n for T(1,2,5)
  -- Map: 0→v₀, 1→u₁, 2→p₁, 3→p₂, 4→q₁, 5→q₂, 6→q₃, 7→q₄, 8→q₅
  let φ_fun : Fin 9 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => u₁  | ⟨2, _⟩ => p₁
    | ⟨3, _⟩ => p₂  | ⟨4, _⟩ => q₁  | ⟨5, _⟩ => q₂
    | ⟨6, _⟩ => q₃  | ⟨7, _⟩ => q₄  | ⟨8, _⟩ => q₅
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 9 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, t125Adj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [t125Adj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag v₀, hdiag u₁, hdiag p₁, hdiag p₂,
        hdiag q₁, hdiag q₂, hdiag q₃, hdiag q₄, hdiag q₅,
        hu₁, hp₁, hp₂, hq₁, hq₂, hq₃, hq₄, hq₅,
        adj_comm v₀ u₁, adj_comm v₀ p₁, adj_comm v₀ p₂,
        adj_comm v₀ q₁, adj_comm v₀ q₂, adj_comm v₀ q₃,
        adj_comm v₀ q₄, adj_comm v₀ q₅,
        adj_comm u₁ p₁, adj_comm u₁ p₂,
        adj_comm u₁ q₁, adj_comm u₁ q₂, adj_comm u₁ q₃,
        adj_comm u₁ q₄, adj_comm u₁ q₅,
        adj_comm p₁ p₂, adj_comm p₁ q₁, adj_comm p₁ q₂,
        adj_comm p₁ q₃, adj_comm p₁ q₄, adj_comm p₁ q₅,
        adj_comm p₂ q₁, adj_comm p₂ q₂, adj_comm p₂ q₃,
        adj_comm p₂ q₄, adj_comm p₂ q₅,
        adj_comm q₁ q₂, adj_comm q₁ q₃, adj_comm q₁ q₄, adj_comm q₁ q₅,
        adj_comm q₂ q₃, adj_comm q₂ q₄, adj_comm q₂ q₅,
        adj_comm q₃ q₄, adj_comm q₃ q₅,
        adj_comm q₄ q₅,
        hu₁p₁, hu₁q₁, hp₁q₁, hv₀p₂, hv₀q₂, hq₁q₃, hq₂q₄, hq₃q₅,
        hu₁p₂, hu₁q₂, hp₁q₂, hp₂q₁, hv₀q₃, hq₁q₄, hq₂q₅,
        hu₁q₃, hp₁q₃, hp₂q₂, hv₀q₄, hq₁q₅,
        hu₁q₄, hp₁q₄, hp₂q₃, hv₀q₅,
        hu₁q₅, hp₁q₅, hp₂q₄,
        hp₂q₅]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (t125_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
