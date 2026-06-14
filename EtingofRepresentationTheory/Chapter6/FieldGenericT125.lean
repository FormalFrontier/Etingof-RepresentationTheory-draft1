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
