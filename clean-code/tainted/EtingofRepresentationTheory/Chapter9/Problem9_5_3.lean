import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FiniteLength
import EtingofRepresentationTheory.Chapter9.Definition9_5_1
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_CompositionFactor
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_Connectivity
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_PrimitiveIdempotents

/-!
# Problem 9.5.3: Blocks and central idempotents

Etingof Problem 9.5.3 relates the block decomposition of a finite abelian category `𝒞`
(here the category of finite dimensional `A`-modules) to the structure of `A`.

* **(i)** There is a natural bijection between blocks of `𝒞` and *indecomposable* central
  idempotents `eₖ` of `A` (central idempotents that cannot be split nontrivially into a sum of
  two orthogonal central idempotents), under which `𝒞ₖ` is the category of `eₖ A`-modules.
  *(This file provides the ingredients — the central character of a simple module, its linkage
  invariance, and block connectivity from indecomposability. The bijection itself is assembled as
  the named `Etingof.Problem953.blockEquivIndecomposableCentralIdempotent` in
  `Problem9_5_3_BlockIdempotent.lean`, together with the characterization of `𝒞ₖ` as the modules
  supported by `eₖ`.)*

* **(ii)** Every indecomposable object of `𝒞` lies in some block `𝒞ₖ`, and
  `Hom(M, N) = 0` whenever `M ∈ 𝒞ₖ`, `N ∈ 𝒞ₗ` with `k ≠ l`. Thus `𝒞 = ⊕ₖ 𝒞ₖ`.

* **(iii)** Determine the blocks of the category of left `A`-modules for `A = k[S₃]` with `k`
  of characteristic `2`. *(This concrete modular-representation computation is discharged in
  `Problem9_5_3_S3Char2.lean`: `k[S₃] ≅ M₂(k) × k[t]/(t²)`, giving exactly two blocks.)*

## Formalization notes

Blocks are `Etingof.Block R` and block membership is `Etingof.InBlock R S M` (Definition
9.5.1). "Indecomposable central idempotent" is the predicate
`Etingof.Problem953.IsIndecomposableCentralIdempotent` (defined in
`Problem9_5_3_PrimitiveIdempotents.lean`, a nonzero central idempotent not expressible as a sum
of two nonzero orthogonal central idempotents).
"`Hom(M, N) = 0`" is `Subsingleton (M ⟶ N)`, and "indecomposable object" is
`CategoryTheory.Indecomposable`. Two blocks are distinct exactly when their representative
simple modules are not `Etingof.AreLinked`.
-/

universe v u

open CategoryTheory

namespace Etingof

namespace Problem953

variable (R : Type u) [Ring R]

/-- **Central character of a simple module (Schur's lemma).** A central idempotent `e` of a
ring `R` acts on any simple `R`-module `M` as the scalar `0` or `1`: either `e • m = 0` for all
`m`, or `e • m = m` for all `m`.

Indeed `φ : m ↦ e • m` is an `R`-linear endomorphism of `M` (centrality of `e` gives
`φ (r • m) = r • φ m`) which is idempotent (`e² = e`). Since `M` is simple, `Module.End R M` is a
division ring by Schur's lemma, and the only idempotents of a division ring are `0` and `1`, so
`φ = 0` or `φ = id`.

This is the building block for the block ↔ central-idempotent bijection of Problem 9.5.3(i): it
assigns to each simple module the set of central idempotents that act on it as `1` (its "central
character"), and linked simples turn out to share this character. The result holds for an
arbitrary ring; no finiteness is needed here. -/
theorem centralIdempotent_smul_simple {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] {e : R} (he : IsIdempotentElem e) (hc : ∀ y : R, e * y = y * e) :
    (∀ m : M, e • m = 0) ∨ (∀ m : M, e • m = m) := by
  classical
  -- `φ : m ↦ e • m` as an `R`-linear endomorphism of `M`; `R`-linearity uses centrality of `e`.
  let φ : Module.End R M :=
    { toFun := fun m => e • m
      map_add' := fun m₁ m₂ => smul_add e m₁ m₂
      map_smul' := fun r m => by simp only [RingHom.id_apply, smul_smul, hc r] }
  -- `φ` is idempotent because `e` is.
  have hφ : IsIdempotentElem φ := by
    ext m
    change e • e • m = e • m
    rw [smul_smul, he]
  -- `Module.End R M` is a division ring (Schur), whose only idempotents are `0` and `1`.
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hφ with h | h
  · left; intro m; exact LinearMap.congr_fun h m
  · right; intro m; exact LinearMap.congr_fun h m

/-- The type of **central idempotents** of `R`: idempotent elements lying in the center. This is
the domain of the central-character indicator `centralCharacter`. -/
abbrev CentralIdempotent : Type u :=
  {e : R // IsIdempotentElem e ∧ ∀ y : R, e * y = y * e}

open scoped Classical in
/-- **Central character of a simple module.** By `centralIdempotent_smul_simple` a central
idempotent `e` acts on the simple module `S` either as `0` or as the identity; this Boolean
records which, returning `true` exactly when `e` acts as the identity. It is the "central
character" of `S` at `e`, and Problem 9.5.3(i) shows it is constant on each linkage class. -/
noncomputable def centralCharacter {S : ModuleCat.{v} R} (_hS : IsSimpleModule R S)
    (e : CentralIdempotent R) : Bool :=
  decide (∀ m : (S : Type v), e.1 • m = m)

/-- `centralCharacter` is `true` exactly when the idempotent acts as the identity. -/
theorem centralCharacter_eq_true_iff {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (e : CentralIdempotent R) :
    centralCharacter R hS e = true ↔ ∀ m : (S : Type v), e.1 • m = m := by
  classical
  unfold centralCharacter
  rw [decide_eq_true_eq]

/-- `centralCharacter` is `false` exactly when the idempotent acts as `0`. -/
theorem centralCharacter_eq_false_iff {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (e : CentralIdempotent R) :
    centralCharacter R hS e = false ↔ ∀ m : (S : Type v), e.1 • m = 0 := by
  classical
  haveI := hS
  haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
  rw [← Bool.not_eq_true, centralCharacter_eq_true_iff]
  constructor
  · intro h
    rcases centralIdempotent_smul_simple R (M := (S : Type v)) (e := e.1) e.2.1 e.2.2 with h0 | h1
    · exact h0
    · exact absurd h1 h
  · intro h0 h1
    obtain ⟨x, hx⟩ := exists_ne (0 : (S : Type v))
    exact hx ((h1 x).symm.trans (h0 x))

open scoped ModuleCat.Algebra in
/-- **Naturality of a central scalar on `Ext`.** For a central element `z` of `R`, viewed as an
endomorphism `z • 𝟙` of every module, pre-composing an `Ext` class with `z • 𝟙 X` equals
post-composing it with `z • 𝟙 Y`: both equal the `z`-scalar multiple `z • α`. This is the
mechanism behind linkage invariance of the central character: `z • 𝟙` is a natural transformation
of the identity functor (centrality), and the category of `R`-modules is linear over the
(commutative) center of `R`, so scalar multiplication by `z` acts the same way through either
`Ext` variable. -/
theorem mk₀_smul_id_comp [Small.{v} R] (z : Subring.center R)
    {X Y : ModuleCat.{v} R} {n : ℕ} (α : Abelian.Ext X Y n) :
    (Abelian.Ext.mk₀ (z • 𝟙 X)).comp α (zero_add n) =
      α.comp (Abelian.Ext.mk₀ (z • 𝟙 Y)) (add_zero n) := by
  simp only [Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp, Abelian.Ext.comp_smul,
    Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]

open scoped ModuleCat.Algebra in
/-- **Ext-adjacency step of linkage invariance.** If simple modules `X`, `Y` are directly
`Ext¹`-linked (`Ext¹(X, Y) ≠ 0`), then a central idempotent `e` acts as the identity on `X` iff
it does on `Y`. If the two characters disagreed, `e` would act as `1` on one simple and `0` on the
other; by `mk₀_smul_id_comp` every class of `Ext¹(X, Y)` would then equal both `α` and `0`, forcing
`Ext¹(X, Y) = 0` and contradicting the adjacency. -/
theorem actsAsId_iff_of_directlyExtLinked [Small.{v} R] (e : CentralIdempotent R)
    {X Y : ModuleCat.{v} R} (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y)
    (hne : Etingof.DirectlyExtLinked R X Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  classical
  haveI := hX; haveI := hY
  haveI hntX : Nontrivial (X : Type v) := IsSimpleModule.nontrivial R (X : Type v)
  haveI hntY : Nontrivial (Y : Type v) := IsSimpleModule.nontrivial R (Y : Type v)
  haveI hneI : Nontrivial (Abelian.Ext X Y 1) := hne
  set z : Subring.center R :=
    ⟨e.1, Subring.mem_center_iff.mpr (fun g => (e.2.2 g).symm)⟩ with hz
  have hzsmul : ∀ {M : ModuleCat.{v} R} (m : (M : Type v)), z • m = e.1 • m := fun m => rfl
  have hid : ∀ {M : ModuleCat.{v} R}, (∀ m : (M : Type v), e.1 • m = m) → z • 𝟙 M = 𝟙 M := by
    intro M h
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [hzsmul m]; exact h m
  have hzero : ∀ {M : ModuleCat.{v} R}, (∀ m : (M : Type v), e.1 • m = 0) → z • 𝟙 M = 0 := by
    intro M h
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hzsmul m]; exact h m
  have notId : ∀ {M : ModuleCat.{v} R} [Nontrivial (M : Type v)],
      (∀ m : (M : Type v), e.1 • m = 0) → ¬ (∀ m : (M : Type v), e.1 • m = m) := by
    intro M _ h0 h1
    obtain ⟨x, hx⟩ := exists_ne (0 : (M : Type v))
    exact hx ((h1 x).symm.trans (h0 x))
  -- If the characters on `X` and `Y` disagree, every class of `Ext¹(X, Y)` vanishes.
  have keyXY : (∀ m : (X : Type v), e.1 • m = m) → (∀ m : (Y : Type v), e.1 • m = 0) → False := by
    intro hXi hY0
    have hz0 : ∀ α : Abelian.Ext X Y 1, α = 0 := by
      intro α
      have hnat := mk₀_smul_id_comp R z α
      rw [hid hXi, hzero hY0] at hnat
      simpa only [Abelian.Ext.mk₀_id_comp, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero] using hnat
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Abelian.Ext X Y 1)
    exact hab ((hz0 a).trans (hz0 b).symm)
  have keyYX : (∀ m : (X : Type v), e.1 • m = 0) → (∀ m : (Y : Type v), e.1 • m = m) → False := by
    intro hX0 hYi
    have hz0 : ∀ α : Abelian.Ext X Y 1, α = 0 := by
      intro α
      have hnat := mk₀_smul_id_comp R z α
      rw [hzero hX0, hid hYi] at hnat
      simpa only [Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_mk₀_id]
        using hnat.symm
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Abelian.Ext X Y 1)
    exact hab ((hz0 a).trans (hz0 b).symm)
  rcases centralIdempotent_smul_simple R (M := (X : Type v)) e.2.1 e.2.2 with hX0 | hXi
  · rcases centralIdempotent_smul_simple R (M := (Y : Type v)) e.2.1 e.2.2 with hY0 | hYi
    · exact iff_of_false (notId hX0) (notId hY0)
    · exact (keyYX hX0 hYi).elim
  · rcases centralIdempotent_smul_simple R (M := (Y : Type v)) e.2.1 e.2.2 with hY0 | hYi
    · exact (keyXY hXi hY0).elim
    · exact iff_of_true hXi hYi

/-- **Isomorphism step of linkage invariance.** A central idempotent acts as the identity on `X`
iff it does on any isomorphic module `Y`, by transporting the action along the `R`-linear
isomorphism. -/
theorem actsAsId_iff_of_iso (e : CentralIdempotent R) {X Y : ModuleCat.{v} R} (iso : X ≅ Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  set φ := iso.toLinearEquiv with hφ
  refine ⟨fun hX n => ?_, fun hY m => ?_⟩
  · have h1 : φ (e.1 • φ.symm n) = e.1 • n := by rw [map_smul, φ.apply_symm_apply]
    rw [← h1, hX (φ.symm n), φ.apply_symm_apply]
  · have h1 : φ.symm (e.1 • φ m) = e.1 • m := by rw [map_smul, φ.symm_apply_apply]
    rw [← h1, hY (φ m), φ.symm_apply_apply]

/-- **Single linkage step of central-character invariance.** For a base `ExtOrIsoSimple` step
(both endpoints simple, related by `Ext¹`-adjacency or isomorphism), a central idempotent acts as
the identity on one endpoint iff on the other. -/
theorem actsAsId_iff_of_extOrIsoSimple [Small.{v} R] (e : CentralIdempotent R)
    {X Y : ModuleCat.{v} R} (h : Etingof.ExtOrIsoSimple R X Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  obtain ⟨hX, hY, hor⟩ := h
  rcases hor with hadj | hiso
  · rcases hadj with h1 | h1
    · exact actsAsId_iff_of_directlyExtLinked R e hX hY h1
    · exact (actsAsId_iff_of_directlyExtLinked R e hY hX h1).symm
  · exact actsAsId_iff_of_iso R e hiso.some

/-- **Central-character invariance along linkage (predicate form).** If `X` and `Y` are linked,
a central idempotent acts as the identity on `X` iff on `Y`. This closes the base
`ExtOrIsoSimple` step under the equivalence-relation generators (reflexivity, symmetry,
transitivity). -/
theorem actsAsId_iff_of_areLinked [Small.{v} R] (e : CentralIdempotent R)
    {X Y : ModuleCat.{v} R} (h : Etingof.AreLinked R X Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  induction h with
  | rel X Y hxy => exact actsAsId_iff_of_extOrIsoSimple R e hxy
  | refl X => exact Iff.rfl
  | symm X Y _ ih => exact ih.symm
  | trans X Y Z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Linkage invariance of the central character (Problem 9.5.3(i), well-definedness engine).**
Linked simple modules have the same central character at every central idempotent. This is what
makes the assignment `block ↦ {central idempotents acting as 1}` well defined on linkage classes,
the `Block R → central idempotents` direction of the bijection. -/
theorem centralCharacter_eq_of_areLinked [Small.{v} R]
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    (e : CentralIdempotent R) (h : Etingof.AreLinked R S T) :
    centralCharacter R hS e = centralCharacter R hT e := by
  classical
  unfold centralCharacter
  rw [decide_eq_decide]
  exact actsAsId_iff_of_areLinked R e h

/-- **The central-character index of a simple module.** Given a *complete orthogonal family* of
central idempotents `e : ι → R` (summing to `1`, pairwise orthogonal, each central and idempotent),
exactly one member `e i` acts as the identity on a given simple module `S`. All others act as `0`
(`centralIdempotent_smul_simple`); at least one is the identity because otherwise `S` would be
killed by `∑ e i = 1`, and at most one because two would multiply to `0` on a nonzero vector.

This is the assignment `simple ↦ its block's idempotent` at the level of the family index, the
engine of the `Block R → central idempotents` direction of Problem 9.5.3(i). -/
theorem existsUnique_actsAsOne_of_completeOrthogonal
    {ι : Type*} [Fintype ι] (e : ι → R)
    (hsum : ∑ i, e i = 1) (hortho : ∀ i j, i ≠ j → e i * e j = 0)
    (hidem : ∀ i, IsIdempotentElem (e i)) (hcentral : ∀ i (y : R), e i * y = y * e i)
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    ∃! i, ∀ m : (S : Type v), e i • m = m := by
  classical
  haveI := hS
  haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
  -- Each `e i` acts on `S` either as `0` or as the identity (Schur).
  have hdicho : ∀ i, (∀ m : (S : Type v), e i • m = 0) ∨ (∀ m : (S : Type v), e i • m = m) :=
    fun i => centralIdempotent_smul_simple R (hidem i) (hcentral i)
  obtain ⟨x, hx⟩ := exists_ne (0 : (S : Type v))
  -- `x = 1 • x = (∑ e i) • x = ∑ (e i • x)`.
  have hxsum : ∑ i, (e i • x) = x := by rw [← Finset.sum_smul, hsum, one_smul]
  -- Existence: if every `e i` acted as `0`, then `x = ∑ 0 = 0`, contradiction.
  have hex : ∃ i, ∀ m : (S : Type v), e i • m = m := by
    by_contra hcon
    exact hx (by
      rw [← hxsum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      exact (hdicho i).resolve_right (fun h => hcon ⟨i, h⟩) x)
  obtain ⟨i₀, hi₀⟩ := hex
  refine ⟨i₀, hi₀, fun j hj => ?_⟩
  -- Uniqueness: if `e j` also acts as the identity and `j ≠ i₀`, then `0 = (e j * e i₀) • x = x`.
  by_contra hne
  apply hx
  have h1 : (e j * e i₀) • x = x := by rw [mul_smul, hi₀ x, hj x]
  rw [hortho j i₀ hne, zero_smul] at h1
  exact h1.symm

/-- **A central idempotent acting as the identity descends to composition factors.** If a central
element `f` acts as the identity on every vector of a module `M`, it acts as the identity on any
composition factor `S` of `M` (a simple subquotient): `S` is a simple quotient `g : Q ↠ S` of a
submodule `Q ≤ M`, and `f • g q = g (f • q) = g q`. -/
theorem actsAsOne_of_isCompositionFactor {M S : ModuleCat.{v} R} {f : R}
    (hM : ∀ m : (M : Type v), f • m = m) (h : Etingof.IsCompositionFactor R M S) :
    ∀ s : (S : Type v), f • s = s := by
  rw [Etingof.isCompositionFactor_iff] at h
  obtain ⟨_, Q, g, hg⟩ := h
  intro s
  obtain ⟨q, rfl⟩ := hg s
  rw [← map_smul]
  congr 1
  exact Subtype.ext (by rw [SetLike.val_smul]; exact hM q.val)

/-- **Every indecomposable central idempotent acts as the identity on some simple module.** For a
nonzero central idempotent `f`, the cyclic module `R · f` (realised inside `Shrink.{v} R`) is
nonzero and `f` acts as the identity on it; any composition factor of it is a simple module on
which `f` acts as the identity. This provides the simple module needed for the
`central idempotents → Block R` direction of Problem 9.5.3(i). -/
theorem exists_simple_actsAsOne [Small.{v} R] {f : R} (hf0 : f ≠ 0)
    (hidem : IsIdempotentElem f) (hcentral : ∀ y : R, f * y = y * f) :
    ∃ S : ModuleCat.{v} R, IsSimpleModule R S ∧ ∀ m : (S : Type v), f • m = m := by
  classical
  set sh := Shrink.linearEquiv.{v} R R with hsh
  set w₀ : Shrink.{v} R := sh.symm f with hw₀
  -- `f` fixes the generator `w₀ = sh.symm f`.
  have hfw : f • w₀ = w₀ := by
    have hmap : f • w₀ = sh.symm (f • f) := (map_smul sh.symm f f).symm
    rw [hmap, smul_eq_mul, hidem.eq]
  -- The cyclic submodule `P = R · w₀`; `f` fixes all of it.
  set P : Submodule R (Shrink.{v} R) := LinearMap.range (LinearMap.toSpanSingleton R _ w₀) with hP
  have hfP : ∀ p ∈ P, f • p = p := by
    rintro p ⟨r, rfl⟩
    rw [LinearMap.toSpanSingleton_apply, ← mul_smul, hcentral r, mul_smul, hfw]
  -- `P` is nonzero: `w₀ ∈ P` and `w₀ ≠ 0`.
  have hw₀ne : w₀ ≠ 0 := by rw [hw₀, Ne, map_eq_zero_iff _ sh.symm.injective]; exact hf0
  have hw₀P : w₀ ∈ P := ⟨1, by rw [LinearMap.toSpanSingleton_apply, one_smul]⟩
  haveI hntP : Nontrivial (P : Type v) :=
    ⟨⟨w₀, hw₀P⟩, 0, fun h => hw₀ne (congrArg Subtype.val h)⟩
  -- A composition factor of `P` is the required simple module.
  obtain ⟨S, hSfac⟩ := Etingof.exists_isCompositionFactor (M := ModuleCat.of R (P : Type v))
  refine ⟨S, hSfac.1, actsAsOne_of_isCompositionFactor R (M := ModuleCat.of R (P : Type v)) ?_ hSfac⟩
  intro m
  exact Subtype.ext (by rw [SetLike.val_smul]; exact hfP m.val m.property)

/-- **Block connectivity from indecomposability (injectivity step of Problem 9.5.3(i)).** If an
*indecomposable* central idempotent `f` acts as the identity on two simple modules `S` and `T` of
a ring `R` of finite length (`IsFiniteLength R R`), then `S` and `T` are linked.

This is the direction of the block ↔ idempotent bijection that fails for a decomposable `f` (e.g.
`f = 1` acts as the identity on every simple, but simples in different blocks are unlinked): it is
precisely the indecomposability of `f` that forces the simples of `R` into a single linkage class.

The finite-length hypothesis is required: over `R = ℤ` the unit `1` is an indecomposable
central idempotent acting as the identity on every simple `ℤ/p`, yet `ℤ/p` and `ℤ/q` are unlinked
for `p ≠ q`. (This mirrors the finiteness needed for the full bijection below.)

The proof decomposes the regular module `Shrink R` along the linkage-class partition (linked to `S`
versus not) of its composition factors, using the finite-length dévissage
(`exists_isCompl_split`). Right multiplications are `R`-linear endomorphisms of `Shrink R`, and the
linked/unlinked summands are stable under every `R`-linear endomorphism, hence are two-sided
ideals. The projection onto the linked summand, being left-`R`-linear, is right multiplication by a
central idempotent `c` (centrality comes from commuting with right multiplication); then
`f = f·c + f·(1 - c)` splits `f` into two orthogonal central idempotents, both nonzero because
`f·c` acts as the identity on `S` and `f·(1 - c)` on `T`, contradicting indecomposability unless
`S` and `T` are linked. -/
theorem areLinked_of_actsAsOne_common [Small.{v} R] {f : R}
    (hfl : IsFiniteLength R R)
    (hindec : IsIndecomposableCentralIdempotent R f)
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    (hSf : ∀ m : (S : Type v), f • m = m) (hTf : ∀ m : (T : Type v), f • m = m) :
    Etingof.AreLinked R S T := by
  classical
  haveI := hS; haveI := hT
  set sh := Shrink.linearEquiv.{v} R R with hsh
  have hflS : IsFiniteLength R (Shrink.{v} R) := sh.symm.isFiniteLength hfl
  -- Decompose the regular module along the linkage-class partition (linked to `S` vs not).
  obtain ⟨P₀, Q₀, hCompl, hgood, hbad⟩ :=
    Etingof.exists_isCompl_split (R := R) (S := S) hflS
  -- A composition factor of `N.map T` is a composition factor of `N` (surjective image).
  have hmapfac : ∀ (T : Shrink.{v} R →ₗ[R] Shrink.{v} R) (N : Submodule R (Shrink.{v} R))
      (U : ModuleCat.{v} R), Etingof.IsCompositionFactor R (ModuleCat.of R (N.map T)) U →
      Etingof.IsCompositionFactor R (ModuleCat.of R N) U := by
    intro T N U h
    refine Etingof.IsCompositionFactor.of_surjective
      ((T.comp N.subtype).codRestrict (N.map T) (fun x => Submodule.mem_map_of_mem x.2)) ?_ h
    rintro ⟨y, hy⟩
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext (by simp [LinearMap.codRestrict])⟩
  -- Any submodule whose factors are all linked to `S` sits inside `P₀`.
  have keyP : ∀ N : Submodule R (Shrink.{v} R),
      (∀ U : ModuleCat.{v} R, Etingof.IsCompositionFactor R (ModuleCat.of R N) U →
        Etingof.AreLinked R S U) → N ≤ P₀ := by
    intro N hN
    have hbot : N.map (Q₀.projection P₀ hCompl.symm) = ⊥ := by
      by_contra hne
      haveI : Nontrivial (N.map (Q₀.projection P₀ hCompl.symm) : Type v) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      obtain ⟨U, hU⟩ := Etingof.exists_isCompositionFactor
        (M := ModuleCat.of R (N.map (Q₀.projection P₀ hCompl.symm) : Type v))
      have hUN : Etingof.IsCompositionFactor R (ModuleCat.of R N) U :=
        hmapfac (Q₀.projection P₀ hCompl.symm) N U hU
      have hle : N.map (Q₀.projection P₀ hCompl.symm) ≤ Q₀ := by
        have h1 : N.map (Q₀.projection P₀ hCompl.symm) ≤
            (⊤ : Submodule R (Shrink.{v} R)).map (Q₀.projection P₀ hCompl.symm) :=
          Submodule.map_mono le_top
        rwa [Submodule.map_top, Submodule.range_projection] at h1
      have hUQ : Etingof.IsCompositionFactor R (ModuleCat.of R Q₀) U :=
        Etingof.IsCompositionFactor.of_submodule
          (Submodule.comap Q₀.subtype (N.map (Q₀.projection P₀ hCompl.symm)))
          (Etingof.IsCompositionFactor.of_linearEquiv (Submodule.comapSubtypeEquivOfLe hle) hU)
      exact hbad U hUQ (hN U hUN)
    intro n hn
    have hmem : (Q₀.projection P₀ hCompl.symm) n ∈ N.map (Q₀.projection P₀ hCompl.symm) :=
      Submodule.mem_map_of_mem hn
    rw [hbot] at hmem
    exact (Submodule.projection_apply_eq_zero_iff hCompl.symm).mp ((Submodule.mem_bot R).mp hmem)
  -- Any submodule whose factors are all unlinked to `S` sits inside `Q₀`.
  have keyQ : ∀ N : Submodule R (Shrink.{v} R),
      (∀ V : ModuleCat.{v} R, Etingof.IsCompositionFactor R (ModuleCat.of R N) V →
        ¬ Etingof.AreLinked R S V) → N ≤ Q₀ := by
    intro N hN
    have hbot : N.map (P₀.projection Q₀ hCompl) = ⊥ := by
      by_contra hne
      haveI : Nontrivial (N.map (P₀.projection Q₀ hCompl) : Type v) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      obtain ⟨V, hV⟩ := Etingof.exists_isCompositionFactor
        (M := ModuleCat.of R (N.map (P₀.projection Q₀ hCompl) : Type v))
      have hVN : Etingof.IsCompositionFactor R (ModuleCat.of R N) V :=
        hmapfac (P₀.projection Q₀ hCompl) N V hV
      have hle : N.map (P₀.projection Q₀ hCompl) ≤ P₀ := by
        have h1 : N.map (P₀.projection Q₀ hCompl) ≤
            (⊤ : Submodule R (Shrink.{v} R)).map (P₀.projection Q₀ hCompl) :=
          Submodule.map_mono le_top
        rwa [Submodule.map_top, Submodule.range_projection] at h1
      have hVP : Etingof.IsCompositionFactor R (ModuleCat.of R P₀) V :=
        Etingof.IsCompositionFactor.of_submodule
          (Submodule.comap P₀.subtype (N.map (P₀.projection Q₀ hCompl)))
          (Etingof.IsCompositionFactor.of_linearEquiv (Submodule.comapSubtypeEquivOfLe hle) hV)
      exact hN V hVN (hgood V hVP)
    intro n hn
    have hmem : (P₀.projection Q₀ hCompl) n ∈ N.map (P₀.projection Q₀ hCompl) :=
      Submodule.mem_map_of_mem hn
    rw [hbot] at hmem
    exact (Submodule.projection_apply_eq_zero_iff hCompl).mp ((Submodule.mem_bot R).mp hmem)
  -- Right multiplication by `a`, transported to an `R`-linear endomorphism of `Shrink R`.
  set Ta : R → (Shrink.{v} R →ₗ[R] Shrink.{v} R) :=
    fun a => sh.symm.toLinearMap.comp ((LinearMap.mulRight R a).comp sh.toLinearMap) with hTa_def
  have hTa : ∀ (a : R) (w : Shrink.{v} R), Ta a w = sh.symm (sh w * a) := by
    intro a w
    simp only [hTa_def, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulRight_apply]
  -- The linked/unlinked summands are stable under every `Ta a`.
  have hstabP : ∀ (a : R) {z : Shrink.{v} R}, z ∈ P₀ → (Ta a) z ∈ P₀ := by
    intro a z hz
    exact keyP (P₀.map (Ta a)) (fun U hU => hgood U (hmapfac (Ta a) P₀ U hU))
      (Submodule.mem_map_of_mem hz)
  have hstabQ : ∀ (a : R) {z : Shrink.{v} R}, z ∈ Q₀ → (Ta a) z ∈ Q₀ := by
    intro a z hz
    exact keyQ (Q₀.map (Ta a)) (fun U hU => hbad U (hmapfac (Ta a) Q₀ U hU))
      (Submodule.mem_map_of_mem hz)
  -- The projection onto `P₀` commutes with each `Ta a`.
  have hcomm_endo : ∀ (a : R) (z : Shrink.{v} R),
      (P₀.projection Q₀ hCompl) ((Ta a) z) = (Ta a) ((P₀.projection Q₀ hCompl) z) := by
    intro a z
    have hzp : (P₀.projection Q₀ hCompl) z ∈ P₀ := Submodule.projection_apply_mem hCompl z
    have hzq : z - (P₀.projection Q₀ hCompl) z ∈ Q₀ := Submodule.sub_projection_mem hCompl z
    have hsplit : (Ta a) z = (Ta a) ((P₀.projection Q₀ hCompl) z)
        + (Ta a) (z - (P₀.projection Q₀ hCompl) z) := by
      rw [← map_add]; congr 1; abel
    rw [hsplit, map_add,
      (Submodule.projection_eq_self_iff hCompl _).mpr (hstabP a hzp),
      (Submodule.projection_apply_eq_zero_iff hCompl).mpr (hstabQ a hzq), add_zero]
  -- `c` is the central idempotent obtained by projecting the identity.
  set c : R := sh (P₀.projection Q₀ hCompl (sh.symm 1)) with hc
  -- The transported projection is right multiplication by `c`.
  have hPiR : ∀ r : R, sh (P₀.projection Q₀ hCompl (sh.symm r)) = r * c := by
    intro r
    have hr : sh.symm r = r • sh.symm (1 : R) := by
      rw [← map_smul]; congr 1; rw [smul_eq_mul, mul_one]
    rw [hr, map_smul, map_smul, smul_eq_mul, ← hc]
  have hProjIdem : ∀ y, (P₀.projection Q₀ hCompl) ((P₀.projection Q₀ hCompl) y)
      = (P₀.projection Q₀ hCompl) y :=
    fun y => (Submodule.projection_eq_self_iff hCompl _).mpr
      (Submodule.projection_apply_mem hCompl y)
  have hidem_c : c * c = c := by
    have h := hPiR c
    rw [show sh.symm c = (P₀.projection Q₀ hCompl) (sh.symm 1) by rw [hc, sh.symm_apply_apply],
      hProjIdem, ← hc] at h
    exact h.symm
  -- The transported projection commutes with right multiplication.
  have hcomm : ∀ x a : R, sh (P₀.projection Q₀ hCompl (sh.symm (x * a)))
      = sh (P₀.projection Q₀ hCompl (sh.symm x)) * a := by
    intro x a
    have h1 : sh.symm (x * a) = (Ta a) (sh.symm x) := by rw [hTa, sh.apply_symm_apply]
    rw [h1, hcomm_endo a (sh.symm x), hTa, sh.apply_symm_apply]
  have hcentral_c : ∀ a : R, a * c = c * a := by
    intro a
    have h := hcomm 1 a
    rw [one_mul, ← hc, hPiR a] at h
    exact h
  have hc_comm : ∀ y : R, c * y = y * c := fun y => (hcentral_c y).symm
  -- The complementary central idempotent `c' = 1 - c`.
  set c' : R := 1 - c with hc'
  have hidem_c' : c' * c' = c' := by
    rw [hc']
    have expand : (1 - c) * (1 - c) = 1 - c - c + c * c := by
      rw [sub_mul, one_mul, mul_sub, mul_one]; abel
    rw [expand, hidem_c]; abel
  have hcc' : c * c' = 0 := by
    rw [hc']
    have : c * (1 - c) = c - c * c := by rw [mul_sub, mul_one]
    rw [this, hidem_c, sub_self]
  have hc'_comm : ∀ y : R, c' * y = y * c' := by
    intro y
    rw [hc']
    have e1 : (1 - c) * y = y - c * y := by rw [sub_mul, one_mul]
    have e2 : y * (1 - c) = y - y * c := by rw [mul_sub, mul_one]
    rw [e1, e2, hc_comm y]
  -- `c` acts as the identity on the linked summand `P₀`, hence on any factor of `P₀`.
  have hcP₀ : ∀ m : (ModuleCat.of R (P₀ : Type v) : Type v), c • m = m := by
    intro m
    apply Subtype.ext
    change c • (m : Shrink.{v} R) = (m : Shrink.{v} R)
    apply sh.injective
    rw [map_smul, smul_eq_mul]
    have hfix : sh (m : Shrink.{v} R) = sh (m : Shrink.{v} R) * c := by
      have h := hPiR (sh (m : Shrink.{v} R))
      rwa [sh.symm_apply_apply, (Submodule.projection_eq_self_iff hCompl _).mpr m.2] at h
    rw [hc_comm (sh (m : Shrink.{v} R))]
    exact hfix.symm
  -- `c'` acts as the identity on the unlinked summand `Q₀`, hence on any factor of `Q₀`.
  have hc'Q : ∀ m : (ModuleCat.of R (Q₀ : Type v) : Type v), c' • m = m := by
    intro m
    apply Subtype.ext
    change c' • (m : Shrink.{v} R) = (m : Shrink.{v} R)
    have hkill : c • (m : Shrink.{v} R) = 0 := by
      apply sh.injective
      rw [map_smul, smul_eq_mul, map_zero]
      have h := hPiR (sh (m : Shrink.{v} R))
      rw [sh.symm_apply_apply, (Submodule.projection_apply_eq_zero_iff hCompl).mpr m.2,
        map_zero] at h
      rw [hc_comm (sh (m : Shrink.{v} R))]
      exact h.symm
    rw [hc', sub_smul, one_smul, hkill, sub_zero]
  -- Every simple module is a composition factor of the regular module `Shrink R`.
  have factorX : ∀ (U : ModuleCat.{v} R), IsSimpleModule R U →
      Etingof.IsCompositionFactor R (ModuleCat.of R (Shrink.{v} R)) U := by
    intro U hU
    haveI := hU
    haveI : Nontrivial (U : Type v) := IsSimpleModule.nontrivial R (U : Type v)
    obtain ⟨u₀, hu₀⟩ := exists_ne (0 : (U : Type v))
    have hspan : Submodule.span R {u₀} = ⊤ := (hU.eq_bot_or_eq_top _).resolve_left (fun h => by
      have : u₀ ∈ (⊥ : Submodule R (U : Type v)) := h ▸ Submodule.mem_span_singleton_self u₀
      exact hu₀ ((Submodule.mem_bot R).mp this))
    refine Etingof.isCompositionFactor_iff.mpr ⟨hU, ⊤,
      (LinearMap.toSpanSingleton R (U : Type v) u₀).comp
        (sh.toLinearMap.comp (⊤ : Submodule R (Shrink.{v} R)).subtype), ?_⟩
    intro y
    have hy : y ∈ Submodule.span R {u₀} := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨⟨sh.symm r, Submodule.mem_top⟩, by simp [LinearMap.toSpanSingleton_apply]⟩
  -- `S` is a factor of `Shrink R`, and is linked to itself, so it is a factor of `P₀`.
  have hcS : ∀ s : (S : Type v), c • s = s := by
    have hSsplit : Etingof.IsCompositionFactor R (ModuleCat.of R P₀) S := by
      rcases Etingof.IsCompositionFactor.of_submodule_or_quotient P₀ (factorX S hS) with h | h
      · exact h
      · exact absurd ((Etingof.areLinked_equivalence R).refl S) (hbad S
          (Etingof.IsCompositionFactor.of_linearEquiv
            (Submodule.quotientEquivOfIsCompl P₀ Q₀ hCompl).symm h))
    exact actsAsOne_of_isCompositionFactor R hcP₀ hSsplit
  -- `T` is a factor of `Shrink R`; either it is linked to `S` (done), or a factor of `Q₀`.
  rcases Etingof.IsCompositionFactor.of_submodule_or_quotient P₀ (factorX T hT) with hTP | hTQ'
  · exact hgood T hTP
  · -- `T` is a factor of `Q₀`; build the splitting `f = f·c + f·c'` and
    -- contradict indecomposability.
    exfalso
    have hTQ : Etingof.IsCompositionFactor R (ModuleCat.of R Q₀) T :=
      Etingof.IsCompositionFactor.of_linearEquiv
        (Submodule.quotientEquivOfIsCompl P₀ Q₀ hCompl).symm hTQ'
    have hc'T : ∀ t : (T : Type v), c' • t = t := actsAsOne_of_isCompositionFactor R hc'Q hTQ
    have hf_idem : IsIdempotentElem f := hindec.2.1
    have hf_central : ∀ y, f * y = y * f := hindec.2.2.1
    -- `f·c` and `f·c'` are orthogonal central idempotents summing to `f`.
    have g1idem : (f * c) * (f * c) = f * c := by
      rw [mul_assoc f c (f * c), ← mul_assoc c f c, hc_comm f, mul_assoc f c c, hidem_c,
        ← mul_assoc, hf_idem.eq]
    have g2idem : (f * c') * (f * c') = f * c' := by
      rw [mul_assoc f c' (f * c'), ← mul_assoc c' f c', hc'_comm f, mul_assoc f c' c', hidem_c',
        ← mul_assoc, hf_idem.eq]
    have g12 : (f * c) * (f * c') = 0 := by
      rw [mul_assoc f c (f * c'), ← mul_assoc c f c', hc_comm f, mul_assoc f c c', hcc',
        mul_zero, mul_zero]
    have hfc_comm : ∀ y, (f * c) * y = y * (f * c) := by
      intro y
      rw [mul_assoc, hc_comm y, ← mul_assoc, hf_central y, mul_assoc]
    have hfc'_comm : ∀ y, (f * c') * y = y * (f * c') := by
      intro y
      rw [mul_assoc, hc'_comm y, ← mul_assoc, hf_central y, mul_assoc]
    have hfsum : f = f * c + f * c' := by rw [← mul_add, hc', add_sub_cancel, mul_one]
    -- Nonzero: `f·c` acts as the identity on `S`, `f·c'` on `T`.
    haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
    obtain ⟨s, hs⟩ := exists_ne (0 : (S : Type v))
    have hg1ne : f * c ≠ 0 := fun h0 => hs (by
      have h1 : (f * c) • s = s := by rw [mul_smul, hcS s, hSf s]
      rw [h0, zero_smul] at h1; exact h1.symm)
    haveI : Nontrivial (T : Type v) := IsSimpleModule.nontrivial R (T : Type v)
    obtain ⟨t, ht⟩ := exists_ne (0 : (T : Type v))
    have hg2ne : f * c' ≠ 0 := fun h0 => ht (by
      have h1 : (f * c') • t = t := by rw [mul_smul, hc'T t, hTf t]
      rw [h0, zero_smul] at h1; exact h1.symm)
    exact hindec.2.2.2
      ⟨f * c, f * c', hg1ne, hg2ne, g1idem, g2idem, hfc_comm, hfc'_comm, g12, hfsum⟩

/-- **Problem 9.5.3 (ii), orthogonality.** If `M` lies in the block of the simple module `S`
and `N` lies in the block of the simple module `T`, and `S`, `T` are not linked (i.e. `M`, `N`
are in different blocks), then `Hom(M, N) = 0`. -/
theorem hom_subsingleton_of_not_linked [Small.{v} R]
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    {M N : ModuleCat.{v} R} (hM : Etingof.InBlock R S M) (hN : Etingof.InBlock R T N)
    (hST : ¬ Etingof.AreLinked R S T) :
    Subsingleton (M ⟶ N) := by
  -- It suffices to show every morphism `M ⟶ N` is zero.
  suffices h0 : ∀ f : M ⟶ N, f = 0 by exact ⟨fun f g => by rw [h0 f, h0 g]⟩
  intro f
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  by_contra hfhom
  -- If `f.hom ≠ 0` its range is a nonzero submodule of `N`, hence has a composition factor `U`.
  have hrange : LinearMap.range f.hom ≠ ⊥ := by rwa [Ne, LinearMap.range_eq_bot]
  haveI hnt : Nontrivial (LinearMap.range f.hom) := Submodule.nontrivial_iff_ne_bot.mpr hrange
  obtain ⟨U, hU⟩ :=
    Etingof.exists_isCompositionFactor (M := ModuleCat.of R (LinearMap.range f.hom))
  -- `U` is a composition factor of `N` (range is a submodule of `N`) ...
  have hUN : Etingof.IsCompositionFactor R N U :=
    Etingof.IsCompositionFactor.of_submodule (LinearMap.range f.hom) hU
  -- ... and of `M` (range is a surjective image of `M`).
  have hUM : Etingof.IsCompositionFactor R M U :=
    Etingof.IsCompositionFactor.of_surjective f.hom.rangeRestrict
      (LinearMap.surjective_rangeRestrict _) hU
  -- Both blocks then link `S` and `T`, contradicting `hST`.
  have h1 : Etingof.AreLinked R U S := hM U hUM
  have h2 : Etingof.AreLinked R U T := hN U hUN
  exact hST ((Etingof.areLinked_equivalence R).trans
    ((Etingof.areLinked_equivalence R).symm h1) h2)

/-- **Block-connectivity of an indecomposable module.** The composition factors of an
indecomposable finite-length module all lie in a single linkage class: any two composition
factors `S`, `T` of `M` are linked.

This is the mathematical core of Problem 9.5.3(ii). Proof strategy (book proof, contrapositive):
the composition factors of `M` split into linkage classes; if `S` and `T` were *not* linked,
the factors would occupy `≥ 2` distinct linkage classes. Let `𝒮` be the saturated set of
simples linked to `S` and `𝒮'` its complement (a union of full linkage classes, so no simple
in `𝒮` is linked to any simple in `𝒮'`). The largest submodule `M_𝒮 ≤ M` with all composition
factors in `𝒮` and the analogous `M_{𝒮'}` then give a nontrivial biproduct decomposition
`M ≅ M_𝒮 ⊞ M_{𝒮'}` (both nonzero: `S` forces `M_𝒮 ≠ 0`, `T` forces `M_{𝒮'} ≠ 0`),
contradicting `Indecomposable M`. The decomposition itself is the Ext-splitting mechanism behind
`hom_subsingleton_of_not_linked`: `Ext¹(X, Y) = 0` whenever every composition factor of `X` is
unlinked to every composition factor of `Y` (dévissage from the simple base case
`¬ Etingof.AreLinked R S T ⟹ Subsingleton (Abelian.Ext S T 1)` via the covariant/contravariant
Ext long exact sequences), so each layer of the composition series of `M` splits off along the
`𝒮`/`𝒮'` partition. -/
theorem compositionFactors_areLinked [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M) (hfl : IsFiniteLength R M)
    {S T : ModuleCat.{v} R}
    (hS : Etingof.IsCompositionFactor R M S) (hT : Etingof.IsCompositionFactor R M T) :
    Etingof.AreLinked R S T :=
  Etingof.compositionFactors_areLinked_aux hM hfl hS hT

/-- **Problem 9.5.3 (ii), decomposition.** Every indecomposable finite-length object lies in
some block: there is a simple module `S` such that all composition factors of `M` are linked to
`S`. The finite-length assumption is `IsFiniteLength R M`; the weaker
"`∃ composition factor`" form does not force finite length, and the block
statement is false without it, e.g. `M = ℤ` over `R = ℤ`. -/
theorem exists_block_of_indecomposable [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M) (hfl : IsFiniteLength R M) :
    ∃ S : ModuleCat.{v} R, IsSimpleModule R S ∧ Etingof.InBlock R S M := by
  -- `M` is nonzero (indecomposable), hence its carrier is nontrivial and has a factor `S`.
  haveI hnt : Nontrivial (M : Type v) := by
    rw [← not_subsingleton_iff_nontrivial, ← ModuleCat.isZero_iff_subsingleton]
    exact hM.1
  obtain ⟨S, hS⟩ := Etingof.exists_isCompositionFactor (M := M)
  refine ⟨S, hS.1, ?_⟩
  -- every composition factor `T` of `M` is linked to `S` by block-connectivity.
  intro T hT
  exact (Etingof.areLinked_equivalence R).symm
    (compositionFactors_areLinked R hM hfl hS hT)

end Problem953

end Etingof
