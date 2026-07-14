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

* **(ii)** Every indecomposable object of `𝒞` lies in some block `𝒞ₖ`, and
  `Hom(M, N) = 0` whenever `M ∈ 𝒞ₖ`, `N ∈ 𝒞ₗ` with `k ≠ l`. Thus `𝒞 = ⊕ₖ 𝒞ₖ`.

* **(iii)** Determine the blocks of the category of left `A`-modules for `A = k[S₃]` with `k`
  of characteristic `2`. *(Deferred: this concrete modular-representation computation is left
  to a follow-up statement-pass item.)*

## Statement-pass note

Blocks are `Etingof.Block R` and block membership is `Etingof.InBlock R S M` (Definition
9.5.1). "Indecomposable central idempotent" is the predicate
`Etingof.Problem953.IsIndecomposableCentralIdempotent` (defined in
`Problem9_5_3_PrimitiveIdempotents.lean`, a nonzero central idempotent not expressible as a sum
of two nonzero orthogonal central idempotents).
"`Hom(M, N) = 0`" is `Subsingleton (M ⟶ N)`, and "indecomposable object" is
`CategoryTheory.Indecomposable`. Two blocks are distinct exactly when their representative
simple modules are not `Etingof.AreLinked`. Proofs are deferred (`sorry`).
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
    show e • e • m = e • m
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
post-composing it with `z • 𝟙 Y` — both equal the `z`-scalar multiple `z • α`. This is the
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

/-- **Problem 9.5.3 (i).** For a finite dimensional algebra `R` over a field `k`, there is a
bijection between the blocks of the category of finite dimensional `R`-modules (linkage classes
of simple modules) and the indecomposable central idempotents of `R`.

The finiteness hypothesis is essential and was missing from the original statement of this item.
Over a general ring the two sides differ: for `R = ℤ` the simple modules `ℤ/p` are pairwise
unlinked (`Ext¹_ℤ(ℤ/p, ℤ/q) = 0` for `p ≠ q`), so there is one block per prime — infinitely many
— while the only indecomposable central idempotent of `ℤ` is `1`. A finiteness assumption forcing
a `1 = Σ eₖ` decomposition into primitive central idempotents (here: `FiniteDimensional k R`) is
what makes the two sides match. We keep the ambient ring `R` and simply add that it is a finite
dimensional `k`-algebra, so the block API (`Etingof.Block R`, `IsIndecomposableCentralIdempotent
R`) is unchanged.

The proof (still to be filled) runs through `centralIdempotent_smul_simple`: each simple module
has a central character (which central idempotents act as `1`), linked simples share it, and the
primitive central idempotents `eₖ` in the decomposition `1 = Σ eₖ` are exactly the indicators of
the blocks. -/
theorem blocks_equiv_indecomposableCentralIdempotents
    {k : Type*} [Field k] [Algebra k R] [FiniteDimensional k R] [Small.{v} R] :
    Nonempty (Etingof.Block.{v} R ≃ {e : R // IsIndecomposableCentralIdempotent R e}) := by
  sorry

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
`S`. The finite-length assumption is the genuine `IsFiniteLength R M` (the earlier
"`∃ composition factor`" form was too weak — it does not force finite length, and the block
statement is false without it, e.g. `M = ℤ` over `R = ℤ`). -/
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
