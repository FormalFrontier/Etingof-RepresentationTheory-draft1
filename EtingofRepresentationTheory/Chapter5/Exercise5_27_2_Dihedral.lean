import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1
import EtingofRepresentationTheory.Chapter5.DihedralCharacterCombinatorics
import EtingofRepresentationTheory.Chapter5.AbelianFDRep

/-!
# Exercise 5.27.2 (dihedral group): redo Problem 4.12.1(a) using Theorem 5.27.1

**Exercise 5.27.2.** Redo Problems 4.12.1(a), 4.12.2, and 4.12.6 using Theorem 5.27.1.

This file handles the **Problem 4.12.1(a)** part: describe all irreducible complex
representations of the dihedral group `D_N`, the symmetry group of a regular `N`-gon (order
`2N`), distinguishing the cases of odd and even `N`.

## The dihedral group as a semidirect product

`D_N = ⟨r, s | rᴺ = s² = 1, s r s⁻¹ = r⁻¹⟩` is the semidirect product of the cyclic rotation
group `A = ⟨r⟩ ≅ ℤ/N` (abelian, normal) by the order-two reflection group `G = ⟨s⟩ ≅ ℤ/2`,
where `s` acts on `A` by inversion `r ↦ r⁻¹`. So `Theorem 5.27.1` (the orbit method for
`A ⋊ G` with `A` abelian) applies with `A = Multiplicative (ZMod N)`, `G = Multiplicative
(ZMod 2)`, and `φ` sending the reflection to the inversion automorphism.

We state the classification for Mathlib's `DihedralGroup N` (the concrete group of `N`-gon
symmetries); the docstrings record how Theorem 5.27.1 produces it. The dual `G`-action on
`Â = A →* ℂˣ ≅ ℤ/N` is again inversion `χ ↦ χ⁻¹`, so the orbits are:

* the fixed characters (`χ = χ⁻¹`), whose stabilizer is all of `G`; each contributes two
  `1`-dimensional irreducibles (one per character of `G ≅ ℤ/2`);
* the free orbit-pairs `{χ, χ⁻¹}` with `χ ≠ χ⁻¹`, whose stabilizer is trivial; each
  contributes one `2`-dimensional irreducible `V(χ, U)` of dimension `[G : G_χ] = 2`.

The number of fixed characters is `gcd(2, N)`: for `N` odd only `χ = 1` is fixed (one
character, two `1`-dim irreps), and for `N` even both `χ = 1` and the order-two character
are fixed (two characters, four `1`-dim irreps). The remaining `N - gcd(2,N)` nontrivial
characters split into `(N - gcd(2,N))/2` free orbit-pairs, giving that many `2`-dimensional
irreducibles.

## The classification (Problem 4.12.1(a))

* `N` odd: `2` irreducibles of dimension `1` and `(N-1)/2` of dimension `2`
  (`∑ dim² = 2 + 4·(N-1)/2 = 2N`);
* `N` even: `4` irreducibles of dimension `1` and `(N-2)/2` of dimension `2`
  (`∑ dim² = 4 + 4·(N-2)/2 = 2N`).

Statement pass: the classification is stated; the proof is left as `sorry`.
-/

noncomputable section

open CategoryTheory Module

namespace Etingof.Exercise5_27_2

variable (N : ℕ) [NeZero N]

/-! ## The dihedral group as a semidirect product `⟨r⟩ ⋊ ⟨s⟩`

We realize `DihedralGroup N` as `Multiplicative (ZMod N) ⋊[dihedralφ N] Multiplicative (ZMod 2)`,
with the reflection generator acting on the rotation group by inversion `a ↦ a⁻¹`. -/

/-- Inversion `a ↦ a⁻¹` as an automorphism of the abelian rotation group `Multiplicative (ZMod N)`. -/
def invAut : MulAut (Multiplicative (ZMod N)) := MulEquiv.inv (Multiplicative (ZMod N))

omit [NeZero N] in
@[simp] lemma invAut_apply (a : Multiplicative (ZMod N)) : invAut N a = a⁻¹ := rfl

omit [NeZero N] in
lemma invAut_mul_self : invAut N * invAut N = 1 := by
  ext a; simp

/-- The action of the reflection group `Multiplicative (ZMod 2)` on the rotation group
`Multiplicative (ZMod N)`: the nontrivial element acts by inversion `a ↦ a⁻¹`. -/
def dihedralφ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod N)) :=
  MonoidHom.mk' (fun g => if Multiplicative.toAdd g = 0 then 1 else invAut N) <| by
    intro a b
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    simp only [toAdd_mul]
    rcases h2 (Multiplicative.toAdd a) with ha | ha <;>
      rcases h2 (Multiplicative.toAdd b) with hb | hb <;> simp only [ha, hb]
    · simp
    · simp
    · simp
    · exact (invAut_mul_self N).symm

omit [NeZero N] in
@[simp] lemma dihedralφ_one_apply (a : Multiplicative (ZMod N)) :
    (dihedralφ N (1 : Multiplicative (ZMod 2))) a = a := by
  simp only [dihedralφ, MonoidHom.mk'_apply]
  rw [if_pos]; · rfl
  rfl

omit [NeZero N] in
@[simp] lemma dihedralφ_ofAdd_one_apply (a : Multiplicative (ZMod N)) :
    (dihedralφ N (Multiplicative.ofAdd (1 : ZMod 2))) a = a⁻¹ := by
  simp only [dihedralφ, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [if_neg (by decide)]; rfl

/-- The semidirect-product realization of the dihedral group `D_N`. -/
abbrev DihedralSemidirect : Type := Multiplicative (ZMod N) ⋊[dihedralφ N] Multiplicative (ZMod 2)

/-- **Deliverable 1.** The group isomorphism `D_N ≅ ⟨r⟩ ⋊ ⟨s⟩` realizing Mathlib's concrete
`DihedralGroup N` as the semidirect product of the rotation group `Multiplicative (ZMod N)` by
the reflection group `Multiplicative (ZMod 2)` acting by inversion. On generators
`r i ↦ ⟨ofAdd i, 1⟩` and `sr i ↦ ⟨ofAdd (-i), ofAdd 1⟩`. -/
def dihedralEquiv : DihedralGroup N ≃* DihedralSemidirect N where
  toFun x := match x with
    | .r i => ⟨Multiplicative.ofAdd i, 1⟩
    | .sr i => ⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd (1 : ZMod 2)⟩
  invFun p :=
    if Multiplicative.toAdd p.right = 0
    then DihedralGroup.r (Multiplicative.toAdd p.left)
    else DihedralGroup.sr (- Multiplicative.toAdd p.left)
  left_inv x := by
    cases x with
    | r i => simp
    | sr i => simp [(by decide : (1 : ZMod 2) ≠ 0)]
  right_inv p := by
    obtain ⟨a, g⟩ := p
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases h2 (Multiplicative.toAdd g) with hg | hg
    · have : g = 1 := by
        rw [← ofAdd_toAdd g, hg]; rfl
      subst this; simp
    · have : g = Multiplicative.ofAdd (1 : ZMod 2) := by
        rw [← ofAdd_toAdd g, hg]
      subst this
      simp only [toAdd_ofAdd, (by decide : (1 : ZMod 2) ≠ 0), if_false, neg_neg,
        ofAdd_toAdd]
  map_mul' x y := by
    cases x <;> cases y <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;>
      apply SemidirectProduct.ext <;>
      simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, ← ofAdd_neg, ← ofAdd_add,
        sub_eq_add_neg, add_comm, show (1 : ZMod 2) + 1 = 0 from by decide, ofAdd_zero]

/-! ## Transport of representation classifications along a group isomorphism

Restriction of scalars along `dihedralEquiv N` is an equivalence of representation categories
`FDRep ℂ (DihedralSemidirect N) ≌ FDRep ℂ (DihedralGroup N)` (Mathlib's `Action.resEquiv`). We
package the four facts needed to move a classification across it: it preserves simplicity, reflects
isomorphisms (fully faithful), is essentially surjective (an equivalence), and preserves dimension
(the underlying vector space is unchanged). -/

section Transport

open CategoryTheory CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A full, faithful, monomorphism-preserving functor reflects simple objects. -/
private lemma simple_of_functor_obj (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (X : C) [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f _ := by
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) :=
        (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
          (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

/-- An equivalence of categories preserves simple objects. -/
private lemma simple_equivalence_functor (E : C ≌ D) (X : C) [Simple X] :
    Simple (E.functor.obj X) := by
  haveI : Simple ((𝟭 C).obj X) := inferInstanceAs (Simple X)
  haveI : Simple (E.inverse.obj (E.functor.obj X)) := Simple.of_iso (E.unitIso.app X).symm
  exact simple_of_functor_obj E.inverse (E.functor.obj X)

end Transport

/-- Restriction of scalars along `dihedralEquiv N`: the equivalence of representation categories
`FDRep ℂ (⟨r⟩ ⋊ ⟨s⟩) ≌ FDRep ℂ (D_N)`. -/
def dihedralRepEquiv :
    FDRep ℂ (DihedralSemidirect N) ≌ FDRep ℂ (DihedralGroup N) :=
  Action.resEquiv (FGModuleCat ℂ) (dihedralEquiv N)

omit [NeZero N] in
/-- The transport functor keeps the underlying vector space, so it preserves dimension. -/
lemma finrank_dihedralRepEquiv_functor (V : FDRep ℂ (DihedralSemidirect N)) :
    finrank ℂ ((dihedralRepEquiv N).functor.obj V : Type) = finrank ℂ (V : Type) := rfl

open Classical in
/-- **Deliverable 3 (the orbit assembly).** The classification stated on the semidirect-product
model `⟨r⟩ ⋊ ⟨s⟩`, before transporting back to Mathlib's `DihedralGroup N`. This is the pure
orbit-method content of Theorem 5.27.1 applied to the inversion action, together with the
`gcd(2,N)` fixed-character / `(N-gcd(2,N))/2` free-orbit count. -/
theorem semidirect_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (DihedralSemidirect N)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (DihedralSemidirect N), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = 2) ∧
      (Odd N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 2 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 1) / 2) ∧
      (Even N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 4 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 2) / 2) := by
  sorry

open Classical in
/-- **Exercise 5.27.2 for Problem 4.12.1(a).** The complete classification of the irreducible
complex representations of the dihedral group `D_N` (symmetries of a regular `N`-gon, order
`2N`), obtained from Theorem 5.27.1 via the semidirect-product structure `⟨r⟩ ⋊ ⟨s⟩` with `s`
acting by inversion. Every irreducible has dimension `1` or `2`, and the number of each kind
depends on the parity of `N`: for `N` odd there are `2` of dimension `1` and `(N-1)/2` of
dimension `2`; for `N` even there are `4` of dimension `1` and `(N-2)/2` of dimension `2`.
In both cases `∑ dim² = 2N = |D_N|`. -/
theorem dihedral_classification :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (DihedralGroup N)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (DihedralGroup N), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = 2) ∧
      (Odd N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 2 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 1) / 2) ∧
      (Even N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 4 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 2) / 2) := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hDim, hOdd, hEven⟩ := semidirect_classification N
  set E := dihedralRepEquiv N with hE
  refine ⟨n, fun i => E.functor.obj (V i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- simplicity is preserved by the equivalence
    intro i
    haveI := hSimple i
    exact simple_equivalence_functor E (V i)
  · -- fully faithful reflects isomorphisms
    intro i j ⟨h⟩
    exact hInj i j ⟨E.fullyFaithfulFunctor.preimageIso h⟩
  · -- essential surjectivity: pull `S` back, classify, push forward
    intro S hS
    haveI := hS
    haveI : Simple (E.inverse.obj S) := simple_equivalence_functor E.symm S
    obtain ⟨i, ⟨h⟩⟩ := hComplete (E.inverse.obj S) inferInstance
    exact ⟨i, ⟨(E.counitIso.app S).symm ≪≫ E.functor.mapIso h⟩⟩
  · -- dimensions are unchanged
    intro i
    rw [finrank_dihedralRepEquiv_functor]; exact hDim i
  · -- odd-`N` counts: the dimension filters agree pointwise with the pre-transport ones
    intro hpar
    have hfilt : ∀ d : ℕ, (Finset.univ.filter
        (fun i => finrank ℂ (E.functor.obj (V i) : Type) = d)) =
        (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) := by
      intro d; apply Finset.filter_congr; intro i _
      rw [finrank_dihedralRepEquiv_functor]
    rw [hfilt, hfilt]; exact hOdd hpar
  · intro hpar
    have hfilt : ∀ d : ℕ, (Finset.univ.filter
        (fun i => finrank ℂ (E.functor.obj (V i) : Type) = d)) =
        (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) := by
      intro d; apply Finset.filter_congr; intro i _
      rw [finrank_dihedralRepEquiv_functor]
    rw [hfilt, hfilt]; exact hEven hpar

end Etingof.Exercise5_27_2
