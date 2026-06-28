import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import EtingofRepresentationTheory.Chapter3.Proposition3_1_4

/-!
# Remark 3.1.5: Generalization of Proposition 3.1.4 over a non-closed base

The remark observes that in Proposition 3.1.4 it does not matter that `k` is algebraically
closed, nor that `V` is finite dimensional. When these assumptions are dropped, the only
change is that the entries of the matrix `Xᵢ` describing the inclusion are no longer scalars
in `k` but live in the division algebra `Dᵢ = End_A(Vᵢ)`.

Two facts make up the genuinely new content of this remark, beyond the classification of
subrepresentations itself:

* **The classification already generalizes.** The Lean statement of Proposition 3.1.4,
  `Etingof.subrepresentation_of_semisimple`, is proved for an arbitrary ring `A` and
  arbitrary simple modules `V i` — no algebraic closure, no finite dimensionality. We
  re-export it here under `Etingof.Remark315.subrepresentation_general` to record that the
  generalization the remark asserts is exactly the theorem we already have.

* **The matrix entries live in `Dᵢ = End_A(Vᵢ)`.** A homomorphism between copies of a
  simple module `V` is given by a matrix over `D = End_A(V)`: we build the explicit
  additive equivalence
  `((Fin r → V) →ₗ[A] (Fin n → V)) ≃+ Matrix (Fin r) (Fin n) (Module.End A V)`
  sending `f` to the matrix `X` with `(f v) j = ∑ i, X i j (v i)` (the book's
  "row vector times matrix" convention). By Schur's lemma `D = End_A(V)` is a division
  ring, recorded as `Module.End.instDivisionRing`.

The "linearly independent rows" condition of the matrix `Xᵢ` is precisely injectivity of
the inclusion. We make this explicit: `f` is injective iff its rows are right
`D`-linearly independent, where a right `D`-linear relation among the rows with
coefficients `c : Fin r → End A V` is `∀ j, ∑ i, (X i j) * c i = 0`.
-/

open scoped DirectSum

namespace Etingof.Remark315

section General

variable {A : Type*} [Ring A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, IsSimpleModule A (V i)]

/-- **Remark 3.1.5**, generalization clause. Proposition 3.1.4 holds over an arbitrary ring
`A` with arbitrary simple modules `V i`: no hypothesis that the base is algebraically closed,
and no finite-dimensionality of the `V i`. Any subrepresentation `W` of `⊕ᵢ nᵢ Vᵢ` is
isomorphic to `⊕ᵢ rᵢ Vᵢ` with `r i ≤ n i`. This is exactly
`Etingof.subrepresentation_of_semisimple`. -/
theorem subrepresentation_general (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (⨁ i, (Fin (n i) → V i))) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (↥W ≃ₗ[A] ⨁ i, (Fin (r i) → V i)) :=
  Etingof.subrepresentation_of_semisimple n hd W

end General

section Matrix

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V]

/-- A homomorphism between copies of a module `V` is given by a matrix of endomorphisms of
`V`: the additive equivalence sending an `A`-linear map `f : (Fin r → V) → (Fin n → V)` to
the matrix `X` with `(f v) j = ∑ i, X i j (v i)`. This is the rectangular generalization of
`endVecRingEquivMatrixEnd`. When `V` is simple, the entries lie in the division algebra
`D = End_A(V)` (Schur's lemma), which is the content of Remark 3.1.5. -/
def homMatrixEquiv (r n : ℕ) :
    ((Fin r → V) →ₗ[A] (Fin n → V)) ≃+ Matrix (Fin r) (Fin n) (Module.End A V) where
  toFun f i j :=
    { toFun := fun x => f (Pi.single i x) j
      map_add' := fun x y => by simp [Pi.single_add]
      map_smul' := fun a x => by simp [Pi.single_smul] }
  invFun X :=
    { toFun := fun v j => ∑ i, X i j (v i)
      map_add' := fun v w => by ext j; simp [Finset.sum_add_distrib]
      map_smul' := fun a v => by ext j; simp [Finset.smul_sum] }
  left_inv f := by
    refine LinearMap.ext fun v => funext fun j => ?_
    change ∑ i, f (Pi.single i (v i)) j = f v j
    rw [← Fintype.sum_apply j (fun i => f (Pi.single i (v i))), ← map_sum,
      Finset.univ_sum_single]
  right_inv X := by
    ext i j x
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i]
    · simp [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  map_add' f g := by ext i j x; simp

@[simp] theorem homMatrixEquiv_apply (r n : ℕ) (f : (Fin r → V) →ₗ[A] (Fin n → V))
    (i : Fin r) (j : Fin n) (x : V) :
    homMatrixEquiv r n f i j x = f (Pi.single i x) j := rfl

@[simp] theorem homMatrixEquiv_symm_apply (r n : ℕ)
    (X : Matrix (Fin r) (Fin n) (Module.End A V)) (v : Fin r → V) (j : Fin n) :
    (homMatrixEquiv r n).symm X v j = ∑ i, X i j (v i) := rfl

/-- Evaluating any homomorphism `f : (Fin r → V) → (Fin n → V)` is given by its matrix:
`(f w) j = ∑ i, X i j (w i)` where `X = homMatrixEquiv f`. This is the "row vector times
matrix" formula of Proposition 3.1.4 / Remark 3.1.5. -/
theorem apply_eq_sum (r n : ℕ) (f : (Fin r → V) →ₗ[A] (Fin n → V))
    (w : Fin r → V) (j : Fin n) :
    f w j = ∑ i, homMatrixEquiv r n f i j (w i) := by
  conv_lhs => rw [← (homMatrixEquiv r n).symm_apply_apply f]
  rw [homMatrixEquiv_symm_apply]

end Matrix

section Injective

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V] [IsSimpleModule A V]

/-- For copies of a *simple* module `V`, a homomorphism `f : (Fin r → V) → (Fin n → V)` is
injective iff it is left-cancellable on maps out of `V`: `f ∘ g = 0` forces `g = 0`. The
converse uses that `Fin r → V` is semisimple, so a nonzero kernel would contain a copy of
`V`. This is the abstract form of "the rows of the matrix `Xᵢ` are linearly independent". -/
theorem injective_iff_comp_eq_zero (r n : ℕ) (f : (Fin r → V) →ₗ[A] (Fin n → V)) :
    Function.Injective f ↔
      ∀ g : V →ₗ[A] (Fin r → V), f ∘ₗ g = 0 → g = 0 := by
  constructor
  · intro hf g hg
    refine LinearMap.ext fun v => hf ?_
    have := LinearMap.congr_fun hg v
    simpa using this
  · intro H
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    obtain ⟨S, hSle, hSsimple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le (LinearMap.ker f)).resolve_left hne
    haveI := hSsimple
    obtain ⟨e⟩ := Etingof.isIsotypicOfType_fun r S
    set g : V →ₗ[A] (Fin r → V) := S.subtype ∘ₗ (e.symm : V →ₗ[A] ↥S) with hg
    have hfg : f ∘ₗ g = 0 := by
      refine LinearMap.ext fun v => ?_
      have hmem : ((e.symm v : ↥S) : Fin r → V) ∈ LinearMap.ker f := hSle (e.symm v).2
      simpa [hg] using LinearMap.mem_ker.mp hmem
    have hg0 := H g hfg
    have hinj : Function.Injective g :=
      S.subtype_injective.comp (e.symm.injective)
    haveI : Nontrivial V := IsSimpleModule.nontrivial A V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hinj (by rw [hg0]; simp))

/-- **Remark 3.1.5**, matrix form of "linearly independent rows". For copies of a simple
module `V`, the homomorphism `f : (Fin r → V) → (Fin n → V)` is injective iff the rows of its
matrix `X = homMatrixEquiv f` over `D = End_A(V)` are right `D`-linearly independent: the only
coefficients `c : Fin r → End_A(V)` with `∑ i, X i j * c i = 0` for every column `j` are the
zero coefficients. -/
theorem injective_iff_rows_linearIndependent (r n : ℕ)
    (f : (Fin r → V) →ₗ[A] (Fin n → V)) :
    Function.Injective f ↔
      ∀ c : Fin r → Module.End A V,
        (∀ j, ∑ i, homMatrixEquiv r n f i j * c i = 0) → ∀ i, c i = 0 := by
  rw [injective_iff_comp_eq_zero]
  constructor
  · intro H c hc
    have hg : f ∘ₗ LinearMap.pi c = 0 := by
      refine LinearMap.ext fun v => funext fun j => ?_
      have : f (LinearMap.pi c v) j = ∑ i, homMatrixEquiv r n f i j (c i v) := by
        rw [apply_eq_sum]; simp [LinearMap.pi_apply]
      rw [LinearMap.comp_apply, this]
      have h0 := LinearMap.congr_fun (hc j) v
      simpa [LinearMap.sum_apply, Module.End.mul_apply] using h0
    have := H _ hg
    intro i
    have := congrArg (fun g : V →ₗ[A] (Fin r → V) => LinearMap.proj i ∘ₗ g) this
    simpa [LinearMap.proj_pi] using this
  · intro H g hg
    set c : Fin r → Module.End A V := fun i => LinearMap.proj i ∘ₗ g with hc
    have hcsum : ∀ j, ∑ i, homMatrixEquiv r n f i j * c i = 0 := by
      intro j
      refine LinearMap.ext fun v => ?_
      have hfg := LinearMap.congr_fun hg v
      have : (∑ i, homMatrixEquiv r n f i j * c i) v
          = ∑ i, homMatrixEquiv r n f i j (g v i) := by
        simp [LinearMap.sum_apply, Module.End.mul_apply, hc]
      rw [this, ← apply_eq_sum]
      simpa using congrFun hfg j
    have hc0 := H c hcsum
    refine LinearMap.ext fun v => funext fun i => ?_
    have := hc0 i
    have h2 := LinearMap.congr_fun this v
    simpa [hc, LinearMap.proj_apply] using h2

end Injective

section DivisionRing

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V]
  [IsSimpleModule A V]

/-- **Remark 3.1.5**, division algebra clause: by Schur's lemma `D = End_A(V)` is a division
ring. Recorded here from `Module.End.instDivisionRing`; this is "which is, as we know, a
division algebra" in the remark. -/
theorem end_divisionRing : Nonempty (DivisionRing (Module.End A V)) := by
  classical exact ⟨inferInstance⟩

end DivisionRing

end Etingof.Remark315
