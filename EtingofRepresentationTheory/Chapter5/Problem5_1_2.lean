import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1

/-!
# Problem 5.1.2: real endomorphism algebras and real forms

**Problem 5.1.2.** (a) Show that `End_{ℝ[G]} V` is `ℂ` for `V` of complex type, `Mat₂(ℝ)` for `V`
of real type, and `ℍ` for `V` of quaternionic type, which motivates the names above.

(b) Show that `V` is of real type if and only if `V` is the complexification of a representation
`V_ℝ` over the field of real numbers.

## Formalization

Let `V` be an irreducible complex representation of a finite group `G`. Viewing `V` as a **real**
representation (restriction of scalars `ℂ → ℝ`, carried by the `[Module ℝ V] [IsScalarTower ℝ ℂ V]`
hypotheses), the algebra `End_{ℝ[G]} V` of `ℝ`-linear `G`-equivariant endomorphisms is the
**centralizer** in `Module.End ℝ V` of the real operators `{(ρ g).restrictScalars ℝ}`. We call
this `Etingof.realGEndAlgebra ρ`.

* **(a)** For an irreducible `V`:
  - complex type ⟹ `End_{ℝ[G]} V ≃ₐ[ℝ] ℂ`;
  - real type ⟹ `End_{ℝ[G]} V ≃ₐ[ℝ] Mat₂(ℝ) = Matrix (Fin 2) (Fin 2) ℝ`;
  - quaternionic type ⟹ `End_{ℝ[G]} V ≃ₐ[ℝ] ℍ = Quaternion ℝ`.
* **(b)** `V` is of real type iff it admits a **real form**: a `G`-stable `ℝ`-subspace `W ⊆ V`
  whose `ℂ`-span is all of `V` and with `dim_ℝ W = dim_ℂ V` (so the inclusion induces an
  equivariant isomorphism `ℂ ⊗_ℝ W ≅ V`; the `G`-action restricts to a real representation on `W`).

Statement pass: the proofs are left as `sorry`.
-/

namespace Etingof

section Problem512

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
variable [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- `End_{ℝ[G]} V`: the `ℝ`-algebra of `ℝ`-linear `G`-equivariant endomorphisms of `V`, realized
as the centralizer in `Module.End ℝ V` of the real operators `(ρ g).restrictScalars ℝ`. -/
noncomputable def realGEndAlgebra (ρ : Representation ℂ G V) :
    Subalgebra ℝ (Module.End ℝ V) :=
  Subalgebra.centralizer ℝ (Set.range (fun g => LinearMap.restrictScalars ℝ (ρ g)))

/-- The `ℂ`-embedding `ℂ ⊆ End_{ℝ[G]} V` of the book: multiplication by a complex scalar `z`
is an `ℝ`-linear endomorphism of `V` that commutes with every `(ρ g).restrictScalars ℝ`
(because each `ρ g` is `ℂ`-linear), hence lies in the centralizer `realGEndAlgebra ρ`. This
packages that as an `ℝ`-algebra hom `ℂ →ₐ[ℝ] realGEndAlgebra ρ`. Reusable toolkit shared by the
real (#6327) and quaternionic (#6328) cases. -/
noncomputable def complexToRealGEnd (ρ : Representation ℂ G V) :
    ℂ →ₐ[ℝ] realGEndAlgebra ρ :=
  (Algebra.lsmul ℝ ℝ V).codRestrict (realGEndAlgebra ρ) (by
    intro z
    rw [realGEndAlgebra, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply, Algebra.lsmul_apply,
      map_smul])

omit [Fintype G] [Module.Finite ℂ V] in
@[simp]
theorem complexToRealGEnd_coe_apply (ρ : Representation ℂ G V) (z : ℂ) (v : V) :
    (complexToRealGEnd ρ z : Module.End ℝ V) v = z • v := rfl

omit [Fintype G] [Module.Finite ℂ V] in
/-- The `ℂ`-embedding is injective when `V ≠ 0`: if `z • v = 0` for all `v`, choosing a nonzero
`v` forces `z = 0`. -/
theorem complexToRealGEnd_injective (ρ : Representation ℂ G V) [Nontrivial V] :
    Function.Injective (complexToRealGEnd ρ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : (complexToRealGEnd ρ z : Module.End ℝ V) v = 0 := by rw [hz]; rfl
  rw [complexToRealGEnd_coe_apply] at this
  rcases smul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hv

section ConjDecomp

/-- In any ring, if `j² = -1` then `j` commutes with `f - j·f·j` (the "`+`" part). -/
private lemma ring_conj_comm {R : Type*} [Ring R] {j : R} (hj : j * j = -1) (f : R) :
    j * (f - j * f * j) = (f - j * f * j) * j := by
  have h2 : j * (j * f * j) = -(f * j) := by
    rw [← mul_assoc, ← mul_assoc, hj, neg_one_mul, neg_mul]
  have h3 : j * f * j * j = -(j * f) := by rw [mul_assoc, hj, mul_neg_one]
  rw [mul_sub, sub_mul, h2, h3]; abel

/-- In any ring, if `j² = -1` then `j` anticommutes with `f + j·f·j` (the "`-`" part). -/
private lemma ring_conj_anticomm {R : Type*} [Ring R] {j : R} (hj : j * j = -1) (f : R) :
    j * (f + j * f * j) = -((f + j * f * j) * j) := by
  have h2 : j * (j * f * j) = -(f * j) := by
    rw [← mul_assoc, ← mul_assoc, hj, neg_one_mul, neg_mul]
  have h3 : j * f * j * j = -(j * f) := by rw [mul_assoc, hj, mul_neg_one]
  rw [mul_add, add_mul, h2, h3]; abel

variable (ρ : Representation ℂ G V)

/-- The operator `J = ·i` (multiplication by `i`) as an element of `End_{ℝ[G]} V`,
the image of `Complex.I` under the `ℂ`-embedding. It satisfies `J² = -1`. -/
noncomputable def realJ : realGEndAlgebra ρ := complexToRealGEnd ρ Complex.I

/-- `J² = -1`: since `J = complexToRealGEnd i` and `i·i = -1`. -/
theorem realJ_sq : realJ ρ * realJ ρ = -1 := by
  rw [realJ, ← map_mul, Complex.I_mul_I, map_neg, map_one]

variable {ρ}

/-- The `ℂ`-linear part of `f ∈ End_{ℝ[G]} V`: `f₊ = ½(f − J∘f∘J)`. It commutes with `J`. -/
noncomputable def realPlus (f : realGEndAlgebra ρ) : realGEndAlgebra ρ :=
  (2⁻¹ : ℝ) • (f - realJ ρ * f * realJ ρ)

/-- The `ℂ`-antilinear part of `f ∈ End_{ℝ[G]} V`: `f₋ = ½(f + J∘f∘J)`. It anticommutes with `J`. -/
noncomputable def realMinus (f : realGEndAlgebra ρ) : realGEndAlgebra ρ :=
  (2⁻¹ : ℝ) • (f + realJ ρ * f * realJ ρ)

/-- `f = f₊ + f₋`. -/
theorem realPlus_add_realMinus (f : realGEndAlgebra ρ) :
    realPlus f + realMinus f = f := by
  rw [realPlus, realMinus, ← smul_add]
  have : (f - realJ ρ * f * realJ ρ) + (f + realJ ρ * f * realJ ρ) = (2 : ℝ) • f := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

/-- `f₊` commutes with `J` (it is `ℂ`-linear). -/
theorem realJ_mul_realPlus (f : realGEndAlgebra ρ) :
    realJ ρ * realPlus f = realPlus f * realJ ρ := by
  rw [realPlus, mul_smul_comm, smul_mul_assoc, ring_conj_comm (realJ_sq ρ)]

/-- `f₋` anticommutes with `J` (it is `ℂ`-antilinear). -/
theorem realJ_mul_realMinus (f : realGEndAlgebra ρ) :
    realJ ρ * realMinus f = -(realMinus f * realJ ρ) := by
  rw [realMinus, mul_smul_comm, smul_mul_assoc, ring_conj_anticomm (realJ_sq ρ), smul_neg]

end ConjDecomp

omit [Module ℝ V] [IsScalarTower ℝ ℂ V] in
open scoped ComplexConjugate in
/-- **Invariant positive-definite Hermitian form** (shared toolkit). Every finite-dimensional
complex representation `ρ` of a finite group carries a `G`-invariant, positive-definite Hermitian
(sesquilinear, linear in the first slot and conjugate-linear in the second) form: average the
standard coordinate form `h₀(v, w) = ∑ᵢ (b.repr v)ᵢ · conj (b.repr w)ᵢ` over the group.

Reused by the real (#6327) and quaternionic (#6328) cases to build the `j`-operator. -/
theorem exists_invariant_posdef_hermitian (ρ : Representation ℂ G V) :
    ∃ H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ,
      (∀ g v w, H (ρ g v) (ρ g w) = H v w) ∧ (∀ v, v ≠ 0 → 0 < (H v v).re) ∧
      (∀ v w, (starRingEnd ℂ) (H v w) = H w v) := by
  classical
  set b := Module.finBasis ℂ V with hb
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => ∑ g : G, ∑ i, b.repr (ρ g v) i * conj (b.repr (ρ g w) i))
      ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · -- additive in the first slot
    intro v₁ v₂ w
    simp only [map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  · -- ℂ-linear in the first slot
    intro c v w
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      mul_assoc]
  · -- additive in the second slot
    intro v w₁ w₂
    simp only [map_add, Finsupp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · -- conjugate-linear in the second slot
    intro c v w
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => by ring
  · -- G-invariance
    intro h v w
    simp only [LinearMap.mk₂'ₛₗ_apply]
    have hcomp : ∀ (g : G) (x : V), ρ g (ρ h x) = ρ (g * h) x := fun g x => by
      rw [map_mul]; rfl
    simp_rw [hcomp]
    exact Equiv.sum_comp (Equiv.mulRight h)
      (fun g : G => ∑ i, b.repr (ρ g v) i * conj (b.repr (ρ g w) i))
  · -- positive-definiteness
    intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    have hcast : (∑ g : G, ∑ i, (Complex.normSq (b.repr (ρ g v) i) : ℂ))
        = ((∑ g : G, ∑ i, Complex.normSq (b.repr (ρ g v) i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast, Complex.ofReal_re]
    refine Finset.sum_pos' (fun g _ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) ?_
    refine ⟨1, Finset.mem_univ 1, ?_⟩
    simp only [map_one, Module.End.one_apply]
    obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv (b.repr.injective (by ext i; simp [hcon i]))
    exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  · -- conjugate symmetry: `conj (H v w) = H w v`
    intro v w
    simp only [LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

section ComplexTypeProof

open scoped ComplexConjugate

variable {ρ : Representation ℂ G V}

/-- `(r : ℂ) • v = r • v` for a real scalar `r`, using the `ℝ`-`ℂ` scalar tower on `V`. -/
private lemma real_coe_smul (r : ℝ) (v : V) : (r : ℂ) • v = r • v := by
  rw [← IsScalarTower.algebraMap_smul ℂ r v, Complex.coe_algebraMap]

/-- Split a complex scalar action into its real and imaginary `ℝ`-linear parts. -/
private lemma complex_smul_eq_real (c : ℂ) (v : V) :
    c • v = c.re • v + c.im • (Complex.I • v) := by
  rw [← real_coe_smul c.re v, ← real_coe_smul c.im (Complex.I • v), smul_smul, ← add_smul,
    Complex.re_add_im]

/-- A `G`-invariant `ℂ`-subspace of a simple representation is `⊥` or `⊤`. -/
private lemma invSubmodule_eq_bot_or_top
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (W : Submodule ℂ V) (hW : ∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hirr
  rcases eq_bot_or_eq_top (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ) with h | h
  · exact Or.inl congr(Subrepresentation.toSubmodule $h)
  · exact Or.inr congr(Subrepresentation.toSubmodule $h)

/-- Upgrade an `ℝ`-linear endomorphism commuting with `Complex.I •` to a `ℂ`-linear map. -/
private def toCLinear (T : Module.End ℝ V)
    (hI : ∀ v, T (Complex.I • v) = Complex.I • T v) : V →ₗ[ℂ] V where
  toFun := T
  map_add' := T.map_add
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [complex_smul_eq_real c v, map_add, map_smul, map_smul, hI,
      complex_smul_eq_real c (T v)]

/-- Upgrade an `ℝ`-linear endomorphism anticommuting with `Complex.I •`
(`T (i • v) = -(i • T v)`) to a conjugate-linear map. -/
private def toAntilinear (T : Module.End ℝ V)
    (hI : ∀ v, T (Complex.I • v) = -(Complex.I • T v)) : V →ₗ⋆[ℂ] V where
  toFun := T
  map_add' := T.map_add
  map_smul' c v := by
    show T (c • v) = (starRingEnd ℂ) c • T v
    rw [complex_smul_eq_real c v, map_add, map_smul, map_smul, hI,
      complex_smul_eq_real ((starRingEnd ℂ) c) (T v), Complex.conj_re, Complex.conj_im,
      smul_neg, neg_smul]

/-- From a `G`-invariant sesquilinear form `H`, the induced conjugate-linear map
`V →ₗ⋆[ℂ] Module.Dual ℂ V`, `w ↦ (v ↦ H v w)`. Shared toolkit for the real/quaternionic cases. -/
noncomputable def hermToDual (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : V →ₗ⋆[ℂ] Module.Dual ℂ V where
  toFun w :=
    { toFun := fun v => H v w
      map_add' := fun a b => by
        show H (a + b) w = H a w + H b w; simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c v => by
        show H (c • v) w = c • H v w; simp only [map_smul, LinearMap.smul_apply] }
  map_add' w₁ w₂ := by ext v; show H v (w₁ + w₂) = H v w₁ + H v w₂; rw [map_add]
  map_smul' c w := by
    ext v; show H v (c • w) = (starRingEnd ℂ) c • H v w; rw [map_smulₛₗ]

@[simp] theorem hermToDual_apply (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (w v : V) :
    (hermToDual H w) v = H v w := rfl

/-- `hermToDual` of a `G`-invariant form is `G`-equivariant into the dual representation. -/
theorem hermToDual_equivariant (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hinv : ∀ g v w, H (ρ g v) (ρ g w) = H v w) (g : G) (w : V) :
    hermToDual H (ρ g w) = ρ.dual g (hermToDual H w) := by
  ext v
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    hermToDual_apply, hermToDual_apply]
  have hgg : (ρ g) ((ρ g⁻¹) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := hinv g (ρ g⁻¹ v) w
  rwa [hgg] at this

/-- `hermToDual` of a positive-definite form is injective. -/
theorem hermToDual_injective (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hpos : ∀ v, v ≠ 0 → 0 < (H v v).re) :
    Function.Injective (hermToDual H) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra hwne
  have h2 : H w w = 0 := by
    have := DFunLike.congr_fun hw w
    simpa using this
  have hp := hpos w hwne
  rw [h2] at hp
  simp at hp

/-- Schur's lemma (scalar form) via eigenvalues: a `ℂ`-linear `G`-equivariant endomorphism of a
simple representation is a scalar. -/
private lemma schur_scalar
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (φ : V →ₗ[ℂ] V) (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v)) :
    ∃ c : ℂ, ∀ v, φ v = c • v := by
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : G) (v : V), v ∈ Module.End.eigenspace φ c → ρ g v ∈ Module.End.eigenspace φ c := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hφ, hv, map_smul]
  rcases invSubmodule_eq_bot_or_top hirr (Module.End.eigenspace φ c) hinv with hbot | htop
  · exact absurd hbot hc
  · intro v
    have : v ∈ Module.End.eigenspace φ c := htop ▸ Submodule.mem_top
    rwa [Module.End.mem_eigenspace_iff] at this

/-- **The `j`-operator** (shared toolkit for the real and quaternionic cases, #6327/#6328).
Given a `G`-invariant nondegenerate bilinear form `B` on a simple representation `V`, together
with the invariant positive-definite Hermitian form `(·,·)` from `exists_invariant_posdef_hermitian`,
there is a `ℂ`-antilinear `G`-equivariant operator `j : V → V` characterized by `(v, j w) = B v w`,
satisfying `j² = λ • id` for a real scalar `λ`. The sign of `λ` matches the (skew)symmetry sign `s`
of `B` (hypothesis `B w v = s • B v w`): `s · λ > 0`. So for a **symmetric** `B` (`s = 1`, real
type) one gets `λ > 0`, and for a **skew** `B` (`s = -1`, quaternionic type) `λ < 0`. -/
theorem exists_antilinear_j_of_invariant_nondegenerate
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hinvB : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (s : ℝ) (hs : ∀ v w, B w v = s • B v w) :
    ∃ (j : V →ₗ⋆[ℂ] V) (lam : ℝ),
      (∀ g v, j (ρ g v) = ρ g (j v)) ∧
      (∀ v, j (j v) = (lam : ℂ) • v) ∧
      0 < s * lam := by
  classical
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  obtain ⟨H, hHinv, hHpos, hHsym⟩ := exists_invariant_posdef_hermitian ρ
  -- `H v v` is a nonnegative real (conjugate symmetry ⇒ real; positive-definiteness ⇒ positive).
  have hHreal : ∀ v, H v v = ((H v v).re : ℂ) := fun v => (Complex.conj_eq_iff_re.mp (hHsym v v)).symm
  -- `s ≠ 0` (else `B = 0`, contradicting nondegeneracy on the nontrivial space `V`).
  have hs0 : s ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hnd v fun w => by have := hs w v; rw [h, zero_smul] at this; exact this)
  -- `B.flip` is injective (second-slot nondegeneracy, obtained from `hs` + `hnd`).
  have hBdinj : Function.Injective (B.flip) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine hnd w fun w' => ?_
    have h1 : B w' w = 0 := DFunLike.congr_fun hw w'
    have := hs w' w
    rw [h1, smul_zero] at this
    exact this
  -- `hermToDual H` is bijective: injective by positive-definiteness, surjective by an
  -- `ℝ`-dimension count (both `V` and `V*` have real dimension `2 · dim_ℂ V`).
  have hΦinj : Function.Injective (hermToDual H) := hermToDual_injective H hHpos
  have hΦsurj : Function.Surjective (hermToDual H) := by
    let ΦR : V →ₗ[ℝ] Module.Dual ℂ V :=
      { toFun := hermToDual H
        map_add' := (hermToDual H).map_add
        map_smul' := fun r w => by
          simp only [RingHom.id_apply]
          rw [show (r : ℝ) • w = ((r : ℂ)) • w from (real_coe_smul r w).symm, map_smulₛₗ,
            Complex.conj_ofReal, ← IsScalarTower.algebraMap_smul ℂ r (hermToDual H w),
            Complex.coe_algebraMap] }
    have hΦRinj : Function.Injective ΦR := hΦinj
    haveI : FiniteDimensional ℝ V := Module.Finite.trans (R := ℝ) ℂ V
    haveI : FiniteDimensional ℝ (Module.Dual ℂ V) := Module.Finite.trans (R := ℝ) ℂ _
    have hdimR : Module.finrank ℝ V = Module.finrank ℝ (Module.Dual ℂ V) := by
      rw [← Module.finrank_mul_finrank ℝ ℂ V,
        ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ V), Subspace.dual_finrank_eq]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimR).mp hΦRinj
  -- Package `hermToDual H` as a conjugate-linear equivalence and define `j := herm⁻¹ ∘ B.flip`.
  let hermEquiv : V ≃ₗ⋆[ℂ] Module.Dual ℂ V :=
    LinearEquiv.ofBijective (hermToDual H) ⟨hΦinj, hΦsurj⟩
  let j0 : V →ₗ⋆[ℂ] V := (hermEquiv.symm.toLinearMap).comp B.flip
  -- Defining relation: `H v (j0 w) = B v w`.
  have hj0dual : ∀ w, hermToDual H (j0 w) = B.flip w := fun w => by
    show hermToDual H (hermEquiv.symm (B.flip w)) = B.flip w
    have : hermEquiv (hermEquiv.symm (B.flip w)) = B.flip w := hermEquiv.apply_symm_apply _
    simpa only [LinearEquiv.ofBijective_apply, hermEquiv] using this
  have hdefn : ∀ v w, H v (j0 w) = B v w := fun v w => by
    have := DFunLike.congr_fun (hj0dual w) v
    simpa only [hermToDual_apply, LinearMap.flip_apply] using this
  have hj0inj : Function.Injective j0 := by
    have : Function.Injective (⇑j0) := by
      show Function.Injective (⇑hermEquiv.symm ∘ ⇑B.flip)
      exact hermEquiv.symm.injective.comp hBdinj
    exact this
  -- `j0` is `G`-equivariant (uniqueness via injectivity of `hermToDual H`).
  have hj0equiv : ∀ g v, j0 (ρ g v) = ρ g (j0 v) := by
    intro g w
    apply hΦinj
    rw [hj0dual]
    ext v
    rw [hermToDual_apply, LinearMap.flip_apply]
    -- `B v (ρ g w) = H v (ρ g (j0 w))`
    have hBv : B v (ρ g w) = B (ρ g⁻¹ v) w := by
      have hgg : (ρ g) ((ρ g⁻¹) v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have := hinvB g (ρ g⁻¹ v) w
      rwa [hgg] at this
    rw [hBv, ← hdefn, ← hHinv g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  -- `φ := j0 ∘ j0` is `ℂ`-linear equivariant, hence a scalar `c` by Schur.
  let φ : V →ₗ[ℂ] V :=
    { toFun := fun v => j0 (j0 v)
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [map_smulₛₗ, map_smulₛₗ, Complex.conj_conj] }
  have hφequiv : ∀ g v, φ (ρ g v) = ρ g (φ v) := fun g v => by
    show j0 (j0 (ρ g v)) = ρ g (j0 (j0 v))
    rw [hj0equiv, hj0equiv]
  obtain ⟨c, hc⟩ := schur_scalar hirr φ hφequiv
  have hcsq : ∀ v, j0 (j0 v) = c • v := hc
  -- Positivity: pin down `c` as a real number of sign `s`, using one nonzero vector.
  obtain ⟨w0, hw0⟩ := exists_ne (0 : V)
  have hjw0 : j0 w0 ≠ 0 := fun h => hw0 (hj0inj (h.trans (map_zero j0).symm))
  -- `conj c • H v w = B v (j0 w)` and `B v (j0 w) = s • H (j0 w) (j0 v)`.
  have hI : ∀ v w, (starRingEnd ℂ) c * H v w = B v (j0 w) := fun v w => by
    rw [← hdefn v (j0 w), hcsq w, map_smulₛₗ]; rfl
  have hII : ∀ v w, B v (j0 w) = (s : ℂ) * H (j0 w) (j0 v) := fun v w => by
    rw [hs (j0 w) v, hdefn (j0 w) v, Complex.real_smul]
  have hkey : (starRingEnd ℂ) c * ((H w0 w0).re : ℂ)
      = (s : ℂ) * ((H (j0 w0) (j0 w0)).re : ℂ) := by
    rw [← hHreal, ← hHreal, hI w0 w0, hII w0 w0]
  set p1 := (H w0 w0).re with hp1def
  set p2 := (H (j0 w0) (j0 w0)).re with hp2def
  have hp1 : 0 < p1 := hHpos w0 hw0
  have hp2 : 0 < p2 := hHpos (j0 w0) hjw0
  -- From `conj c * p1 = s * p2` deduce `conj c` is the real number `s * p2 / p1`.
  have hconj : (starRingEnd ℂ) c = ((s * p2 / p1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff (by exact_mod_cast hp1.ne')]
    push_cast at hkey ⊢
    linear_combination hkey
  have hcre : c = ((s * p2 / p1 : ℝ) : ℂ) := by
    have := congrArg (starRingEnd ℂ) hconj
    rwa [Complex.conj_conj, Complex.conj_ofReal] at this
  refine ⟨j0, s * p2 / p1, hj0equiv, ?_, ?_⟩
  · intro v; rw [hcsq v, hcre]
  · have hs2 : 0 < s ^ 2 := (sq_nonneg s).lt_of_ne' (pow_ne_zero 2 hs0)
    have hrw : s * (s * p2 / p1) = s ^ 2 * (p2 / p1) := by ring
    rw [hrw]
    exact mul_pos hs2 (div_pos hp2 hp1)

/-- **Normalized `j'`-operator** for the real type (#6327). If the simple representation `V` is of
real type, then `End_{ℝ[G]} V` contains an element `j'` (the antilinear operator `j` normalized so
that `j'² = 1`) that **anticommutes** with `J = ·i`. Together with `J` (`J² = -1`) this exhibits the
split-quaternion / `Mat₂(ℝ)` relations `J² = -1`, `j'² = 1`, `Jj' = -j'J`. -/
theorem exists_normalized_antilinear_of_isRealType
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsRealType ρ) :
    ∃ j' : realGEndAlgebra ρ, j' * j' = 1 ∧ realJ ρ * j' = -(j' * realJ ρ) := by
  obtain ⟨B, hsymm, hnd, hinvB⟩ := h
  obtain ⟨j0, lam, hjequiv, hjsq, hpos⟩ :=
    exists_antilinear_j_of_invariant_nondegenerate hirr B hnd hinvB 1
      (fun v w => by rw [hsymm, one_smul])
  rw [one_mul] at hpos
  -- `(r : ℂ) • v = r • v` for real `r`, via the scalar tower.
  have rcs : ∀ (r : ℝ) (v : V), (r : ℂ) • v = r • v := fun r v => by
    rw [← IsScalarTower.algebraMap_smul ℂ r v, Complex.coe_algebraMap]
  -- The underlying `ℝ`-linear map of the antilinear `j0`.
  let jm : Module.End ℝ V :=
    { toFun := j0
      map_add' := j0.map_add
      map_smul' := fun r v => by
        simp only [RingHom.id_apply]
        rw [← rcs r v, map_smulₛₗ, Complex.conj_ofReal, rcs r (j0 v)] }
  have hmem : jm ∈ realGEndAlgebra ρ := by
    rw [realGEndAlgebra, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply]
    exact (hjequiv g v).symm
  set X : realGEndAlgebra ρ := ⟨jm, hmem⟩ with hXdef
  -- `X² = lam • 1`.
  have hjm2 : X * X = lam • 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hXdef]
    ext v
    simp only [Module.End.mul_apply, SetLike.val_smul, Subalgebra.coe_one, LinearMap.smul_apply,
      Module.End.one_apply]
    show j0 (j0 v) = lam • v
    rw [hjsq v, rcs lam v]
  -- `X` anticommutes with `J = ·i`.
  have hanti0 : realJ ρ * X = -(X * realJ ρ) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul, hXdef]
    ext v
    simp only [Module.End.mul_apply, LinearMap.neg_apply, realJ, complexToRealGEnd_coe_apply]
    show Complex.I • j0 v = -(j0 (Complex.I • v))
    rw [map_smulₛₗ, Complex.conj_I, neg_smul, neg_neg]
  have hsqrt : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hpos.le
  have hsne : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  refine ⟨(Real.sqrt lam)⁻¹ • X, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hjm2, smul_smul]
    have hscal : (Real.sqrt lam)⁻¹ * (Real.sqrt lam)⁻¹ * lam = 1 := by
      rw [← mul_inv, hsqrt, inv_mul_cancel₀ hpos.ne']
    rw [hscal, one_smul]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_neg, hanti0]

end ComplexTypeProof

/-- Problem 5.1.2(a), complex type. If the irreducible representation `V` is of complex type, then
`End_{ℝ[G]} V ≃ₐ[ℝ] ℂ`. -/
theorem realGEndAlgebra_equiv_complex_of_isComplexType
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsComplexType ρ) :
    Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] ℂ) := by
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  -- Equivariance of any element of the centralizer.
  have equiv_of_mem : ∀ (x : realGEndAlgebra ρ) (g : G) (v : V),
      (↑x : Module.End ℝ V) (ρ g v) = ρ g ((↑x : Module.End ℝ V) v) := by
    intro x g v
    have hx2 : (↑x : Module.End ℝ V) ∈
        Subalgebra.centralizer ℝ (Set.range fun g => LinearMap.restrictScalars ℝ (ρ g)) := x.2
    rw [Subalgebra.mem_centralizer_iff] at hx2
    have hcomm := hx2 (LinearMap.restrictScalars ℝ (ρ g)) ⟨g, rfl⟩
    have hv := DFunLike.congr_fun hcomm v
    simpa only [Module.End.mul_apply, LinearMap.restrictScalars_apply] using hv.symm
  -- The `ℂ`-embedding `complexToRealGEnd` is surjective.
  have hsurj : Function.Surjective (complexToRealGEnd ρ) := by
    intro f
    -- `realPlus f` commutes with `i •`.
    have hIp : ∀ v, (↑(realPlus f) : Module.End ℝ V) (Complex.I • v)
        = Complex.I • (↑(realPlus f) : Module.End ℝ V) v := by
      intro v
      have h0 : ((realJ ρ * realPlus f : realGEndAlgebra ρ) : Module.End ℝ V)
             = ((realPlus f * realJ ρ : realGEndAlgebra ρ) : Module.End ℝ V) :=
        congrArg _ (realJ_mul_realPlus f)
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul] at h0
      have hv := DFunLike.congr_fun h0 v
      simpa only [Module.End.mul_apply, realJ, complexToRealGEnd_coe_apply] using hv.symm
    -- `realMinus f` anticommutes with `i •`.
    have hIm : ∀ v, (↑(realMinus f) : Module.End ℝ V) (Complex.I • v)
        = -(Complex.I • (↑(realMinus f) : Module.End ℝ V) v) := by
      intro v
      have h0 : ((realJ ρ * realMinus f : realGEndAlgebra ρ) : Module.End ℝ V)
             = ((-(realMinus f * realJ ρ) : realGEndAlgebra ρ) : Module.End ℝ V) :=
        congrArg _ (realJ_mul_realMinus f)
      rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul] at h0
      have hv := DFunLike.congr_fun h0 v
      simp only [Module.End.mul_apply, LinearMap.neg_apply, realJ,
        complexToRealGEnd_coe_apply] at hv
      rw [hv, neg_neg]
    -- `realPlus f` as a `ℂ`-linear equivariant endomorphism, hence a scalar by Schur.
    obtain ⟨c, hc⟩ := schur_scalar hirr (toCLinear _ hIp)
      (fun g v => equiv_of_mem (realPlus f) g v)
    -- `realMinus f = 0`.
    have hMeq : realMinus f = 0 := by
      by_contra hne
      have hTmne : (↑(realMinus f) : Module.End ℝ V) ≠ 0 := fun h0 => hne (by
        apply Subtype.ext; simpa using h0)
      set ψ : V →ₗ⋆[ℂ] V := toAntilinear _ hIm with hψ
      have hψequiv : ∀ g v, ψ (ρ g v) = ρ g (ψ v) := fun g v => equiv_of_mem (realMinus f) g v
      have hψne : ψ ≠ 0 := fun h0 => hTmne (by
        ext v; have := DFunLike.congr_fun h0 v; simpa [hψ, toAntilinear] using this)
      have hkerinv : ∀ (g : G) (v : V),
          v ∈ LinearMap.ker ψ → ρ g v ∈ LinearMap.ker ψ := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hψequiv, hv, map_zero]
      rcases invSubmodule_eq_bot_or_top hirr (LinearMap.ker ψ) hkerinv with hkbot | hktop
      · -- `ψ` injective: produce a `ℂ`-linear equivariant `V ≃ V*`, contradicting complex type.
        have hψinj : Function.Injective ψ := LinearMap.ker_eq_bot.mp hkbot
        obtain ⟨H, hHinv, hHpos, _⟩ := exists_invariant_posdef_hermitian ρ
        have hΦinj : Function.Injective (hermToDual H) := hermToDual_injective H hHpos
        let e : V →ₗ[ℂ] Module.Dual ℂ V :=
          { toFun := fun v => hermToDual H (ψ v)
            map_add' := fun a b => by simp only [map_add]
            map_smul' := fun c v => by
              simp only [RingHom.id_apply]
              rw [map_smulₛₗ ψ, map_smulₛₗ (hermToDual H), Complex.conj_conj] }
        have heinj : Function.Injective e :=
          fun a b hab => hψinj (hΦinj (show hermToDual H (ψ a) = hermToDual H (ψ b) from hab))
        have hdim : Module.finrank ℂ V = Module.finrank ℂ (Module.Dual ℂ V) :=
          (Subspace.dual_finrank_eq).symm
        apply h
        refine ⟨e.linearEquivOfInjective heinj hdim, ?_⟩
        intro g v
        rw [LinearMap.linearEquivOfInjective_apply, LinearMap.linearEquivOfInjective_apply]
        show hermToDual H (ψ (ρ g v)) = ρ.dual g (hermToDual H (ψ v))
        rw [hψequiv, hermToDual_equivariant H hHinv]
      · exact hψne (by
          ext v
          have : v ∈ LinearMap.ker ψ := hktop ▸ Submodule.mem_top
          rwa [LinearMap.mem_ker] at this)
    -- Assemble: `f = realPlus f = c • id = complexToRealGEnd ρ c`.
    have hPeq : realPlus f = complexToRealGEnd ρ c := by
      apply Subtype.ext
      ext v
      rw [complexToRealGEnd_coe_apply]
      exact hc v
    refine ⟨c, ?_⟩
    have hf : f = realPlus f + realMinus f := (realPlus_add_realMinus f).symm
    rw [hMeq, add_zero] at hf
    rw [hf, hPeq]
  exact ⟨(AlgEquiv.ofBijective (complexToRealGEnd ρ)
    ⟨complexToRealGEnd_injective ρ, hsurj⟩).symm⟩

/-- Problem 5.1.2(a), real type. If the irreducible representation `V` is of real type, then
`End_{ℝ[G]} V ≃ₐ[ℝ] Mat₂(ℝ)`. -/
theorem realGEndAlgebra_equiv_matrix_of_isRealType
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsRealType ρ) :
    Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  sorry

/-- Problem 5.1.2(a), quaternionic type. If the irreducible representation `V` is of quaternionic
type, then `End_{ℝ[G]} V ≃ₐ[ℝ] ℍ`. -/
theorem realGEndAlgebra_equiv_quaternion_of_isQuaternionicType
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsQuaternionicType ρ) :
    Nonempty (realGEndAlgebra ρ ≃ₐ[ℝ] Quaternion ℝ) := by
  sorry

/-- Problem 5.1.2(b). An irreducible complex representation `V` is of real type if and only if it
is the complexification of a real representation: there is a `G`-stable `ℝ`-subspace `W ⊆ V` (a
**real form**) whose `ℂ`-span is all of `V` and with `dim_ℝ W = dim_ℂ V`. -/
theorem isRealType_iff_exists_real_form
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.IsRealType ρ ↔
      ∃ W : Submodule ℝ V,
        (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) ∧
        Submodule.span ℂ (W : Set V) = ⊤ ∧
        Module.finrank ℝ W = Module.finrank ℂ V := by
  sorry

end Problem512

end Etingof
