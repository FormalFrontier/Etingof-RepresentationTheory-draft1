import EtingofRepresentationTheory.Chapter4.Problem4_12_10_Symmetric
import EtingofRepresentationTheory.Chapter5.RepresentationAsModuleHom
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
# Problem 4.12.10: the orbit-evaluation surjection `⊕ₙ SⁿV ↠ ℂ[G]`

This file builds the hard analytic core of Problem 4.12.10 (symmetric-power form): a
**`G`-equivariant surjection from the symmetric algebra onto the regular representation**.

Following the book's hint, fix a covector `u ∈ V*` with trivial `G`-stabilizer (obtained from
`Etingof.exists_trivialStabilizer_covector`). The orbit points `p g := (dual ρ) g u` are then
`|G|` **distinct** covectors. Evaluating a degree-`n` symmetric tensor as a homogeneous polynomial
function at `p g` and assembling over the orbit gives a linear map

`E : (⨁ n, Sym[ℂ]^n V) →ₗ[ℂ] (G → ℂ)`,  `E t g = ∑ₙ evalAt (p g) n (t n)`.

* `Etingof.evalAt p n : Sym[ℂ]^n V →ₗ[ℂ] ℂ` — evaluation of a symmetric tensor at the covector `p`
  (`⨂ₛ vᵢ ↦ ∏ᵢ p vᵢ`), built by descending the tensor-power pairing `PiTensorProduct.dualDistrib`
  through the symmetrization quotient.
* `Etingof.subalgebra_eq_top_of_separatesPoints_of_finite` — an elementary "finite
  Stone-Weierstrass": a point-separating unital subalgebra of `α → 𝕜` (`α` finite) is everything.
* `Etingof.exists_orbitEval_surjection` — the headline: a surjective `G`-equivariant
  `φ : (⨁ n, Sym[ℂ]^n V) →ₗ[ℂ] MonoidAlgebra ℂ G` intertwining `⨁ₙ symPowRep ρ n` with
  `ofMulAction ℂ G G`. This is the crux consumed by the Maschke-splitting assembly step.
-/

open scoped TensorProduct DirectSum

set_option linter.unusedFintypeInType false

noncomputable section

namespace Etingof

/-! ## An algebraic finite Stone-Weierstrass -/

/-- **Finite point-separation.** A unital subalgebra `A` of the function algebra `α → 𝕜` over a
field `𝕜`, with `α` finite, that separates the points of `α` is everything. The proof builds, for
each `i`, the indicator `Pi.single i 1` as a product of Lagrange-style affine functions drawn from
`A`, then writes an arbitrary `f` as `∑ᵢ f i • Pi.single i 1`. -/
theorem subalgebra_eq_top_of_separatesPoints_of_finite
    {α : Type*} [Fintype α] {𝕜 : Type*} [Field 𝕜] (A : Subalgebra 𝕜 (α → 𝕜))
    (hsep : ∀ x y : α, x ≠ y → ∃ f ∈ A, f x ≠ f y) : A = ⊤ := by
  classical
  -- Each indicator `Pi.single i 1` lies in `A`.
  have hsingle : ∀ i : α, Pi.single i (1 : 𝕜) ∈ A := by
    intro i
    -- For each `j ≠ i` an affine function in `A` that is `1` at `i` and `0` at `j`.
    have hg : ∀ j : {j : α // j ≠ i}, ∃ g ∈ A, g i = 1 ∧ g j.1 = 0 := by
      rintro ⟨j, hj⟩
      obtain ⟨fj, hfjA, hfj⟩ := hsep i j (Ne.symm hj)
      have hc0 : fj i - fj j ≠ 0 := sub_ne_zero.mpr hfj
      refine ⟨(fj i - fj j)⁻¹ • (fj - fj j • 1), ?_, ?_, ?_⟩
      · exact Subalgebra.smul_mem _
          (Subalgebra.sub_mem _ hfjA (Subalgebra.smul_mem _ (one_mem _) _)) _
      · simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
        rw [inv_mul_cancel₀ hc0]
      · simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one, sub_self,
          mul_zero]
    choose g hgA hgi hgj using hg
    -- The Lagrange indicator: product over the `|α|-1` factors.
    have hmem : (∏ j : {j : α // j ≠ i}, g j) ∈ A := prod_mem (fun j _ => hgA j)
    have heq : (∏ j : {j : α // j ≠ i}, g j) = Pi.single i (1 : 𝕜) := by
      funext k
      rw [Finset.prod_apply]
      by_cases hk : k = i
      · subst hk
        simp only [hgi, Finset.prod_const_one, Pi.single_eq_same]
      · rw [Finset.prod_eq_zero (Finset.mem_univ (⟨k, hk⟩ : {j : α // j ≠ i})) (hgj ⟨k, hk⟩),
          Pi.single_eq_of_ne hk]
    rwa [heq] at hmem
  rw [eq_top_iff]
  intro f _
  have hf : f = ∑ i : α, f i • Pi.single i (1 : 𝕜) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ k f]
    simp
  rw [hf]
  exact Subalgebra.sum_mem _ (fun i _ => Subalgebra.smul_mem _ (hsingle i) _)

/-! ## Evaluation of a symmetric tensor at a covector -/

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- The evaluation of a degree-`n` **tensor** at a covector `p`, `⨂ᵢ vᵢ ↦ ∏ᵢ p vᵢ`, realised as
the image of the constant `n`-fold tensor `⨂ₜ p` under `PiTensorProduct.dualDistrib`. -/
def evalTensorPow (p : Module.Dual ℂ V) (n : ℕ) : (⨂[ℂ]^n V) →ₗ[ℂ] ℂ :=
  PiTensorProduct.dualDistrib (⨂ₜ[ℂ] (_ : Fin n), p)

@[simp] lemma evalTensorPow_tprod (p : Module.Dual ℂ V) (n : ℕ) (v : Fin n → V) :
    evalTensorPow p n (PiTensorProduct.tprod ℂ v) = ∏ i, p (v i) := by
  simp only [evalTensorPow, PiTensorProduct.dualDistrib_apply]

/-- The evaluation of a degree-`n` **symmetric tensor** at a covector `p`, `⨂ₛᵢ vᵢ ↦ ∏ᵢ p vᵢ`.
Since `∏ᵢ p vᵢ` is symmetric in the `vᵢ`, `evalTensorPow` descends through the symmetrization
quotient `SymmetricPower.mk`. -/
def evalAt (p : Module.Dual ℂ V) (n : ℕ) : Sym[ℂ]^n V →ₗ[ℂ] ℂ where
  toFun := AddCon.lift _ (evalTensorPow p n).toAddMonoidHom (fun x y h => by
    induction h with
    | of x y h => cases h with
      | perm e f =>
        change evalTensorPow p n (PiTensorProduct.tprod ℂ f)
          = evalTensorPow p n (PiTensorProduct.tprod ℂ fun i => f (e i))
        rw [evalTensorPow_tprod, evalTensorPow_tprod]
        exact (Equiv.prod_comp e (fun i => p (f i))).symm
    | refl => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | add _ _ ih₁ ih₂ =>
        change evalTensorPow p n (_ + _) = evalTensorPow p n (_ + _)
        rw [map_add, map_add]
        exact congr_arg₂ (· + ·) ih₁ ih₂)
  map_add' x y := by
    refine AddCon.induction_on₂ x y (fun a b => ?_)
    change evalTensorPow p n (a + b) = evalTensorPow p n a + evalTensorPow p n b
    rw [map_add]
  map_smul' r x := by
    refine AddCon.induction_on x (fun a => ?_)
    change evalTensorPow p n (r • a) = r • evalTensorPow p n a
    rw [map_smul]

@[simp] lemma evalAt_mk (p : Module.Dual ℂ V) (n : ℕ) (x : ⨂[ℂ]^n V) :
    evalAt p n (SymmetricPower.mk ℂ (Fin n) V x) = evalTensorPow p n x := rfl

@[simp] lemma evalAt_mk_tprod (p : Module.Dual ℂ V) (n : ℕ) (v : Fin n → V) :
    evalAt p n (SymmetricPower.mk ℂ (Fin n) V (PiTensorProduct.tprod ℂ v)) = ∏ i, p (v i) := by
  rw [evalAt_mk, evalTensorPow_tprod]

/-- Naturality of `evalAt` in the covector: evaluating `symmetricPowerMap f x` at `p` is the same
as evaluating `x` at the pulled-back covector `p ∘ₗ f`. -/
lemma evalAt_symmetricPowerMap (p : Module.Dual ℂ V) (n : ℕ) (f : V →ₗ[ℂ] V) (x : Sym[ℂ]^n V) :
    evalAt p n (symmetricPowerMap f x) = evalAt (p ∘ₗ f) n x := by
  obtain ⟨y, rfl⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk ℂ (Fin n) V) x
  rw [symmetricPowerMap_mk, evalAt_mk, evalAt_mk]
  have key : evalTensorPow p n ∘ₗ PiTensorProduct.map (fun _ : Fin n => f) = evalTensorPow (p ∘ₗ f) n := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, evalTensorPow_tprod]
  exact LinearMap.congr_fun key y

/-! ## The orbit-evaluation map -/

variable {G : Type*} [Group G] [Fintype G] (ρ : Representation ℂ G V)

/-- Evaluation of the whole symmetric algebra at a single covector `q`, assembled from the graded
`evalAt q n`: `(⨁ n, Sym[ℂ]^n V) →ₗ[ℂ] ℂ`. -/
def evalDsum (q : Module.Dual ℂ V) : (⨁ n : ℕ, Sym[ℂ]^n V) →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ ℕ ℂ (fun n => evalAt q n)

@[simp] lemma evalDsum_lof (q : Module.Dual ℂ V) (n : ℕ) (w : Sym[ℂ]^n V) :
    evalDsum q (DirectSum.lof ℂ ℕ (fun n => Sym[ℂ]^n V) n w) = evalAt q n w := by
  simp only [evalDsum, DirectSum.toModule_lof]

variable (u : Module.Dual ℂ V)

/-- The orbit covector `p g = (dual ρ) g u`. -/
def orbitCovector (g : G) : Module.Dual ℂ V := (Representation.dual ρ) g u

lemma orbitCovector_comp (x g : G) :
    (orbitCovector ρ u x) ∘ₗ ρ g = orbitCovector ρ u (g⁻¹ * x) := by
  ext v
  change (orbitCovector ρ u x) (ρ g v) = (orbitCovector ρ u (g⁻¹ * x)) v
  simp only [orbitCovector, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv]

/-- The assembled orbit-evaluation map `E : (⨁ n, Sym[ℂ]^n V) →ₗ[ℂ] (G → ℂ)`,
`E t g = ∑ₙ evalAt (p g) n (t n)`. -/
def orbitEval : (⨁ n : ℕ, Sym[ℂ]^n V) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi (fun g => evalDsum (orbitCovector ρ u g))

@[simp] lemma orbitEval_apply (t : ⨁ n : ℕ, Sym[ℂ]^n V) (g : G) :
    orbitEval ρ u t g = evalDsum (orbitCovector ρ u g) t := rfl

/-- Left-translation equivariance of the single-covector evaluation: precomposing with the
direct-sum action shifts the covector along the orbit. -/
lemma evalDsum_directSum (g x : G) :
    evalDsum (orbitCovector ρ u x) ∘ₗ (Representation.directSum (fun n => symPowRep ρ n)) g
      = evalDsum (orbitCovector ρ u (g⁻¹ * x)) := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, Representation.directSum_apply, DirectSum.lmap_lof,
    evalDsum_lof, symPowRep_apply, evalAt_symmetricPowerMap, orbitCovector_comp]

/-! ## Surjectivity -/

/-- Distinctness of the orbit points: if `u` has trivial stabilizer then `g ↦ (dual ρ) g u` is
injective. -/
lemma orbitCovector_injective (hρ : Function.Injective ρ)
    (hu : ∀ g : G, (Representation.dual ρ) g u = u → g = 1) :
    Function.Injective (orbitCovector ρ u) := by
  intro x y hxy
  -- `(dual ρ) (y⁻¹ x) u = u`, so `y⁻¹ x = 1`.
  have h1 : (Representation.dual ρ) (y⁻¹ * x) u = u := by
    have : (Representation.dual ρ) (y⁻¹ * x) u
        = (Representation.dual ρ) y⁻¹ ((Representation.dual ρ) x u) := by
      rw [map_mul]; rfl
    rw [this, show (Representation.dual ρ) x u = orbitCovector ρ u x from rfl, hxy]
    change (Representation.dual ρ) y⁻¹ ((Representation.dual ρ) y u) = u
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have := hu _ h1
  rw [inv_mul_eq_one] at this
  exact this.symm

/-- The orbit-evaluation map is **surjective** onto `G → ℂ`. Its range is a linear subspace
containing all monomials `g ↦ ∏ᵢ (p g) vᵢ`; these are the products of the point-separating
degree-1 functions `g ↦ (p g) v`, so their span is a point-separating subalgebra, hence
everything by `subalgebra_eq_top_of_separatesPoints_of_finite`. -/
lemma orbitEval_surjective (hρ : Function.Injective ρ)
    (hu : ∀ g : G, (Representation.dual ρ) g u = u → g = 1) :
    Function.Surjective (orbitEval ρ u) := by
  classical
  rw [← LinearMap.range_eq_top]
  -- The generating degree-1 functions and their subalgebra.
  set ℓ : V → (G → ℂ) := fun v g => (orbitCovector ρ u g) v with hℓ
  set S : Set (G → ℂ) := Set.range ℓ with hS
  -- Every monomial `∏ᵢ (p g) vᵢ` is in the range (image of a symmetric pure tensor).
  have hmono : ∀ (m : ℕ) (v : Fin m → V),
      (fun g => ∏ i, (orbitCovector ρ u g) (v i)) ∈ LinearMap.range (orbitEval ρ u) := by
    intro m v
    refine ⟨DirectSum.lof ℂ ℕ (fun n => Sym[ℂ]^n V) m
      (SymmetricPower.mk ℂ (Fin m) V (PiTensorProduct.tprod ℂ v)), ?_⟩
    funext g
    rw [orbitEval_apply, evalDsum_lof, evalAt_mk_tprod]
  -- The monoid closure of the generators lands in the range.
  have hclosure : ∀ f ∈ Submonoid.closure S, f ∈ LinearMap.range (orbitEval ρ u) := by
    intro f hf
    have hex : ∃ (m : ℕ) (v : Fin m → V), f = fun g => ∏ i, (orbitCovector ρ u g) (v i) := by
      induction hf using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨1, ![v], by funext g; simp [hℓ]⟩
      | one => exact ⟨0, ![], by funext g; simp⟩
      | mul x y _ _ ihx ihy =>
        obtain ⟨m, v, rfl⟩ := ihx
        obtain ⟨m', v', rfl⟩ := ihy
        refine ⟨m + m', Fin.append v v', ?_⟩
        funext g
        simp only [Pi.mul_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
    obtain ⟨m, v, rfl⟩ := hex
    exact hmono m v
  -- The subalgebra generated by the degree-1 functions is everything.
  have htop : Algebra.adjoin ℂ S = ⊤ := by
    apply subalgebra_eq_top_of_separatesPoints_of_finite
    intro x y hxy
    have hpxy : orbitCovector ρ u x ≠ orbitCovector ρ u y :=
      fun h => hxy (orbitCovector_injective ρ u hρ hu h)
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hpxy
    exact ⟨ℓ v, Algebra.subset_adjoin ⟨v, rfl⟩, hv⟩
  -- Combine: range ⊇ adjoin.toSubmodule = ⊤.
  have hle : (Algebra.adjoin ℂ S).toSubmodule ≤ LinearMap.range (orbitEval ρ u) := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    exact hclosure
  rw [htop] at hle
  simpa using hle

/-! ## The `G`-equivariant surjection onto the regular representation -/

/-- **Problem 4.12.10 orbit-evaluation surjection.** For a finite group `G` with a faithful
representation `ρ` on `V`, there is a surjective `G`-equivariant linear map from the symmetric
algebra `⨁ₙ SⁿV` onto the regular representation `ℂ[G]`. Concretely, evaluating a symmetric tensor
along the trivial-stabilizer orbit `{g · u}` and reading the result as a function on `G`
(equivalently an element of `MonoidAlgebra ℂ G`) is a surjection intertwining `⨁ₙ symPowRep ρ n`
with `ofMulAction ℂ G G`.

By Maschke this surjection splits, so `ℂ[G]` — which contains every irreducible — is a
`G`-summand of `⨁ₙ SⁿV`; this is what the assembly step needs to place any irreducible `W` inside
some `SⁿV`. -/
theorem exists_orbitEval_surjection (hρ : Function.Injective ρ) :
    ∃ φ : (⨁ n : ℕ, Sym[ℂ]^n V) →ₗ[ℂ] MonoidAlgebra ℂ G,
      Function.Surjective φ ∧
      ∀ g : G, φ ∘ₗ (Representation.directSum (fun n => symPowRep ρ n)) g
        = (Representation.ofMulAction ℂ G G) g ∘ₗ φ := by
  classical
  -- The trivial-stabilizer covector.
  obtain ⟨u, hu⟩ := Etingof.exists_trivialStabilizer_covector ρ hρ
  -- Transport `orbitEval` (into `G → ℂ`) to `MonoidAlgebra ℂ G = G →₀ ℂ`.
  refine ⟨(MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
      (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm.toLinearMap ∘ₗ orbitEval ρ u, ?_, ?_⟩
  · -- surjective: composite of surjections
    exact (MonoidAlgebra.coeffLinearEquiv ℂ).symm.surjective.comp
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm.surjective.comp
        (orbitEval_surjective ρ u hρ hu))
  · -- equivariance
    intro g
    apply LinearMap.ext
    intro t
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro x
    -- unfold the composite and the finsupp/function transport (both by `rfl`)
    change orbitEval ρ u ((Representation.directSum (fun n => symPowRep ρ n)) g t) x
      = ((Representation.ofMulAction ℂ G G) g
          (MonoidAlgebra.ofCoeff
            ((Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm (orbitEval ρ u t)))).coeff x
    rw [Representation.ofMulAction_apply]
    change orbitEval ρ u ((Representation.directSum (fun n => symPowRep ρ n)) g t) x
      = orbitEval ρ u t (g⁻¹ • x)
    rw [orbitEval_apply, orbitEval_apply, smul_eq_mul,
      ← LinearMap.congr_fun (evalDsum_directSum ρ u g x) t]
    rfl

end Etingof

end

section MainTheorem

open scoped TensorProduct
open Etingof

/-- **Problem 4.12.10 (symmetric-power form).** Let `G` be a finite group with a faithful
complex representation `ρ` on `V`, and let `σ` be an irreducible complex representation on `W`.
Then `W` occurs inside the symmetric power `SⁿV` for some `n`: there is a nonzero
`G`-equivariant linear map `W → Sym[ℂ]^n V` intertwining `σ` with `symPowRep ρ n`.

Together with `Etingof.symPowEmbedding_equivariant`, this gives the book's full statement
"occurs inside `SⁿV` (and hence inside `V^{⊗n}`)".

Proof (the book's hint, assembled by Maschke splitting): the simple `W` embeds `G`-equivariantly
in the regular representation `ℂ[G]` (`exists_injective_intertwiner_ofMulAction`). The
orbit-evaluation map `E : ⨁ₙ SⁿV ↠ ℂ[G]` (`exists_orbitEval_surjection`, built from a
trivial-stabilizer covector) is a `G`-equivariant surjection; packaged as a `ℂ[G]`-module hom of
`asModule`s it splits, because the regular module is semisimple (Maschke, characteristic `0`), so
it has a `ℂ[G]`-linear section `s`. Repackaging `s` as a `ℂ`-linear `G`-equivariant map and
composing with the embedding places `W` inside `⨁ₙ SⁿV` by an injective, hence nonzero,
intertwiner; extracting the summand on which it does not vanish
(`exists_component_intertwiner_of_ne_zero`) yields the index `n`. -/
theorem Etingof.Problem4_12_10_symmetric {G : Type*} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule) :
    ∃ (n : ℕ) (φ : W →ₗ[ℂ] (Sym[ℂ]^n V)),
      φ ≠ 0 ∧ ∀ g : G, φ ∘ₗ σ g = (symPowRep ρ n g) ∘ₗ φ := by
  classical
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- (1) The simple `W` embeds `G`-equivariantly in the regular representation `ℂ[G]`.
  obtain ⟨ι, hι_inj, hι_equiv⟩ := exists_injective_intertwiner_ofMulAction σ hσ
  -- (2) The orbit-evaluation surjection `E : ⨁ₙ SⁿV ↠ ℂ[G]`.
  obtain ⟨E, hE_surj, hE_equiv⟩ := Etingof.exists_orbitEval_surjection ρ hρ
  -- Package `E` as a `ℂ[G]`-module hom of `asModule`s and split it: the regular module is
  -- semisimple (Maschke, char 0), so the surjection has a `ℂ[G]`-linear section `s`.
  set F : (Representation.directSum (fun n => symPowRep ρ n)).asModule
      →ₗ[MonoidAlgebra ℂ G] (Representation.ofMulAction ℂ G G).asModule :=
    Representation.asModuleHomOfIntertwiner E
      (fun g x => LinearMap.congr_fun (hE_equiv g) x) with hF
  have hF_surj : Function.Surjective F := hE_surj
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property (R := MonoidAlgebra ℂ G)
    (M := (Representation.directSum (fun n => symPowRep ρ n)).asModule)
    (N := (Representation.ofMulAction ℂ G G).asModule)
    (P := (Representation.ofMulAction ℂ G G).asModule) F hF_surj (LinearMap.id)
  have hs_linv : Function.LeftInverse F s := fun x => by
    simpa using LinearMap.congr_fun hs x
  -- Repackage the section as a `ℂ`-linear `G`-equivariant map `ℂ[G] → ⨁ₙ SⁿV`.
  set sLin := Representation.intertwinerOfAsModuleHom s with hsLin
  have hsLin_inj : Function.Injective sLin :=
    Representation.intertwinerOfAsModuleHom_injective hs_linv.injective
  -- (3) `Φ = sLin ∘ ι : W ↪ ⨁ₙ SⁿV` is injective, hence nonzero, and `G`-equivariant.
  set Φ := sLin ∘ₗ ι with hΦ
  have hΦ_inj : Function.Injective Φ := hsLin_inj.comp hι_inj
  haveI : Nontrivial W := hσ.nontrivial
  have hΦ_ne : Φ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    intro h0
    apply hw
    apply hΦ_inj
    rw [h0]; simp
  have hΦ_equiv : ∀ g : G, Φ ∘ₗ σ g
      = (Representation.directSum (fun n => symPowRep ρ n)) g ∘ₗ Φ := by
    intro g
    apply LinearMap.ext
    intro w
    have h1 : ι (σ g w) = (Representation.ofMulAction ℂ G G) g (ι w) :=
      LinearMap.congr_fun (hι_equiv g) w
    have h2 := Representation.intertwinerOfAsModuleHom_equivariant s g (ι w)
    simp only [hΦ, LinearMap.comp_apply]
    exact (congrArg (⇑sLin) h1).trans h2
  -- (4) Extract a single symmetric-power summand `SⁿV` on which the composite is nonzero.
  obtain ⟨n, ψ, hψ_ne, hψ_equiv⟩ :=
    exists_component_intertwiner_of_ne_zero (fun n => symPowRep ρ n) σ Φ hΦ_ne hΦ_equiv
  exact ⟨n, ψ, hψ_ne, hψ_equiv⟩

end MainTheorem
