import Mathlib
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Exercise 4.2.3: enumeration of simple `K[G]`-modules in the modular case

Over an algebraically closed field `K` (with no `NeZero (Nat.card G : K)` hypothesis, so the
modular case is allowed) this file builds the standard family of simple `K[G]`-modules coming from
the Wedderburn decomposition of the semisimple quotient `A = K[G] ⧸ rad(K[G])`.

The semisimple, non-modular enumeration lives in
`Infrastructure/IrreducibleEnumeration.lean` (`IrrepDecomp`), but that development bundles an
algebra isomorphism `k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k`, which does not exist
modularly (the radical is nonzero). Here we replace the isomorphism by a surjective algebra
hom `π : K[G] →ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K`, the composite of the quotient map
`K[G] ↠ A` with the Wedderburn isomorphism of `A`. Only surjectivity of `π` is used in the
column-representation argument, so the enumeration survives.

## Main constructions

* `SplitData K G`: bundles `n`, the block sizes `d`, and the surjective `π`.
* `SplitData.of`: constructs the data from `A = K[G] ⧸ rad` semisimple and Wedderburn.
* `SplitData.blockHom`: projection `K[G] →ₐ[K] Matrix (Fin (D.d i)) (Fin (D.d i)) K` to block `i`
  (surjective).
* `SplitData.Std D i := Fin (D.d i) → K`: the `i`-th standard module, a simple, finite-dimensional
  `K[G]`-module with `IsScalarTower K (MonoidAlgebra K G) (D.Std i)`.

The enumeration (`Std` pairwise non-isomorphic via `Std_injective` and exhaustive via
`exists_Std_linearEquiv`) and the resulting count `Nat.card (SimpleModuleClasses K[G]) = n`
(`card_simpleModuleClasses` / `exists_splitSimples_count`) are proved below.

## References

- Etingof, *Introduction to Representation Theory*, §4.
- `Infrastructure/IrreducibleEnumeration.lean` (`IrrepDecomp`, the analog requiring `NeZero`).
- Mathlib: `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`.
-/

open CategoryTheory

namespace Etingof.SplitSimples

universe u v

variable (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G]

/-- Bundled data for the modular Wedderburn enumeration of `K[G]`: the number of blocks `n`, the
block sizes `d`, and a **surjective** algebra hom
`π : K[G] →ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K`, obtained as
`(K[G] ↠ K[G]/rad) ≫ (Wedderburn iso of the semisimple quotient)`. -/
structure SplitData where
  /-- Number of Wedderburn blocks of the semisimple quotient `K[G] ⧸ rad`. -/
  n : ℕ
  /-- Block sizes. -/
  d : Fin n → ℕ
  /-- Each block is nonempty. -/
  d_pos : ∀ i, NeZero (d i)
  /-- The surjective structure hom `K[G] ↠ Π i, Matrix (Fin (d i)) (Fin (d i)) K`. -/
  π : MonoidAlgebra K G →ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K
  /-- `π` is surjective (composite of a surjective quotient map with an isomorphism). -/
  π_surj : Function.Surjective π
  /-- The kernel of `π` is exactly the Jacobson radical: `π` is the composite of the quotient
  `K[G] ↠ K[G]/rad` with the (injective) Wedderburn isomorphism, so `ker π = rad`. This pins down
  the structure: without it `π` could be, e.g., a projection onto a single Wedderburn factor,
  whose kernel is strictly larger than `rad`, and the enumeration below would be false. -/
  π_ker : RingHom.ker π.toRingHom = Ring.jacobson (MonoidAlgebra K G)

variable {K G}

/-- Construct the split data from the Wedderburn decomposition of the semisimple quotient
`A = K[G] ⧸ rad(K[G])`. Over an algebraically closed field, `A` is a finite product of matrix
algebras; precomposing with the quotient map yields the surjective structure hom `π`. -/
noncomputable def SplitData.of : SplitData K G := by
  classical
  haveI : Module.Finite K (MonoidAlgebra K G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G K)
  haveI : IsArtinianRing (MonoidAlgebra K G) := IsArtinianRing.of_finite K (MonoidAlgebra K G)
  haveI : IsSemiprimaryRing (MonoidAlgebra K G) := inferInstance
  set J := Ring.jacobson (MonoidAlgebra K G) with hJ
  haveI : IsSemisimpleRing (MonoidAlgebra K G ⧸ J) := IsSemiprimaryRing.isSemisimpleRing
  haveI : Module.Finite K (MonoidAlgebra K G ⧸ J) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ K J).toLinearMap (Ideal.Quotient.mkₐ_surjective K J)
  have hwed := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K (MonoidAlgebra K G ⧸ J)
  choose n d hd hn using hwed
  refine
    { n := n
      d := d
      d_pos := hd
      π := ((hn.some).toAlgHom).comp (Ideal.Quotient.mkₐ K J)
      π_surj := ?_
      π_ker := ?_ }
  · intro x
    obtain ⟨y, hy⟩ := EquivLike.surjective hn.some x
    obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective K J y
    exact ⟨z, by rw [AlgHom.comp_apply, hz]; exact hy⟩
  · -- `ker (iso ∘ quotient) = ker quotient = J`, since the Wedderburn iso is injective.
    have hinj : Function.Injective ((hn.some).toAlgHom.toRingHom) :=
      (EquivLike.injective hn.some)
    have hcomp : (((hn.some).toAlgHom).comp (Ideal.Quotient.mkₐ K J)).toRingHom
        = ((hn.some).toAlgHom.toRingHom).comp ((Ideal.Quotient.mkₐ K J).toRingHom) := rfl
    rw [hcomp, RingHom.ker_comp_of_injective _ hinj, Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker]

/-- The projection `K[G] →ₐ[K] Matrix (Fin (D.d i)) (Fin (D.d i)) K` onto the `i`-th block. -/
noncomputable def SplitData.blockHom (D : SplitData K G) (i : Fin D.n) :
    MonoidAlgebra K G →ₐ[K] Matrix (Fin (D.d i)) (Fin (D.d i)) K :=
  (Pi.evalAlgHom K (fun i => Matrix (Fin (D.d i)) (Fin (D.d i)) K) i).comp D.π

/-- Each block projection is surjective (composite of the surjective `π` with an evaluation). -/
lemma SplitData.blockHom_surjective (D : SplitData K G) (i : Fin D.n) :
    Function.Surjective (D.blockHom i) := by
  intro M
  obtain ⟨a, ha⟩ := D.π_surj (Pi.single i M)
  refine ⟨a, ?_⟩
  simp only [SplitData.blockHom, AlgHom.comp_apply, ha, Pi.evalAlgHom_apply, Pi.single_eq_same]

/-! ### Standard modules -/

/-- The `i`-th standard module `Fin (D.d i) → K`, made a `K[G]`-module via `blockHom i`. -/
def SplitData.Std (D : SplitData K G) (i : Fin D.n) : Type u := Fin (D.d i) → K

namespace SplitData

instance (D : SplitData K G) (i : Fin D.n) : AddCommGroup (D.Std i) :=
  inferInstanceAs (AddCommGroup (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) : Module K (D.Std i) :=
  inferInstanceAs (Module K (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) :
    Module (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (D.Std i) :=
  inferInstanceAs (Module (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) :
    IsScalarTower K (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (D.Std i) :=
  inferInstanceAs (IsScalarTower K (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) : Module.Finite K (D.Std i) :=
  inferInstanceAs (Module.Finite K (Fin (D.d i) → K))

/-- The `K[G]`-action on the `i`-th standard module, factoring through `blockHom i`. -/
noncomputable instance instModuleMonoidAlgebraStd (D : SplitData K G) (i : Fin D.n) :
    Module (MonoidAlgebra K G) (D.Std i) :=
  Module.compHom (D.Std i) (D.blockHom i).toRingHom

/-- The `K`-action and the `K[G]`-action on a standard module are compatible: the structure hom
`blockHom i` is `K`-linear. -/
instance (D : SplitData K G) (i : Fin D.n) :
    IsScalarTower K (MonoidAlgebra K G) (D.Std i) where
  smul_assoc c x m := by
    change (D.blockHom i).toRingHom (c • x) • m = c • ((D.blockHom i).toRingHom x • m)
    have hlin : (D.blockHom i).toRingHom (c • x) = c • (D.blockHom i).toRingHom x := by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul]
    rw [hlin, smul_assoc]

/-- Each standard module is a simple `K[G]`-module: it is the simple `Matrix`-module `Fin (D.d i) →
K`, restricted along the surjective block projection `blockHom i`. -/
theorem isSimpleModule_Std (D : SplitData K G) (i : Fin D.n) :
    IsSimpleModule (MonoidAlgebra K G) (D.Std i) := by
  haveI := D.d_pos i
  haveI : IsSimpleModule (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (D.Std i) :=
    inferInstanceAs (IsSimpleModule (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (Fin (D.d i) → K))
  exact IsSimpleModule.compHom (D.blockHom i).toRingHom (D.blockHom_surjective i)

/-! ### Enumeration and count

The three remaining facts are: the standard modules are pairwise non-isomorphic
(`Std_injective`), they exhaust the simple `K[G]`-modules (`exists_Std_linearEquiv`), and the
resulting count `Nat.card (SimpleModuleClasses K[G]) = n` (`card_simpleModuleClasses` /
`exists_splitSimples_count`). The arguments follow those for `IrrepDecomp` in
`Infrastructure/IrreducibleEnumeration.lean`, with the algebra isomorphism replaced by the
surjection `π` (only surjectivity is used). -/

/-- Over a simple artinian ring, any two simple modules are isomorphic: each is isomorphic to a
minimal left ideal, and all minimal left ideals lie in the single isotypic component
(`IsSimpleRing.isIsotypic`). -/
theorem linearEquiv_of_isSimpleRing {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    (M N : Type*) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨I, ⟨eM⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  obtain ⟨I', ⟨eN⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  haveI : IsSimpleModule R I := IsSimpleModule.congr eM.symm
  haveI : IsSimpleModule R I' := IsSimpleModule.congr eN.symm
  have h : Nonempty ((I' : Submodule R R) ≃ₗ[R] (I : Submodule R R)) :=
    (IsSimpleRing.isIsotypic R R : IsIsotypic R R) I I'
  exact ⟨eM.trans (h.some.symm.trans eN.symm)⟩

/-- The `K[G]`-action on a standard module factors through `blockHom`: `x • v` is the matrix
`blockHom i x` acting on the column vector `v`. This is definitional (`Module.compHom`), exposed
here as a rewrite lemma. -/
lemma smul_Std_eq (D : SplitData K G) (i : Fin D.n) (x : MonoidAlgebra K G) (v : D.Std i) :
    x • v = D.blockHom i x • v := rfl

/-- **Pairwise non-isomorphic.** Distinct standard modules are not isomorphic.
If `i ≠ j`, pick a preimage `e ∈ K[G]` of the block idempotent `Pi.single i 1`; then `e` acts as
the identity on `Std i` (its `i`-block is the identity matrix) and as `0` on `Std j` (its `j`-block
is the zero matrix). Any `K[G]`-linear map `Std i → Std j` therefore vanishes, so no isomorphism
can exist. -/
theorem Std_injective (D : SplitData K G) (i j : Fin D.n)
    (h : Nonempty (D.Std i ≃ₗ[MonoidAlgebra K G] D.Std j)) : i = j := by
  obtain ⟨φ⟩ := h
  by_contra hij
  -- A preimage of the `i`-th block idempotent `Pi.single i 1`.
  obtain ⟨e, he⟩ := D.π_surj (Pi.single i 1)
  -- `e` acts as the identity on `Std i`.
  have hei : ∀ v : D.Std i, e • v = v := by
    intro v
    have hblock : D.blockHom i e = 1 := by
      simp only [SplitData.blockHom, AlgHom.comp_apply, he, Pi.evalAlgHom_apply, Pi.single_eq_same]
    rw [smul_Std_eq, hblock, one_smul]
  -- `e` acts as `0` on `Std j` (since `i ≠ j`).
  have hej : ∀ w : D.Std j, e • w = 0 := by
    intro w
    have hblock : D.blockHom j e = 0 := by
      simp only [SplitData.blockHom, AlgHom.comp_apply, he, Pi.evalAlgHom_apply,
        Pi.single_eq_of_ne (Ne.symm hij)]
    rw [smul_Std_eq, hblock, zero_smul]
  -- Hence `φ` kills every vector.
  have hzero : ∀ v : D.Std i, φ v = 0 := fun v => by
    calc φ v = φ (e • v) := by rw [hei v]
      _ = e • φ v := map_smul φ e v
      _ = 0 := hej (φ v)
  -- But `Std i` is nontrivial (`d i ≠ 0`), contradicting injectivity of `φ`.
  haveI := D.d_pos i
  have hv : (fun _ => (1 : K)) ≠ (0 : D.Std i) := fun hcontra =>
    one_ne_zero (congr_fun hcontra ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩)
  exact hv (φ.injective ((hzero _).trans (map_zero φ).symm))

/-- **Exhaustiveness.** Every simple `K[G]`-module is isomorphic to some standard
module `Std i`. -/
theorem exists_Std_linearEquiv (D : SplitData K G)
    (M : Type u) [AddCommGroup M] [Module (MonoidAlgebra K G) M]
    [IsSimpleModule (MonoidAlgebra K G) M] :
    ∃ i, Nonempty (M ≃ₗ[MonoidAlgebra K G] D.Std i) := by
  classical
  -- `ker π = rad` annihilates the simple module `M`.
  have hann : ∀ a : MonoidAlgebra K G, D.π a = 0 → ∀ m : M, a • m = (0 : M) := by
    intro a ha m
    have hmem : a ∈ Ring.jacobson (MonoidAlgebra K G) := by
      rw [← D.π_ker, RingHom.mem_ker]; exact ha
    exact Module.mem_annihilator.mp
      (IsSemisimpleModule.jacobson_le_annihilator (MonoidAlgebra K G) M hmem) m
  -- The block central idempotents `Pi.single i 1` are central in `Π Matrix`.
  have hcentral : ∀ (i : Fin D.n) (b : Π j, Matrix (Fin (D.d j)) (Fin (D.d j)) K),
      (Pi.single i (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) K)) * b
        = b * Pi.single i 1 := by
    intro i b; funext j
    rcases eq_or_ne j i with h | h
    · subst h; simp [Pi.mul_apply, Pi.single_eq_same]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne h]
  -- For each block, a preimage `ε i` of the central idempotent `Pi.single i 1`.
  choose ε hε using
    fun i : Fin D.n => D.π_surj (Pi.single i (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) K))
  -- `ε i` acts `K[G]`-linearly (it commutes with the action, mod the annihilated kernel).
  have hlin : ∀ (i : Fin D.n) (a : MonoidAlgebra K G) (m : M),
      a • (ε i • m) = ε i • (a • m) := by
    intro i a m
    have h0 : (a * ε i) • m = (ε i * a) • m := by
      apply sub_eq_zero.mp
      rw [← sub_smul]
      apply hann
      rw [map_sub, map_mul, map_mul, hε i, hcentral i (D.π a), sub_self]
    rw [mul_smul, mul_smul] at h0
    exact h0
  -- `ε i` is idempotent on `M`.
  have hidem : ∀ (i : Fin D.n) (m : M), ε i • (ε i • m) = ε i • m := by
    intro i m
    rw [← mul_smul]
    apply sub_eq_zero.mp
    rw [← sub_smul]
    apply hann
    rw [map_sub, map_mul, hε i, sub_eq_zero]
    funext j
    rcases eq_or_ne j i with h | h
    · subst h; simp [Pi.mul_apply, Pi.single_eq_same]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne h]
  -- `∑ ε i` acts as the identity on `M` (`∑ Pi.single i 1 = 1`).
  have hsum : ∀ m : M, ∑ i, ε i • m = m := by
    intro m
    have h1 : ((∑ i, ε i) - 1) • m = 0 := by
      apply hann
      rw [map_sub, map_one, map_sum]
      have hone : ∑ i, D.π (ε i)
          = (1 : Π j, Matrix (Fin (D.d j)) (Fin (D.d j)) K) := by
        simp only [hε]
        exact Finset.univ_sum_single 1
      rw [hone, sub_self]
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [← Finset.sum_smul]; exact h1
  -- The `K[G]`-linear idempotent endomorphism `m ↦ ε i • m`.
  let fmap : Fin D.n → (M →ₗ[MonoidAlgebra K G] M) := fun i =>
    { toFun := fun m => ε i • m
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun a m => by simp only [RingHom.id_apply]; exact (hlin i a m).symm }
  -- `M` is nontrivial; some block idempotent acts nontrivially.
  haveI : Nontrivial M := IsSimpleModule.nontrivial (MonoidAlgebra K G) M
  obtain ⟨m₀, hm₀⟩ : ∃ m : M, m ≠ 0 := exists_ne 0
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ε i₀ • m₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hm₀ ((hsum m₀).symm.trans (Finset.sum_eq_zero (fun i _ => h i)))
  refine ⟨i₀, ?_⟩
  -- `ε i₀` acts as the identity on all of `M` (a nonzero idempotent on a simple module).
  have hid : ∀ m : M, ε i₀ • m = m := by
    have hne : fmap i₀ ≠ 0 := fun hcontra => hi₀ (by
      have := LinearMap.congr_fun hcontra m₀; simpa [fmap] using this)
    rcases eq_bot_or_eq_top (LinearMap.range (fmap i₀)) with hbot | htop
    · exact absurd (LinearMap.range_eq_bot.mp hbot) hne
    · intro m
      obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp htop m
      have hfx : fmap i₀ (fmap i₀ x) = fmap i₀ x := hidem i₀ x
      have : fmap i₀ m = m := by rw [← hx]; exact hfx
      exact this
  -- `M` is now a simple module over the single block `R = Matrix (Fin (d i₀)) K`.
  haveI : IsArtinianRing (MonoidAlgebra K G) := IsArtinianRing.of_finite K (MonoidAlgebra K G)
  haveI := D.d_pos i₀
  have hblock : ∀ a : MonoidAlgebra K G, D.blockHom i₀ a = (D.π a) i₀ := fun _ => rfl
  have hφ_surj : Function.Surjective (D.blockHom i₀) := D.blockHom_surjective i₀
  -- `ker (blockHom i₀)` annihilates `M`, using that `ε i₀` acts as the identity.
  have hkerφ : ∀ a : MonoidAlgebra K G, D.blockHom i₀ a = 0 → ∀ m : M, a • m = 0 := by
    intro a ha m
    rw [show a • m = (a * ε i₀) • m by rw [mul_smul, hid m]]
    apply hann
    rw [map_mul, hε i₀]
    have hcol : D.π a * Pi.single i₀ (1 : Matrix (Fin (D.d i₀)) (Fin (D.d i₀)) K)
        = Pi.single i₀ (D.blockHom i₀ a) := by
      funext j
      rcases eq_or_ne j i₀ with h | h
      · subst h; simp [Pi.mul_apply, Pi.single_eq_same, hblock]
      · simp [Pi.mul_apply, Pi.single_eq_of_ne h]
    rw [hcol, ha, Pi.single_zero]
  -- Package `M` and `Std i₀` as torsion modules by `ker (blockHom i₀)`, hence modules over the
  -- block quotient `Q ≅ R`.
  have hTM : Module.IsTorsionBySet (MonoidAlgebra K G) M
      (RingHom.ker (D.blockHom i₀).toRingHom) :=
    fun x a => hkerφ (a : MonoidAlgebra K G) (RingHom.mem_ker.mp a.2) x
  have hTS : Module.IsTorsionBySet (MonoidAlgebra K G) (D.Std i₀)
      (RingHom.ker (D.blockHom i₀).toRingHom) := fun v a => by
    have ha : D.blockHom i₀ (a : MonoidAlgebra K G) = 0 := RingHom.mem_ker.mp a.2
    rw [smul_Std_eq, ha, zero_smul]
  letI hQM : Module (MonoidAlgebra K G ⧸ RingHom.ker (D.blockHom i₀).toRingHom) M := hTM.module
  letI hQS : Module (MonoidAlgebra K G ⧸ RingHom.ker (D.blockHom i₀).toRingHom) (D.Std i₀) :=
    hTS.module
  -- `Q ≅ R` is a simple artinian ring.
  let e := RingHom.quotientKerEquivOfSurjective (f := (D.blockHom i₀).toRingHom) hφ_surj
  haveI : IsSimpleRing (MonoidAlgebra K G ⧸ RingHom.ker (D.blockHom i₀).toRingHom) :=
    IsSimpleRing.of_ringEquiv e.symm inferInstance
  haveI : IsSimpleModule (MonoidAlgebra K G ⧸ RingHom.ker (D.blockHom i₀).toRingHom) M :=
    (hTM.semilinearMap.isSimpleModule_iff_of_bijective Function.bijective_id).mp inferInstance
  haveI : IsSimpleModule (MonoidAlgebra K G ⧸ RingHom.ker (D.blockHom i₀).toRingHom) (D.Std i₀) :=
    (hTS.semilinearMap.isSimpleModule_iff_of_bijective Function.bijective_id).mp
      (isSimpleModule_Std D i₀)
  -- Two simple modules over the simple artinian block quotient are isomorphic.
  obtain ⟨eQ⟩ := linearEquiv_of_isSimpleRing (R := MonoidAlgebra K G ⧸
    RingHom.ker (D.blockHom i₀).toRingHom) M (D.Std i₀)
  -- Demote the `Q`-linear equivalence to a `K[G]`-linear one (`Q`-action = `K[G]`-action mod ker).
  refine ⟨{ eQ with
    map_smul' := fun a m => by
      have h1 : a • m
          = (Ideal.Quotient.mk (RingHom.ker (D.blockHom i₀).toRingHom) a) • m :=
        (hTM.mk_smul a m).symm
      have h2 : (Ideal.Quotient.mk (RingHom.ker (D.blockHom i₀).toRingHom) a) • eQ m
          = a • eQ m := hTS.mk_smul a (eQ m)
      calc eQ (a • m)
          = eQ ((Ideal.Quotient.mk _ a) • m) := by rw [h1]
        _ = (Ideal.Quotient.mk _ a) • eQ m := eQ.map_smul _ _
        _ = a • eQ m := h2 }⟩

/-- **The count.** The number of isomorphism classes of simple `K[G]`-modules equals
the number of Wedderburn blocks `n`. -/
theorem card_simpleModuleClasses (D : SplitData K G) :
    Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra K G)) = D.n := by
  -- Package each standard module as a simple object of `ModuleCat K[G]`.
  let P : Fin D.n → (simpleProp (ModuleCat.{u} (MonoidAlgebra K G))).FullSubcategory := fun i =>
    { obj := ModuleCat.of (MonoidAlgebra K G) (D.Std i)
      property := by
        haveI := isSimpleModule_Std D i
        exact (simple_iff_isSimpleModule (M := D.Std i)).mpr inferInstance }
  let f : Fin D.n → SimpleModuleClasses.{u} (MonoidAlgebra K G) :=
    fun i => Quotient.mk (isIsomorphicSetoid _) (P i)
  have hf : Function.Bijective f := by
    constructor
    · -- Injective: `⟦Std i⟧ = ⟦Std j⟧` gives `Std i ≃ₗ Std j`, hence `i = j` (`Std_injective`).
      intro i j hij
      obtain ⟨iso⟩ := Quotient.exact hij
      exact Std_injective D i j ⟨(((simpleProp _).ι).mapIso iso).toLinearEquiv⟩
    · -- Surjective: any simple module is `≃ₗ` some `Std i` (`exists_Std_linearEquiv`).
      intro c
      obtain ⟨Q, rfl⟩ := Quotient.exists_rep c
      haveI : Simple Q.obj := Q.property
      obtain ⟨i, ⟨e⟩⟩ := exists_Std_linearEquiv D (Q.obj : Type u)
      refine ⟨i, Quotient.sound
        ⟨((simpleProp _).fullyFaithfulι).preimageIso (LinearEquiv.toModuleIso e.symm)⟩⟩
  rw [← Nat.card_fin D.n]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end SplitData

/-- Over an algebraically closed field `K` (modular case allowed), the
simple `K[G]`-modules are enumerated by a finite family of standard modules whose count equals the
number of Wedderburn blocks of `K[G] ⧸ rad`. -/
theorem exists_splitSimples_count (K : Type u) (G : Type v)
    [Field K] [IsAlgClosed K] [Group G] [Fintype G] :
    ∃ (D : SplitData K G), Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra K G)) = D.n :=
  ⟨SplitData.of, SplitData.card_simpleModuleClasses _⟩

end Etingof.SplitSimples
