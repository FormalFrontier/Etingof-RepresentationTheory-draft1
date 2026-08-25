import EtingofRepresentationTheory.Chapter8.KoszulHomotopy
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Exactness of the augmented Koszul complex, and the Koszul resolution

`Chapter8/KoszulHomotopy.lean` produced a `k`-linear contracting homotopy of the augmented
Koszul complex

`⋯ → C₂ → C₁ → C₀ --ε--> k → 0`,   `Cᵢ = SV ⊗[k] ⋀ⁱ V`,

namely `Etingof.koszulH` together with the splitting `Etingof.koszulEta` of the augmentation,
satisfying `d h + h d = id` in positive degrees and `d h + η ε = id` in degree zero. This file
turns that into the statement Problem 8.2.10(i) actually asks for: the augmented complex is
**exact**, so `C_•` is a free resolution of `k`.

The homotopy is only `k`-linear — no `SV`-linear contracting homotopy can exist, since `C_•` is a
resolution of `k` and is not `SV`-split. That is harmless: exactness is a statement about the
underlying additive groups. If `d x = 0` then

`x = d (h x) + h (d x) = d (h x) ∈ range d`,

and the ranges and kernels involved are `SV`-submodules because `d` and `ε` are `SV`-linear, even
though the witness `h x` is produced by a merely `k`-linear map.

## Main results

* `Etingof.koszulD_range_eq_ker` — `range dᵢ₊₁ = ker dᵢ`, exactness in positive degrees.
* `Etingof.koszulD_zero_range_eq_ker_koszulAug` — `range d₀ = ker ε`, exactness at `C₀`.
* `Etingof.koszulComplex_exactAt_succ` — the same, as `HomologicalComplex.ExactAt`.
* `Etingof.koszulPi` — the augmentation as a chain map `C_• ⟶ k[0]`, and
  `Etingof.koszulPi_quasiIso`, which says it is a quasi-isomorphism.
* `Etingof.koszulResolution` — **the Koszul resolution**: the whole package, as a
  `CategoryTheory.ProjectiveResolution (ModuleCat.of SV (Etingof.KoszulAugModule k V))`. Its terms
  are free, not merely projective (`Etingof.koszulXBasis`), which is the "(in fact, free)" of the
  problem statement.
* `Etingof.koszulResolutionOfFiniteDimensional` — the same under the book's hypothesis, `V` a
  finite dimensional vector space over a field.
-/

universe u v w

open scoped TensorProduct

namespace Etingof

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]
variable {κ : Type w} [LinearOrder κ] [Fintype κ]

/-! ### Exactness as an identity of `SV`-submodules -/

/-- **Exactness of the Koszul complex in positive degrees**: `range dᵢ₊₁ = ker dᵢ`.

`⊆` is `d ∘ d = 0`. For `⊇`, the contracting homotopy exhibits an explicit preimage: a cycle `x`
satisfies `x = d (h x) + h (d x) = d (h x)`. The homotopy is only `k`-linear, but both sides of
the equation are `SV`-submodules of `Cᵢ₊₁` regardless, since `d` is `SV`-linear. -/
theorem koszulD_range_eq_ker (b : Module.Basis κ k V) (i : ℕ) :
    LinearMap.range (koszulD b (i + 1)) = LinearMap.ker (koszulD b i) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, koszulD_comp_koszulD b i,
      LinearMap.zero_apply]
  · refine ⟨koszulH b (i + 1) x, ?_⟩
    have h := koszulD_koszulH_add_koszulH_koszulD b i x
    rwa [LinearMap.mem_ker.mp hx, map_zero, add_zero] at h

/-- **Exactness of the augmented Koszul complex at `C₀`**: `range d₀ = ker ε`.

Together with `Etingof.koszulAug_surjective` and `Etingof.koszulD_range_eq_ker` this is the whole
of "the augmented complex `⋯ → C₁ → C₀ → k → 0` is exact". -/
theorem koszulD_zero_range_eq_ker_koszulAug (b : Module.Basis κ k V) :
    LinearMap.range (koszulD b 0) = LinearMap.ker (koszulAug k V) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, koszulAug_comp_koszulD b,
      LinearMap.zero_apply]
  · refine ⟨koszulH b 0 x, ?_⟩
    have h := koszulD_koszulH_add_eta_aug b x
    rwa [LinearMap.mem_ker.mp hx, map_zero, add_zero] at h

omit [Fintype κ] in
/-- Freeness of the Koszul terms, in the form needed below: a basis of `V` is all one needs, no
separate `Module.Free k V` hypothesis. -/
theorem koszulX_free_of_basis (b : Module.Basis κ k V) (i : ℕ) :
    Module.Free (SymmetricAlgebra k V) (koszulX k V i) :=
  Module.Free.of_basis (koszulXBasis k V b i)

/-! ### The categorical package -/

section Resolution

open CategoryTheory Limits

variable (b : Module.Basis κ k V)

/-- Each term of `Etingof.koszulComplex` is a projective object of `ModuleCat SV` — indeed a free
module, by `Etingof.koszulXBasis`. Not an `instance`: it needs the basis `b`, which typeclass
inference cannot supply. -/
theorem koszulComplex_projective_X (i : ℕ) : Projective ((koszulComplex b).X i) :=
  haveI := koszulX_free_of_basis b i
  inferInstanceAs
    (Projective (ModuleCat.of (SymmetricAlgebra k V) (koszulX k V i)))

/-- **The augmentation as a chain map** `C_• ⟶ k[0]`, where `k` carries the trivial `SV`-action.
This is the `π` datum of the Koszul resolution; it is a chain map precisely because
`ε ∘ d₀ = 0` (`Etingof.koszulAug_comp_koszulD`). -/
noncomputable def koszulPi :
    koszulComplex b ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} (SymmetricAlgebra k V))).obj
        (ModuleCat.of _ (KoszulAugModule k V)) :=
  (ChainComplex.toSingle₀Equiv (koszulComplex b)
      (ModuleCat.of (SymmetricAlgebra k V) (KoszulAugModule k V))).symm
    ⟨ModuleCat.ofHom (koszulAug k V), by
      rw [koszulComplex_d b 0]
      ext x
      exact LinearMap.congr_fun (koszulAug_comp_koszulD b) x⟩

omit [LinearOrder κ] in
@[simp]
theorem koszulPi_f_zero :
    (koszulPi b).f 0 = ModuleCat.ofHom (koszulAug k V) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **The Koszul complex is exact in every positive degree.** This is
`Etingof.koszulD_range_eq_ker` transported into `HomologicalComplex.ExactAt`. -/
theorem koszulComplex_exactAt_succ (i : ℕ) : (koszulComplex b).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hf : ((koszulComplex b).sc' (i + 2) (i + 1) i).f
      = ModuleCat.ofHom (koszulD b (i + 1)) := koszulComplex_d b (i + 1)
  have hg : ((koszulComplex b).sc' (i + 2) (i + 1) i).g
      = ModuleCat.ofHom (koszulD b i) := koszulComplex_d b i
  intro x hx
  rw [hg] at hx
  refine ⟨koszulH b (i + 1) x, ?_⟩
  rw [hf]
  change koszulD b i x = 0 at hx
  change koszulD b (i + 1) (koszulH b (i + 1) x) = x
  have h := koszulD_koszulH_add_koszulH_koszulD b i x
  rwa [hx, map_zero, add_zero] at h

/-- The augmented degree-zero short complex `C₁ → C₀ → k` is exact: this is
`Etingof.koszulD_zero_range_eq_ker_koszulAug` in `ShortComplex` form. -/
theorem koszulAug_shortComplex_exact :
    (ShortComplex.moduleCatMk (koszulD b 0) (koszulAug k V)
      (koszulAug_comp_koszulD b)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  refine ⟨koszulH b 0 x, ?_⟩
  change koszulAug k V x = 0 at hx
  change koszulD b 0 (koszulH b 0 x) = x
  have h := koszulD_koszulH_add_eta_aug b x
  rwa [hx, map_zero, add_zero] at h

/-- **The augmentation is a quasi-isomorphism.** In positive degrees both complexes are exact
(`Etingof.koszulComplex_exactAt_succ` for the source, and `k[0]` trivially); in degree zero the
augmentation presents `k` as the cokernel of `d₀`, being surjective
(`Etingof.koszulAug_surjective`) with kernel exactly the boundaries
(`Etingof.koszulD_zero_range_eq_ker_koszulAug`). -/
theorem koszulPi_quasiIso : QuasiIso (koszulPi b) := by
  rw [quasiIso_iff]
  rintro (_ | i)
  · have hepi : Epi (ShortComplex.moduleCatMk (koszulD b 0) (koszulAug k V)
        (koszulAug_comp_koszulD b)).g := by
      rw [show (ShortComplex.moduleCatMk (koszulD b 0) (koszulAug k V)
        (koszulAug_comp_koszulD b)).g = ModuleCat.ofHom (koszulAug k V) from rfl,
        ModuleCat.epi_iff_surjective]
      exact koszulAug_surjective
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)).2
        ⟨koszulAug_shortComplex_exact b, hepi⟩
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact koszulComplex_exactAt_succ b i

/-- **The Koszul resolution** of Problem 8.2.10(i): `C_• = SV ⊗ ⋀^• V` is a free — in particular
projective — resolution of `k` as an `SV`-module, `k` carrying the trivial action of `V`.

The three ingredients are `Etingof.koszulComplex` (the complex, with `d ∘ d = 0`), freeness of
the terms via the base-changed basis `Etingof.koszulXBasis`, and the augmentation
`Etingof.koszulPi`, a quasi-isomorphism because the augmented complex admits the `k`-linear
contracting homotopy `Etingof.koszulH`. -/
noncomputable def koszulResolution :
    ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k V) (KoszulAugModule k V)) where
  complex := koszulComplex b
  π := koszulPi b
  projective i := koszulComplex_projective_X b i
  quasiIso := koszulPi_quasiIso b

@[simp]
theorem koszulResolution_complex : (koszulResolution b).complex = koszulComplex b := rfl

@[simp]
theorem koszulResolution_π : (koszulResolution b).π = koszulPi b := rfl

/-- Every term of the Koszul resolution is a *free* `SV`-module, not merely projective — the
parenthetical "(in fact, free)" of Problem 8.2.10(i). -/
theorem koszulResolution_free (i : ℕ) :
    Module.Free (SymmetricAlgebra k V) ((koszulResolution b).complex.X i) :=
  koszulX_free_of_basis b i

end Resolution

/-! ### The book's hypothesis: `V` a finite dimensional vector space -/

/-- **The Koszul resolution of a finite dimensional vector space**, the exact hypothesis of
Problem 8.2.10: `V` finite dimensional over a field `k`. This is `Etingof.koszulResolution` for the
basis `Module.finBasis k V`; by `Etingof.koszulComplex_eq_of_basis` the underlying complex does not
depend on that choice. -/
noncomputable def koszulResolutionOfFiniteDimensional (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    CategoryTheory.ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k V) (KoszulAugModule k V)) :=
  koszulResolution (Module.finBasis k V)

end Etingof
