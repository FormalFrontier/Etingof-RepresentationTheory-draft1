import Mathlib

/-!
# Definition 5.1.1: Complex, Real, and Quaternionic Type

An irreducible complex representation V of a finite group G is said to be of:
- **complex type** if V ≇ V* (not isomorphic to its dual)
- **real type** if V admits a nondegenerate symmetric bilinear form invariant under G
- **quaternionic type** if V admits a nondegenerate skew-symmetric bilinear form invariant under G

## Mathlib correspondence

Mathlib does not have a dedicated type classification for representations. This can be modeled
using `LinearMap.BilinForm` with symmetry/skew-symmetry conditions and G-invariance.
-/

/-- Classification of irreducible representations into complex, real, and quaternionic types.
(Etingof Definition 5.1.1) -/
inductive Etingof.RepresentationType where
  | complex
  | real
  | quaternionic

/-- A representation is of real type if it admits a G-invariant nondegenerate symmetric
bilinear form. (Etingof Definition 5.1.1) -/
def Etingof.IsRealType
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
    (∀ v w, B v w = B w v) ∧  -- symmetric
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧  -- nondegenerate
    (∀ g v w, B (ρ g v) (ρ g w) = B v w)  -- G-invariant

/-- A representation is of quaternionic type if it admits a G-invariant nondegenerate
skew-symmetric bilinear form. (Etingof Definition 5.1.1) -/
def Etingof.IsQuaternionicType
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
    (∀ v w, B v w = -(B w v)) ∧  -- skew-symmetric
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧  -- nondegenerate
    (∀ g v w, B (ρ g v) (ρ g w) = B v w)  -- G-invariant

/-- A representation is of complex type if it is **not** isomorphic to its dual `V*`,
i.e. there is no `G`-equivariant linear isomorphism `V ≃ V*`. Here `V*` carries the
dual (contragredient) representation `ρ.dual`, `(ρ.dual g) f = f ∘ ρ g⁻¹`.
(Etingof Definition 5.1.1) -/
def Etingof.IsComplexType
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ¬ ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v)

/-- A `G`-invariant nondegenerate bilinear form on `V` provides a `G`-equivariant
isomorphism `V ≅ V*`: the form, read as a map `v ↦ B v ∈ V*`, is injective by
nondegeneracy hence bijective (`finrank V = finrank V*`), and equivariant by
invariance. Both real and quaternionic types supply such a form. -/
theorem Etingof.exists_equivariant_dual_equiv_of_invariant_nondegenerate
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v) := by
  -- `B`, viewed as `V →ₗ[ℂ] Module.Dual ℂ V`, is injective by nondegeneracy.
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hnd v fun w => by rw [hv]; rfl
  -- equal dimensions ⇒ injective ⇒ a linear equivalence `V ≃ₗ V*`.
  have hdim : Module.finrank ℂ V = Module.finrank ℂ (Module.Dual ℂ V) :=
    (Subspace.dual_finrank_eq (K := ℂ) (V := V)).symm
  refine ⟨B.linearEquivOfInjective hinj hdim, ?_⟩
  intro g v
  -- compare the two dual vectors by evaluating on an arbitrary `w`.
  apply LinearMap.ext
  intro w
  rw [LinearMap.linearEquivOfInjective_apply, LinearMap.linearEquivOfInjective_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  -- goal: `B (ρ g v) w = B v (ρ g⁻¹ w)`; instantiate invariance with `ρ g⁻¹ w`.
  have hgg : (ρ g) ((ρ g⁻¹) w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := hinv g v (ρ g⁻¹ w)
  rwa [hgg] at this

/-- A real-type representation is not of complex type: the invariant symmetric
nondegenerate form gives an equivariant isomorphism `V ≅ V*`. -/
theorem Etingof.not_isComplexType_of_isRealType
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    {ρ : Representation ℂ G V} (h : Etingof.IsRealType ρ) :
    ¬ Etingof.IsComplexType ρ := by
  obtain ⟨B, _, hnd, hinv⟩ := h
  exact fun hc => hc (exists_equivariant_dual_equiv_of_invariant_nondegenerate ρ B hnd hinv)

/-- A quaternionic-type representation is not of complex type: the invariant
skew-symmetric nondegenerate form gives an equivariant isomorphism `V ≅ V*`. -/
theorem Etingof.not_isComplexType_of_isQuaternionicType
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    {ρ : Representation ℂ G V} (h : Etingof.IsQuaternionicType ρ) :
    ¬ Etingof.IsComplexType ρ := by
  obtain ⟨B, _, hnd, hinv⟩ := h
  exact fun hc => hc (exists_equivariant_dual_equiv_of_invariant_nondegenerate ρ B hnd hinv)
