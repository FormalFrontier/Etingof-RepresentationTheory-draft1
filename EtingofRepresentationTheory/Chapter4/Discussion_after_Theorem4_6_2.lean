import Mathlib
import EtingofRepresentationTheory.Chapter4.Theorem4_6_2

/-!
# Discussion after Theorem 4.6.2: the conjugate representation `V̄ ≅ V*`

For a finite-dimensional complex representation `V` of a finite group `G`, the
**complex conjugate representation** `V̄` has the same underlying additive group,
the same `G`-action, but the conjugate scalar multiplication `z •_{V̄} v = z̄ • v`.
Theorem 4.6.2 (the existence of a `G`-invariant positive definite Hermitian form,
a unitary structure) shows that `V̄` is isomorphic to the dual representation `V*`.

A homomorphism of representations `V̄ → V*` is the same data as an invariant
sesquilinear form on `V` (additive on both arguments, linear on the first and
antilinear on the second); an isomorphism corresponds to a *nondegenerate* one.
A unitary structure on `V` supplies such a nondegenerate invariant form, namely
`(v, w) ↦ c(v, w)` for the invariant inner product `c`, giving the isomorphism.

## Main definitions and results

* `Etingof.Conjugate V` — the conjugate `ℂ`-vector space (a type synonym of `V`
  carrying the conjugate scalar action via `Module.compHom`).
* `Etingof.conjugateRep ρ` — the conjugate representation `V̄`, a genuine
  `Representation ℂ G (Conjugate V)` with the same underlying `G`-action as `ρ`.
* `Etingof.conjEquivDual c` — the `ℂ`-linear equivalence `V̄ ≃ₗ[ℂ] V*` attached
  to a positive definite Hermitian form `c`, built from the conjugate-linear
  `V ≃ₛₗ V*` of Theorem 4.6.2.
* `Etingof.conjugate_iso_dual` — for a finite-dimensional complex representation of
  a finite group, there is a `G`-equivariant `ℂ`-linear isomorphism `V̄ ≅ V*`.

## Mathlib correspondence

The conjugate scalar action reuses `Module.compHom` with `starRingEnd ℂ`. The
nondegenerate form and the equivalence `V ≃ₛₗ V*` are supplied by
`Etingof.Theorem4_6_2`. Not otherwise in Mathlib.
-/

namespace Etingof

open scoped ComplexConjugate

universe u

variable {G : Type*} [Group G]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The complex conjugate vector space of `V`: the same underlying additive group,
but with the conjugate scalar multiplication `z • v = z̄ • v`. Implemented as a type
synonym of `V` carrying the `Module ℂ`-structure pulled back along the conjugation
ring homomorphism `starRingEnd ℂ`. -/
def Conjugate (V : Type u) : Type u := V

namespace Conjugate

instance : AddCommGroup (Conjugate V) := inferInstanceAs (AddCommGroup V)

/-- The conjugate scalar action `z • v = z̄ • v`, pulled back along the conjugation
ring homomorphism `starRingEnd ℂ`. -/
noncomputable instance : Module ℂ (Conjugate V) := Module.compHom V (starRingEnd ℂ)

/-- The conjugate scalar action computed on the underlying space `V`. -/
lemma smul_def (z : ℂ) (v : Conjugate V) :
    z • v = (starRingEnd ℂ) z • (show V from v) := rfl

end Conjugate

/-- The complex conjugate representation `V̄` of a representation `ρ`: the same
underlying additive group and `G`-action, but the conjugate scalar action.
A `ℂ`-linear map is automatically linear for the conjugate scalar action, so each
`ρ g` is again `ℂ`-linear on `Conjugate V`. -/
noncomputable def conjugateRep (ρ : Representation ℂ G V) :
    Representation ℂ G (Conjugate V) where
  toFun g :=
    { toFun := fun v => ρ g v
      map_add' := fun v w => map_add (ρ g) v w
      map_smul' := fun r v => by
        simp only [RingHom.id_apply, Conjugate.smul_def, map_smul] }
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one]; rfl
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]; rfl

@[simp] lemma conjugateRep_apply (ρ : Representation ℂ G V) (g : G) (v : Conjugate V) :
    conjugateRep ρ g v = ρ g v := rfl

variable [FiniteDimensional ℂ V]

/-- The `ℂ`-linear equivalence `V̄ ≃ₗ[ℂ] V*` attached to a positive definite Hermitian
form `c` on `V`. As a map it sends `v` to the functional `w ↦ c(v, w)`; this is
conjugate-linear in `v` as a map out of `V`, hence genuinely `ℂ`-linear out of the
conjugate space `V̄`. It is bijective because `c` is nondegenerate (Theorem 4.6.2). -/
noncomputable def conjEquivDual (c : InnerProductSpace.Core ℂ V) :
    Conjugate V ≃ₗ[ℂ] Module.Dual ℂ V :=
  { toFun := fun v => Theorem4_6_2.innerEquivDual c v
    map_add' := fun v v' => (Theorem4_6_2.innerEquivDual c).map_add v v'
    map_smul' := fun r v => by
      simp only [RingHom.id_apply]
      rw [Conjugate.smul_def, map_smulₛₗ]
      simp
    invFun := fun f => (Theorem4_6_2.innerEquivDual c).symm f
    left_inv := fun v => (Theorem4_6_2.innerEquivDual c).left_inv v
    right_inv := fun f => (Theorem4_6_2.innerEquivDual c).right_inv f }

@[simp] lemma conjEquivDual_apply (c : InnerProductSpace.Core ℂ V) (v : Conjugate V) (w : V) :
    conjEquivDual c v w = c.inner v w := rfl

/-- For an invariant form `c`, the equivalence `conjEquivDual c` intertwines the conjugate
representation `V̄` with the dual representation `V*`: it is a homomorphism of
representations. -/
theorem conjEquivDual_intertwines (ρ : Representation ℂ G V)
    (c : InnerProductSpace.Core ℂ V)
    (hc : ∀ (g : G) (v w : V), c.inner (ρ g v) (ρ g w) = c.inner v w)
    (g : G) (v : Conjugate V) :
    conjEquivDual c (conjugateRep ρ g v) = (Representation.dual ρ) g (conjEquivDual c v) := by
  ext w
  -- `LHS w = c(ρ g v, w)` and `RHS w = (conjEquivDual c v)(ρ g⁻¹ w) = c(v, ρ g⁻¹ w)`.
  change c.inner (ρ g v) w = c.inner v (ρ g⁻¹ w)
  have hw : ρ g (ρ g⁻¹ w) = w := by
    have h : ρ g (ρ g⁻¹ w) = ρ (g * g⁻¹) w := by rw [map_mul]; rfl
    rw [h, mul_inv_cancel, map_one]; rfl
  calc c.inner (ρ g v) w
      = c.inner (ρ g v) (ρ g (ρ g⁻¹ w)) := by rw [hw]
    _ = c.inner v (ρ g⁻¹ w) := hc g v (ρ g⁻¹ w)

set_option linter.unusedFintypeInType false in
/-- **Conjugate representation is isomorphic to the dual** (Etingof, discussion after
Theorem 4.6.2). For a finite-dimensional complex representation `ρ` of a finite group
`G`, there is a `G`-equivariant `ℂ`-linear isomorphism between the conjugate
representation `V̄` and the dual representation `V*`. The isomorphism is supplied by a
`G`-invariant positive definite Hermitian form (the unitary structure of Theorem 4.6.2),
viewed as a nondegenerate invariant sesquilinear form. -/
theorem conjugate_iso_dual [Fintype G] (ρ : Representation ℂ G V) :
    ∃ e : Conjugate V ≃ₗ[ℂ] Module.Dual ℂ V,
      ∀ (g : G) (v : Conjugate V),
        e (conjugateRep ρ g v) = (Representation.dual ρ) g (e v) := by
  obtain ⟨c, hc⟩ := Theorem4_6_2_existence G V ρ
  exact ⟨conjEquivDual c, conjEquivDual_intertwines ρ c hc⟩

end Etingof
