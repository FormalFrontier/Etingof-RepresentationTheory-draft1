import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Definition 6.6.4: Reflection Functor F⁻ᵢ (at a Source)

Let Q be a quiver and i ∈ Q be a source. Let ψ : V_i → ⊕_{i→j} V_j be the
canonical map. The reflection functor F⁻ᵢ : Rep Q → Rep Q̄ᵢ is defined by:
- F⁻ᵢ(V)_k = V_k for k ≠ i
- F⁻ᵢ(V)_i = Coker(ψ) = (⊕_{i→j} V_j) / Im ψ

All maps now pointing into i are replaced by the compositions of the inclusions
V_k → ⊕_{i→j} V_j with the natural quotient map ⊕_{i→j} V_j → (⊕_{i→j} V_j)/Im ψ.

## Mathlib correspondence

BGP reflection functors are not in Mathlib. The cokernel-based construction uses
`Submodule.mkQ` for quotient maps and `LinearMap.range` for image.
-/

/-- The type indexing the direct sum for F⁻ᵢ: pairs (j, h) where h : i ⟶ j is an arrow
out of the source vertex i. -/
def Etingof.ArrowsOutOf (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (i ⟶ j)

/-- Over a field, any `AddCommMonoid` module is actually an `AddCommGroup`, with negation
given by scalar multiplication by `-1`. This bridges `QuiverRepresentation` (which uses
`AddCommMonoid`) and APIs like `Submodule.mkQ` (which require `AddCommGroup`).
The resulting `AddCommGroup` extends the existing `AddCommMonoid` — no diamond. -/
noncomputable def Etingof.addCommGroupOfField' {k : Type*} [Field k] {M : Type*}
    [inst : AddCommMonoid M] [Module k M] : AddCommGroup M :=
  { inst with
    neg := fun x => (-1 : k) • x
    zsmul := fun n x => (n : k) • x
    neg_add_cancel := fun a => by
      change (-1 : k) • a + a = 0
      nth_rw 2 [show a = (1 : k) • a from (one_smul k a).symm]
      rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul_zero' := fun a => by simp [zero_smul]
    zsmul_succ' := fun n a => by
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
    zsmul_neg' := fun n a => by
      simp only [Int.negSucc_eq, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_neg, smul_smul, neg_one_mul] }

/-- The reflection functor F⁻ᵢ at a source vertex i, sending representations of Q
to representations of Q̄ᵢ (the quiver with arrows at i reversed).

At vertex k ≠ i, F⁻ᵢ(ρ)_k = ρ_k (unchanged).
At vertex i, F⁻ᵢ(ρ)_i = coker(ψ) where ψ : ρ_i → ⊕_{i→j} ρ_j is the sum of
the representation maps ρ(h) for each arrow h : i → j.

The linear maps in the reversed quiver Q̄ᵢ are:
- For arrows not touching i: unchanged from ρ
- For arrows into i in Q̄ᵢ (= reversed arrows out of i in Q):
  ρ_j → ⊕_{i→j} ρ_j → coker(ψ) (inclusion then quotient)

(Etingof Definition 6.6.4) -/
noncomputable def Etingof.reflectionFunctorMinus
    {k : Type*} [Field k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSource V i)
    (ρ : Etingof.QuiverRepresentation k V)
    [Fintype (Etingof.ArrowsOutOf V i)] :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) := by
  classical
  -- Upgrade AddCommMonoid to AddCommGroup using field negation (extends existing ACM)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField' (k := k)
  exact
  -- The source map ψ : ρ.obj i →ₗ[k] ⊕_{i→j} ρ.obj j
  let ψ : ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1) :=
    ∑ a : Etingof.ArrowsOutOf V i,
      (DirectSum.lof k (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1) a).comp (ρ.mapLinear a.2)
  -- Use Decidable.casesOn for coherent type-level case split (same pattern as F⁺ᵢ)
  let dp : ∀ v, Decidable (v = i) := fun v => inst v i
  let objAt : ∀ v, Decidable (v = i) → Type _ :=
    fun v d => @Decidable.casesOn _ (fun _ => Type _) d
      (fun _ => ρ.obj v)
      (fun _ => (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) ⧸ LinearMap.range ψ)
  let acmAt : ∀ v d, AddCommMonoid (objAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => AddCommMonoid (objAt v d)) d
      (fun _ => ρ.instAddCommMonoid v)
      (fun _ => inferInstance)
  let modAt : ∀ v d, @Module k (objAt v d) _ (acmAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => @Module k (objAt v d) _ (acmAt v d)) d
      (fun _ => ρ.instModule v)
      (fun _ => inferInstance)
  @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => objAt v (dp v))
    (fun v => acmAt v (dp v))
    (fun v => modAt v (dp v))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) => by
      change Etingof.ReversedAtVertexHom V i a b at e
      unfold Etingof.ReversedAtVertexHom at e
      by_cases ha : a = i
      · by_cases hb : b = i
        · -- a = i, b = i: self-loop; vacuous since i is a source
          simp only [ha, hb] at e; exact ((hi i).false e).elim
        · -- a = i, b ≠ i: (b ⟶ i) in Q; vacuous since i is a source
          simp only [ha, hb, ite_true, ite_false] at e
          exact ((hi b).false e).elim
      · by_cases hb : b = i
        · -- a ≠ i, b = i: reversed arrow (i ⟶ a) in Q
          -- Map: ρ.obj a → ⊕_{i→j} ρ.obj j → coker(ψ) via inclusion then quotient
          -- The intended map is (Submodule.mkQ (range ψ)).comp (DirectSum.lof ⟨a, e⟩)
          -- Type coercion between the if-else dependent types uses sorry (same as F⁺ᵢ)
          exact sorry
        · -- a ≠ i, b ≠ i: unchanged arrow
          -- The intended map is ρ.mapLinear e
          -- Type coercion between the if-else dependent types uses sorry (same as F⁺ᵢ)
          exact sorry)
