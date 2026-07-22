import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Defs

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

The cokernel construction (quotient module) requires `AddCommGroup` and `Ring`
structure. The definition requires `[CommRing k]` and constructs compatible
`AddCommGroup` instances internally using scalar multiplication by `-1`.
-/

universe u_k u_V u_obj u_hom

/-- The type indexing the direct sum for F⁻ᵢ: pairs (j, h) where h : i ⟶ j is an arrow
out of the source vertex i. -/
def Etingof.ArrowsOutOf (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (i ⟶ j)

/-- Over a commutative ring, any `AddCommMonoid` module is actually an `AddCommGroup`,
with negation given by scalar multiplication by `-1`. The resulting `AddCommGroup`
extends the existing `AddCommMonoid` — no diamond.

This is useful since `QuiverRepresentation` uses `AddCommMonoid` but many APIs
(e.g. `Submodule.exists_isCompl`) require `AddCommGroup`. -/
noncomputable def Etingof.addCommGroupOfRing {k : Type*} [CommRing k] {M : Type*}
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

/-- The canonical map ψ : V_i → ⊕_{i→j} V_j at a source vertex i. -/
noncomputable def Etingof.QuiverRepresentation.sourceMap
    {k : Type*} [CommRing k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) := by
  classical
  exact ∑ a : Etingof.ArrowsOutOf Q i,
    (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) a).comp
      (ρ.mapLinear a.2)

/-- The vertex-space type family of `reflectionFunctorMinus`, with the `Decidable`
discriminant exposed as an explicit argument `d`. At `d = .isFalse _` this is
`ρ.obj v`; at `d = .isTrue _` it is the cokernel of `sourceMap i`. -/
def Etingof.reflFunctorMinus_objAt
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) (i v : V)
    [Fintype (Etingof.ArrowsOutOf V i)] (d : Decidable (v = i)) :
    Type (max u_V u_obj u_hom) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  @Decidable.casesOn _ (fun _ => Type (max u_V u_obj u_hom)) d
    (fun _ => ρ.obj v)
    (fun _ =>
      (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.sourceMap i))

/-- `AddCommMonoid` on `reflFunctorMinus_objAt`, with the discriminant `d` explicit. -/
noncomputable def Etingof.reflFunctorMinus_acmAt
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) (i v : V)
    [Fintype (Etingof.ArrowsOutOf V i)] (d : Decidable (v = i)) :
    AddCommMonoid (Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i v d) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  @Decidable.casesOn _
    (fun d => AddCommMonoid (Etingof.reflFunctorMinus_objAt ρ i v d)) d
    (fun _ => ρ.instAddCommMonoid v)
    (fun _ => Submodule.Quotient.addCommGroup (p := LinearMap.range (ρ.sourceMap i))
      |>.toAddCommMonoid)

/-- `Module` on `reflFunctorMinus_objAt`, with the discriminant `d` explicit. -/
noncomputable def Etingof.reflFunctorMinus_modAt
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) (i v : V)
    [Fintype (Etingof.ArrowsOutOf V i)] (d : Decidable (v = i)) :
    @Module k (Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i v d) _
      (Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ i v d) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  @Decidable.casesOn _
    (fun d => @Module k (Etingof.reflFunctorMinus_objAt ρ i v d) _
      (Etingof.reflFunctorMinus_acmAt ρ i v d)) d
    (fun _ => ρ.instModule v)
    (fun _ => Submodule.Quotient.module (LinearMap.range (ρ.sourceMap i)))

/-- The `mapLinear` field of `reflectionFunctorMinus`, with both discriminants explicit. -/
noncomputable def Etingof.reflFunctorMinus_mapAt
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) {i : V}
    (hi : Etingof.IsSource V i)
    [Fintype (Etingof.ArrowsOutOf V i)] (a b : V)
    (da : Decidable (a = i)) (db : Decidable (b = i)) :
    letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ i a da
    letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ i b db
    letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ i a da
    letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ i b db
    Etingof.reflFunctorPlus_arrowAt i a b da db →
      (Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i a da →ₗ[k]
        Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i b db) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  letI : DecidableEq (Etingof.ArrowsOutOf V i) := Classical.decEq _
  @Decidable.casesOn (a = i)
    (fun da =>
      letI := Etingof.reflFunctorMinus_acmAt ρ i a da
      letI := Etingof.reflFunctorMinus_acmAt ρ i b db
      letI := Etingof.reflFunctorMinus_modAt ρ i a da
      letI := Etingof.reflFunctorMinus_modAt ρ i b db
      Etingof.reflFunctorPlus_arrowAt i a b da db →
        (Etingof.reflFunctorMinus_objAt ρ i a da →ₗ[k]
          Etingof.reflFunctorMinus_objAt ρ i b db))
    da
    (fun ha_ne => @Decidable.casesOn (b = i)
      (fun db =>
        letI := Etingof.reflFunctorMinus_acmAt ρ i b db
        letI := Etingof.reflFunctorMinus_modAt ρ i b db
        Etingof.reflFunctorPlus_arrowAt i a b (.isFalse ha_ne) db →
          (ρ.obj a →ₗ[k] Etingof.reflFunctorMinus_objAt ρ i b db))
      db
      (fun _hb_ne => fun e => ρ.mapLinear e)
      (fun _hb_eq => fun e =>
        (Submodule.mkQ (LinearMap.range (ρ.sourceMap i))).comp
          (DirectSum.lof k (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1) ⟨a, e⟩)))
    (fun ha_eq => @Decidable.casesOn (b = i)
      (fun db =>
        letI := Etingof.reflFunctorMinus_acmAt ρ i a (.isTrue ha_eq)
        letI := Etingof.reflFunctorMinus_acmAt ρ i b db
        letI := Etingof.reflFunctorMinus_modAt ρ i a (.isTrue ha_eq)
        letI := Etingof.reflFunctorMinus_modAt ρ i b db
        Etingof.reflFunctorPlus_arrowAt i a b (.isTrue ha_eq) db →
          (Etingof.reflFunctorMinus_objAt ρ i a (.isTrue ha_eq) →ₗ[k]
            Etingof.reflFunctorMinus_objAt ρ i b db))
      db
      (fun _hb_ne => fun e => ((hi b).false e).elim)
      (fun hb_eq => fun e => ((hi a).false (show a ⟶ i by exact hb_eq ▸ e)).elim))

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
    {k : Type*} [CommRing k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSource V i)
    (ρ : Etingof.QuiverRepresentation k V)
    [Fintype (Etingof.ArrowsOutOf V i)] :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) :=
  @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => Etingof.reflFunctorMinus_objAt ρ i v (inst v i))
    (fun v => Etingof.reflFunctorMinus_acmAt ρ i v (inst v i))
    (fun v => Etingof.reflFunctorMinus_modAt ρ i v (inst v i))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) =>
      Etingof.reflFunctorMinus_mapAt ρ hi a b (inst a i) (inst b i) e)

section ReflectionFunctorMinusAPI

/-! ## API for `reflectionFunctorMinus`

Dual of the `reflectionFunctorPlus` API. Provides `LinearEquiv`s that reduce
the `Decidable.casesOn` in the definition of `reflectionFunctorMinus`. -/

/-- At a vertex v ≠ i, the type `F⁻ᵢ(ρ).obj v` is propositionally equal to `ρ.obj v`. -/
theorem Etingof.reflFunctorMinus_obj_ne
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v = ρ.obj v := by
  unfold Etingof.reflectionFunctorMinus Etingof.reflFunctorMinus_objAt
  simp only []
  match hd : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ => rw [hd]

/-- At vertex i, the type `F⁻ᵢ(ρ).obj i` is propositionally equal to the cokernel
of `sourceMap i`. -/
theorem Etingof.reflFunctorMinus_obj_eq
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i =
    ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
      LinearMap.range (ρ.sourceMap i)) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  unfold Etingof.reflectionFunctorMinus Etingof.reflFunctorMinus_objAt
  simp only []
  match hd : (‹DecidableEq Q› i i) with
  | .isTrue _ => rw [hd]
  | .isFalse hii => exact absurd rfl hii

/-- The vertex equivalence at `v ≠ i`, with the `Decidable` discriminant exposed as an
explicit argument `d`. At `d = .isFalse _` this is the identity on `ρ.obj v`. -/
noncomputable def Etingof.reflFunctorMinus_equivAtAt_ne
    {k : Type u_k} [CommRing k] {Q : Type u_V} [Quiver.{u_hom} Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) (d : Decidable (v = i)) :
    letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ i v d
    letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ i v d
    Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i v d ≃ₗ[k] ρ.obj v :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ i v d
      letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ i v d
      Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i v d ≃ₗ[k] ρ.obj v)
    d
    (fun _ => LinearEquiv.refl k (ρ.obj v))
    (fun hvi => absurd hvi hv)

/-- `LinearEquiv` at vertex v ≠ i: `F⁻ᵢ(ρ).obj v ≃ₗ[k] ρ.obj v`.
This reduces the `Decidable.casesOn` in the `reflectionFunctorMinus` definition. -/
noncomputable def Etingof.reflFunctorMinus_equivAt_ne
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v ≃ₗ[k] ρ.obj v :=
  Etingof.reflFunctorMinus_equivAtAt_ne ρ v hv (inst v i)

/-- The vertex equivalence at `i`, with the `Decidable` discriminant exposed as an explicit
argument `d`. At `d = .isTrue _` this is the identity on `coker(sourceMap i)`. -/
noncomputable def Etingof.reflFunctorMinus_equivAtAt_eq
    {k : Type u_k} [CommRing k] {Q : Type u_V} [Quiver.{u_hom} Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] (d : Decidable (i = i)) :
    letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ i i d
    letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ i i d
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i i d ≃ₗ[k]
      (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.sourceMap i) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  @Decidable.casesOn (i = i)
    (fun d =>
      letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ i i d
      letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ i i d
      Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i i d ≃ₗ[k]
        (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
          LinearMap.range (ρ.sourceMap i))
    d
    (fun hii => absurd rfl hii)
    (fun _ => LinearEquiv.refl k
      ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.sourceMap i)))

/-- `LinearEquiv` at vertex i: `F⁻ᵢ(ρ).obj i ≃ₗ[k] coker(sourceMap)`.
This reduces the `Decidable.casesOn` in the `reflectionFunctorMinus` definition at vertex i.
Dual of `reflFunctorPlus_equivAt_eq`. -/
noncomputable def Etingof.reflFunctorMinus_equivAt_eq
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i ≃ₗ[k]
    (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
      LinearMap.range (ρ.sourceMap i) :=
  Etingof.reflFunctorMinus_equivAtAt_eq ρ (inst i i)

/-- For an arrow `j →_{Q̄ᵢ} i` in the reversed quiver (with i a source), the source vertex
j ≠ i. This is because i is a sink in Q̄ᵢ. -/
theorem Etingof.arrowsIntoReversed_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : @Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  intro heq; dsimp only at heq
  change Etingof.ReversedAtVertexHom Q i j i at e
  rw [Etingof.ReversedAtVertexHom_eq_eq heq rfl] at e
  exact (hi j).false (show j ⟶ i from e)

/-- Extract the original arrow i →_Q j from a reversed arrow j →_{Q̄ᵢ} i.
When i is a source, `ReversedAtVertexHom Q i j i` with j ≠ i is just `i ⟶ j` in Q. -/
def Etingof.arrowsIntoReversed_origArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : @Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i) : i ⟶ a.fst := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i j i at e
  have hne := Etingof.arrowsIntoReversed_ne hi ⟨j, e⟩
  rw [Etingof.ReversedAtVertexHom_ne_eq hne rfl] at e; exact e

set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorMinus + equivAt_ne + match reduction
/-- At non-source vertices (a ≠ i, b ≠ i), the F⁻ᵢ map equals the original ρ map,
after transport through the equivAt_ne equivalences.

Dual of `reflFunctorPlus_mapLinear_ne_ne`. -/
theorem Etingof.reflFunctorMinus_mapLinear_ne_ne
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b)
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) a) :
    (Etingof.reflFunctorMinus_equivAt_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a b e w) =
    ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e)
      ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w) := by
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
  -- (1) Function-level HEq of `mapAt` at the live discriminants vs. at the literal `isFalse`
  -- branch, where the map iota-reduces to `ρ.mapLinear`.
  have hmap : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a b e)
      (ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e)) := by
    have hf : HEq
        (Etingof.reflFunctorMinus_mapAt ρ hi a b (inst a i) (inst b i))
        (Etingof.reflFunctorMinus_mapAt ρ hi a b (.isFalse ha) (.isFalse hb)) := by
      rw [h_da, h_db]
    have he : HEq e (Etingof.reversedArrow_ne_ne ha hb e) := by
      rw [Etingof.reversedArrow_ne_ne_eq_cast ha hb]; exact (cast_heq _ _).symm
    refine Etingof.heq_apply (Etingof.ReversedAtVertexHom_ne_ne ha hb) ?_ hf he
    rw [h_da, h_db]
  -- (2) `equivAt_ne` is heterogeneously the identity (function level, via the parametrized
  -- `equivAtAt_ne` and `rw` on the discriminant).
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    show HEq (⇑(Etingof.reflFunctorMinus_equivAtAt_ne ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  -- (3) Instance HEqs to bridge `hmap` to HEq of coercions.
  have hac_a : HEq
      (Etingof.reflFunctorMinus_acmAt ρ i a (inst a i)) (ρ.instAddCommMonoid a) := by
    rw [h_da]; rfl
  have hac_b : HEq
      (Etingof.reflFunctorMinus_acmAt ρ i b (inst b i)) (ρ.instAddCommMonoid b) := by
    rw [h_db]; rfl
  have hmo_a : HEq
      (Etingof.reflFunctorMinus_modAt ρ i a (inst a i)) (ρ.instModule a) := by
    rw [h_da]; rfl
  have hmo_b : HEq
      (Etingof.reflFunctorMinus_modAt ρ i b (inst b i)) (ρ.instModule b) := by
    rw [h_db]; rfl
  have hmapcoe : HEq
      (⇑(@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a b e))
      (⇑(ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e))) :=
    Etingof.heq_linearMap_coe
      (Etingof.reflFunctorMinus_obj_ne hi ρ a ha)
      (Etingof.reflFunctorMinus_obj_ne hi ρ b hb)
      hac_a hac_b hmo_a hmo_b hmap
  -- (4) Assemble via HEq congruence.
  have hwa : HEq ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w) w :=
    (Etingof.heq_apply (Etingof.reflFunctorMinus_obj_ne hi ρ a ha) rfl (heqv a ha)
      (cast_heq (Etingof.reflFunctorMinus_obj_ne hi ρ a ha) w).symm).trans
      (cast_heq (Etingof.reflFunctorMinus_obj_ne hi ρ a ha) w)
  have hmapw : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a b e w)
      (ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e)
        ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w)) :=
    Etingof.heq_apply (Etingof.reflFunctorMinus_obj_ne hi ρ a ha)
      (Etingof.reflFunctorMinus_obj_ne hi ρ b hb) hmapcoe hwa.symm
  have hfinal := Etingof.heq_apply (Etingof.reflFunctorMinus_obj_ne hi ρ b hb) rfl (heqv b hb)
    (cast_heq (Etingof.reflFunctorMinus_obj_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a b e w)).symm
  exact eq_of_heq (hfinal.trans ((cast_heq (Etingof.reflFunctorMinus_obj_ne hi ρ b hb)
    (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) a b e w)).trans hmapw))

/-- Convert a reversed-quiver arrow from a ≠ i to i back to the original i ⟶ a in Q.
For a ≠ i, `ReversedAtVertexHom Q i a i = i ⟶ a`. -/
def Etingof.reversedArrow_ne_eq
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a : Q}
    (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i) : i ⟶ a :=
  -- Defined directly as the `cast` along the type-equality lemma; see `reversedArrow_ne_ne`.
  cast (Etingof.ReversedAtVertexHom_ne_eq ha rfl) e

/-- `reversedArrow_ne_eq ha` is the `cast` along `ReversedAtVertexHom_ne_eq`. -/
theorem Etingof.reversedArrow_ne_eq_eq_cast
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a : Q}
    (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i) :
    Etingof.reversedArrow_ne_eq ha e =
      cast (Etingof.ReversedAtVertexHom_ne_eq ha rfl) e :=
  -- `reversedArrow_ne_eq` is now *defined* as this cast.
  rfl

/-- Canonical quotient map into F⁻ᵢ(ρ).obj i from the direct sum.
Reduces the `Decidable.casesOn` at vertex i (which is `.isTrue` since i = i)
and injects via the quotient map `mkQ`. -/
noncomputable def Etingof.reflFunctorMinus_mkQ
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) →ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i := by
  -- Need AddCommGroup for Submodule.mkQ
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  -- Build the quotient map via the `equivAt_eq` equivalence (which reduces the
  -- discriminant cleanly), avoiding a discriminant `match` that desyncs the carrier
  -- from its module instances on v4.29.
  exact (Etingof.reflFunctorMinus_equivAt_eq hi ρ).symm.toLinearMap ∘ₗ
    Submodule.mkQ (LinearMap.range (ρ.sourceMap i))

open Classical in
set_option maxHeartbeats 800000 in -- unfolding reflFunctorMinus_mkQ + reflectionFunctorMinus + match reduction
/-- The quotient map mkQ kills sourceMap elements: mkQ(∑ lof(a)(mapLinear(a.snd)(v))) = 0.
The mathematical content is: ψ(v) ∈ range(ψ) = ker(mkQ), so mkQ(ψ(v)) = 0.

Key technique: avoid `= 0` (where `0 : F⁻(ρ).obj i` has Decidable.rec in its type) by
first proving `= mkQ(0)` (where `0 : DirectSum` has no Decidable dependency), then
using `map_zero` to bridge. The `revert; unfold; rw [h_di]` pattern works because
both sides share the same `Decidable.casesOn` structure. -/
theorem Etingof.reflFunctorMinus_mkQ_kills_sourceMap
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : ρ.obj i) :
    Etingof.reflFunctorMinus_mkQ hi ρ
      (∑ a : Etingof.ArrowsOutOf Q i,
        (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) a)
          (ρ.mapLinear a.2 v)) = 0 := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  -- `mkQ = equivAt_eq.symm ∘ₗ Submodule.mkQ`, so it suffices that the quotient class of
  -- the source-map image is zero, i.e. the argument lies in `range (sourceMap i)`.
  have hz : Submodule.mkQ (LinearMap.range (ρ.sourceMap i))
      (∑ a : Etingof.ArrowsOutOf Q i,
        (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) a)
          (ρ.mapLinear a.2 v)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨v, by simp [Etingof.QuiverRepresentation.sourceMap, LinearMap.sum_apply,
      LinearMap.comp_apply]⟩
  unfold Etingof.reflFunctorMinus_mkQ
  rw [LinearMap.comp_apply, hz, map_zero]

open Classical in
set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorMinus + equivAt_ne + mkQ + match reduction
/-- At (a ≠ i, b = i), the F⁻ᵢ map sends w to mkQ(lof ⟨a, reversed_arrow⟩ (equivAt_ne w))
in the quotient at vertex i.

Dual of `reflFunctorPlus_mapLinear_eq_ne`. -/
theorem Etingof.reflFunctorMinus_mapLinear_ne_eq
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    {a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i)
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) a) :
    @Etingof.QuiverRepresentation.mapLinear k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) a i e w =
    (Etingof.reflFunctorMinus_mkQ hi ρ)
      (DirectSum.lof k (Etingof.ArrowsOutOf Q i)
        (fun a => ρ.obj a.1) ⟨a, Etingof.reversedArrow_ne_eq ha e⟩
        ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w)) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_di : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
  -- The target linear map of the F⁻ map at (a ≠ i, b = i): injection into the `a`-component
  -- of the direct sum followed by the quotient map `mkQ`.
  set RHSmap :=
    (Submodule.mkQ (LinearMap.range (ρ.sourceMap i))).comp
      (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)
        ⟨a, Etingof.reversedArrow_ne_eq ha e⟩) with hRHS
  -- (1) Function-level HEq of `mapAt` at the live discriminants vs. at the literal
  -- `(isFalse, isTrue)` branch, where the map iota-reduces to `RHSmap`.
  have hmap : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a i e)
      RHSmap := by
    have hf : HEq
        (Etingof.reflFunctorMinus_mapAt ρ hi a i (inst a i) (inst i i))
        (Etingof.reflFunctorMinus_mapAt ρ hi a i (.isFalse ha) (.isTrue rfl)) := by
      rw [h_da, h_di]
    have he : HEq e (Etingof.reversedArrow_ne_eq ha e) := by
      rw [Etingof.reversedArrow_ne_eq_eq_cast ha]; exact (cast_heq _ _).symm
    refine Etingof.heq_apply (Etingof.ReversedAtVertexHom_ne_eq ha rfl) ?_ hf he
    rw [h_da, h_di]
  -- (2) `equivAt_ne` is heterogeneously the identity on `ρ.obj a`.
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    show HEq (⇑(Etingof.reflFunctorMinus_equivAtAt_ne ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  have hwa : HEq ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w) w :=
    (Etingof.heq_apply (Etingof.reflFunctorMinus_obj_ne hi ρ a ha) rfl (heqv a ha)
      (cast_heq (Etingof.reflFunctorMinus_obj_ne hi ρ a ha) w).symm).trans
      (cast_heq (Etingof.reflFunctorMinus_obj_ne hi ρ a ha) w)
  -- (3) Instance HEqs to bridge `hmap` to HEq of coercions.
  have hac_a : HEq
      (Etingof.reflFunctorMinus_acmAt ρ i a (inst a i)) (ρ.instAddCommMonoid a) := by
    rw [h_da]; rfl
  have hac_i : HEq
      (Etingof.reflFunctorMinus_acmAt ρ i i (inst i i))
      (Submodule.Quotient.addCommGroup (p := LinearMap.range (ρ.sourceMap i))).toAddCommMonoid := by
    rw [h_di]; rfl
  have hmo_a : HEq
      (Etingof.reflFunctorMinus_modAt ρ i a (inst a i)) (ρ.instModule a) := by
    rw [h_da]; rfl
  have hmo_i : HEq
      (Etingof.reflFunctorMinus_modAt ρ i i (inst i i))
      (Submodule.Quotient.module (LinearMap.range (ρ.sourceMap i))) := by
    rw [h_di]; rfl
  have hmapcoe : HEq
      (⇑(@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a i e))
      (⇑RHSmap) :=
    Etingof.heq_linearMap_coe
      (Etingof.reflFunctorMinus_obj_ne hi ρ a ha)
      (Etingof.reflFunctorMinus_obj_eq hi ρ)
      hac_a hac_i hmo_a hmo_i hmap
  -- (4) Apply the coercion-HEq to the transported input.
  have hmapw : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a i e w)
      (RHSmap ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w)) :=
    Etingof.heq_apply (Etingof.reflFunctorMinus_obj_ne hi ρ a ha)
      (Etingof.reflFunctorMinus_obj_eq hi ρ) hmapcoe hwa.symm
  -- (5) `equivAt_eq.symm` is heterogeneously the identity on `coker(sourceMap i)`; combine.
  -- `equivAt_eq` is heterogeneously the identity (forward map, via the parametrized
  -- `equivAtAt_eq` and `rw` on the discriminant). Mirror of `heqve` in the Plus template.
  have hfwd : HEq (⇑(Etingof.reflFunctorMinus_equivAt_eq hi ρ))
      (id : ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.sourceMap i)) →
        ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
          LinearMap.range (ρ.sourceMap i))) := by
    show HEq (⇑(Etingof.reflFunctorMinus_equivAtAt_eq ρ (inst i i))) _
    rw [h_di]
    rfl
  -- The RHS of the goal, `reflFunctorMinus_mkQ (lof ...)`, equals `equivAt_eq.symm (mkQ (lof ...))`.
  have hRHSeq : (Etingof.reflFunctorMinus_mkQ hi ρ)
      (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)
        ⟨a, Etingof.reversedArrow_ne_eq ha e⟩
        ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w)) =
      (Etingof.reflFunctorMinus_equivAt_eq hi ρ).symm
        (RHSmap ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w)) := by
    rw [hRHS]
    unfold Etingof.reflFunctorMinus_mkQ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hRHSeq]
  -- `equivAt_eq.symm q ≅ q`, and `mapLinear ... e w ≅ q`; conclude by `eq_of_heq`.
  -- For `x := equivAt_eq.symm q : F⁻ᵢ(ρ).obj i`, the forward map is heterogeneously the
  -- identity, so `equivAt_eq x ≅ x`, i.e. `q ≅ x` (since `equivAt_eq x = q`).
  set x := (Etingof.reflFunctorMinus_equivAt_eq hi ρ).symm
    (RHSmap ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w)) with hx
  have hxq : HEq ((Etingof.reflFunctorMinus_equivAt_eq hi ρ) x) x :=
    (Etingof.heq_apply (Etingof.reflFunctorMinus_obj_eq hi ρ) rfl hfwd
      (cast_heq (Etingof.reflFunctorMinus_obj_eq hi ρ) x).symm).trans
      (cast_heq (Etingof.reflFunctorMinus_obj_eq hi ρ) x)
  have hqx : (Etingof.reflFunctorMinus_equivAt_eq hi ρ) x =
      RHSmap ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w) := by
    rw [hx, LinearEquiv.apply_symm_apply]
  rw [hqx] at hxq
  exact eq_of_heq (hmapw.trans hxq)


end ReflectionFunctorMinusAPI
