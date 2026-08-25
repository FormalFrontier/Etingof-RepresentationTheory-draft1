import EtingofRepresentationTheory.Infrastructure.FGModuleCatEnoughProjectives
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# The subobject lattice of an `FGModuleCat A` object is finite dimensional

For a left-Noetherian ring `A` that is also Artinian (in particular a finite-dimensional
`k`-algebra) and any `X : FGModuleCat A`, the categorical subobject lattice `Subobject X` is a
`FiniteDimensionalOrder`: its strictly increasing chains have bounded length. This is the
order-theoretic finite-length standing assumption of Etingof §6.6/§9.6, recorded as
`finiteDimensionalOrder_subobject` in `Etingof.IsFiniteAbelianCategory`
(`Chapter9/Definition9_6_1.lean`), instantiated for `FGModuleCat A` (issue #7424, sub-issue #7639).

## Strategy

The fully faithful, monomorphism-preserving inclusion `forget₂ (FGModuleCat A) (ModuleCat A)` sends
a subobject `P ≤ X` to the subobject `Subobject.mk (incl.map P.arrow)` of the underlying module,
and this assignment is an **order embedding** `Subobject X ↪o Subobject (incl.obj X)`
(`Etingof.subobjectInclOrderEmbedding`): monotone because `P ≤ Q` factors the arrows, and reflecting
`≤` because full faithfulness lifts a `ModuleCat`-factorisation back to `FGModuleCat`.

Composing with Mathlib's `ModuleCat.subobjectModule : Subobject (incl.obj X) ≃o Submodule A X`
gives a strictly monotone map `Subobject X → Submodule A X`. Over an Artinian and Noetherian ring
the submodule lattice is already `FiniteDimensionalOrder` (`RingTheory/Length.lean`), and
`Order.krullDim_le_of_strictMono` transports the finite Krull dimension back to `Subobject X`.
-/

open CategoryTheory Limits

namespace Etingof

universe u

noncomputable section

variable {A : Type u} [Ring A] [IsNoetherianRing A]

/-- The inclusion `forget₂ (FGModuleCat A) (ModuleCat A)` preserves monomorphisms (it preserves
finite limits over a Noetherian ring). -/
instance forget₂_fgModuleCat_preservesMono :
    (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).PreservesMonomorphisms := by
  haveI : PreservesLimitsOfShape WalkingCospan
      (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)) := inferInstance
  infer_instance

/-- Mapping a subobject of `X : FGModuleCat A` to the corresponding subobject of the underlying
`ModuleCat A` object, via the fully faithful inclusion, is an order embedding: it is monotone and
reflects `≤`. -/
def subobjectInclOrderEmbedding (X : FGModuleCat.{u} A) :
    Subobject X ↪o Subobject ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).obj X) :=
  OrderEmbedding.ofMapLEIff
    (fun P => Subobject.mk ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).map P.arrow))
    (fun P Q => by
      set F := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
      constructor
      · -- reflect `≤`: a `ModuleCat`-factorisation lifts back through the fully faithful inclusion
        intro h
        let m := Subobject.ofMkLEMk (F.map P.arrow) (F.map Q.arrow) h
        have hm : m ≫ F.map Q.arrow = F.map P.arrow := Subobject.ofMkLEMk_comp h
        have hlift : F.map (F.preimage m ≫ Q.arrow) = F.map P.arrow := by
          rw [F.map_comp, F.map_preimage, hm]
        exact Subobject.le_of_comm (F.preimage m) (F.map_injective hlift)
      · -- monotone: `P ≤ Q` factors `P.arrow` through `Q.arrow`
        intro h
        refine Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE P Q h)) ?_
        rw [← F.map_comp, Subobject.ofLE_arrow])

/-- **The subobject lattice of any `FGModuleCat A` object is finite dimensional**, for `A` a
left-Noetherian *and* Artinian ring (in particular a finite-dimensional `k`-algebra). This is the
order-theoretic finite-length standing assumption of Etingof §9.6, supplying the
`finiteDimensionalOrder_subobject` field of `Etingof.IsFiniteAbelianCategory (FGModuleCat A)`. -/
theorem finiteDimensionalOrder_subobject_fgModuleCat [IsArtinianRing A] (X : FGModuleCat.{u} A) :
    FiniteDimensionalOrder (Subobject X) := by
  -- A strictly monotone map `Subobject X → Submodule A X`, through the order embedding above and
  -- Mathlib's subobject/submodule order isomorphism.
  have hsm : StrictMono (fun P : Subobject X =>
      ModuleCat.subobjectModule ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).obj X)
        (subobjectInclOrderEmbedding X P)) :=
    (ModuleCat.subobjectModule _).strictMono.comp (subobjectInclOrderEmbedding X).strictMono
  -- The submodule lattice is finite dimensional (finitely generated module over an Artinian and
  -- Noetherian ring), so its Krull dimension is neither `⊥` nor `⊤`.
  haveI : FiniteDimensionalOrder (Submodule A X) := inferInstance
  have hle : Order.krullDim (Subobject X) ≤ Order.krullDim (Submodule A X) :=
    Order.krullDim_le_of_strictMono _ hsm
  rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  refine ⟨Order.krullDim_ne_bot_iff.mpr ⟨⊥⟩, fun htop => ?_⟩
  rw [htop] at hle
  exact Order.krullDim_ne_top_of_finiteDimensionalOrder (top_le_iff.mp hle)

end

end Etingof
