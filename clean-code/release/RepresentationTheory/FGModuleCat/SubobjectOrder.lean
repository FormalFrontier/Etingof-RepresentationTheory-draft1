/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FGModuleCat.Projectivity
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Subobject orders in finitely generated module categories
-/

open CategoryTheory Limits

namespace RepresentationTheory.FGModuleCat.SubobjectOrder

universe u

noncomputable section

variable {A : Type u} [Ring A] [IsNoetherianRing A]

/-- The forgetful functor from finitely generated modules to modules preserves monomorphisms over a Noetherian ring. -/
instance preservesMonomorphisms_forgetToModuleCat :
    (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).PreservesMonomorphisms := by
  haveI : PreservesLimitsOfShape WalkingCospan
      (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)) := inferInstance
  infer_instance

/-- An order embedding from subobjects of a finitely generated module to subobjects of its underlying module. -/
def subobjectOrderEmbeddingToModuleCat (X : FGModuleCat.{u} A) :
    Subobject X ↪o Subobject ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).obj X) :=
  OrderEmbedding.ofMapLEIff
    (fun P => Subobject.mk ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).map P.arrow))
    (fun P Q => by
      set F := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
      constructor
      · intro h
        let m := Subobject.ofMkLEMk (F.map P.arrow) (F.map Q.arrow) h
        have hm : m ≫ F.map Q.arrow = F.map P.arrow := Subobject.ofMkLEMk_comp h
        have hlift : F.map (F.preimage m ≫ Q.arrow) = F.map P.arrow := by
          rw [F.map_comp, F.map_preimage, hm]
        exact Subobject.le_of_comm (F.preimage m) (F.map_injective hlift)
      · intro h
        refine Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE P Q h)) ?_
        rw [← F.map_comp, Subobject.ofLE_arrow])

/-- The subobjects of a finitely generated module over a Noetherian Artinian ring form a finite-dimensional order. -/
theorem finiteDimensionalOrder_subobject [IsArtinianRing A] (X : FGModuleCat.{u} A) :
    FiniteDimensionalOrder (Subobject X) := by
  have hsm : StrictMono (fun P : Subobject X =>
      ModuleCat.subobjectModule ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).obj X)
        (subobjectOrderEmbeddingToModuleCat X P)) :=
    (ModuleCat.subobjectModule _).strictMono.comp
      (subobjectOrderEmbeddingToModuleCat X).strictMono
  haveI : FiniteDimensionalOrder (Submodule A X) := inferInstance
  have hle : Order.krullDim (Subobject X) ≤ Order.krullDim (Submodule A X) :=
    Order.krullDim_le_of_strictMono _ hsm
  rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  refine ⟨Order.krullDim_ne_bot_iff.mpr ⟨⊥⟩, fun htop => ?_⟩
  rw [htop] at hle
  exact Order.krullDim_ne_top_of_finiteDimensionalOrder (top_le_iff.mp hle)

end

end RepresentationTheory.FGModuleCat.SubobjectOrder
