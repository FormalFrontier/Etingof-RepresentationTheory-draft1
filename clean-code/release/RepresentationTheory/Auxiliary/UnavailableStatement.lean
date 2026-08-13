/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.AuxiliaryUnavailableStatement
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary Unavailable Statement

An auxiliary trace identity in the nested `RepresentationTheory.Auxiliary` namespace.
-/

open Representation
open scoped TensorProduct

/-- Auxiliary theorem. -/
@[source_ref "Chapter5/Remark5.9.2" (role := supporting)]
theorem RepresentationTheory.Auxiliary.UnavailableStatement.auxiliary
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H V)
    (g : G) :
    LinearMap.trace ℂ (Representation.IndV H.subtype ρ)
        (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ g)
      = (Fintype.card H : ℂ)⁻¹ *
          ∑ x : G,
            if h : x * g * x⁻¹ ∈ H then
              LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩)
            else 0 :=
  RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem H ρ g
