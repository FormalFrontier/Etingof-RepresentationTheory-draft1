import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Tower

namespace RepresentationTheory.Mathlib.Algebra.Algebra.FiniteDimensional.RingProperties

/-- A ring that is finite-dimensional as an algebra over a field is Artinian. -/
theorem FiniteDimensional.isArtinianRing
    (k A : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsArtinianRing A :=
  isArtinian_of_tower k inferInstance

/-- A ring that is finite-dimensional as an algebra over a field is semiprimary. -/
theorem FiniteDimensional.isSemiprimaryRing
    (k A : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsSemiprimaryRing A :=
  haveI : IsArtinianRing A := FiniteDimensional.isArtinianRing k A
  inferInstance

end RepresentationTheory.Mathlib.Algebra.Algebra.FiniteDimensional.RingProperties
