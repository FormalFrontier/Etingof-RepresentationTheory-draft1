import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType

/-!
# Field-Generic T(1, 2, 5) Representation — API stub

API stub file introduced by issue #2875 (deliverable 1) so that the
per-(F, Q) assembly `not_posdef_infinite_type_per_kQ` in
`FieldGenericInfiniteType.lean` can dispatch by name to the T(1, 2, 5)
forbidden-subgraph case.

The actual `_F` / `_kQ` constructions and the body of
`t125_not_finite_type_per_kQ` are tracked by issue #2793. This file only
introduces the theorem signature with a `sorry` body so that the
assembly remains decoupled from the proof-level chain.

See `FieldGenericInfiniteType.lean` for the naming conventions
(`_F` / `_gen`, `_kQ`, `_per_kQ`).
-/

namespace Etingof

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `t125_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `t125Adj`, the
set of dimension vectors of indecomposable representations of `Q` over
`F` is infinite.

API stub introduced by issue #2875 (deliverable 1): the body is `sorry`
pending the proof tracked by issue #2793. This stub exists so that the
per-(F, Q) assembly `not_posdef_infinite_type_per_kQ` can dispatch by
name to the T(1, 2, 5) forbidden-subgraph case via
`subgraph_infinite_type_transfer_per_kQ`. -/
theorem t125_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q t125Adj) :
    ¬ Set.Finite
      {d : Fin 9 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 9) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- TODO (#2793): replace this `sorry` with the proof that the
  -- orientation-generic family `t125Rep_kQ F Q hOrient (m + 1)` is
  -- indecomposable and produces infinitely many distinct dimension
  -- vectors (mirror `etilde6_not_finite_type_per_kQ`).
  let _ := hOrient
  sorry

end Etingof
