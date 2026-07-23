import EtingofRepresentationTheory.Chapter6.CoxeterInfrastructure

/-!
# Downstream import/`#check` test for the §6.8 Coxeter/Gabriel infrastructure

This file imports `Chapter6/CoxeterInfrastructure.lean` and pins the public signatures of
the admissible-ordering, iterated-reversal and reflection-functor endpoints. Its purpose is
to catch a regression in the source even when cached oleans would otherwise hide it from the
aggregate build: because this file `import`s the infrastructure file and re-elaborates the
endpoint statements, it forces a fresh check of their public API.

See issue #7509 (restore fresh-buildable Coxeter/Gabriel infrastructure).
-/

-- The public admissible-ordering / iterated-reversal API must remain importable.
#check @Etingof.iteratedReversedAtVertices
#check @Etingof.iteratedReversedAtVertices_append
#check @Etingof.iteratedReversedAtVertices_perm_eq
#check @Etingof.IsAdmissibleOrdering
#check @Etingof.admissibleOrdering_exists
#check @Etingof.admissible_sinks_replicated

-- The reflection-functor `Module.Free` / `Module.Finite` endpoints that the Gabriel-theorem
-- setup depends on: these were the specific declarations whose fresh build regressed.
#check @Etingof.reflFunctorPlus_free_ne
#check @Etingof.reflFunctorPlus_free_eq
#check @Etingof.reflFunctorPlus_finite_ne
#check @Etingof.reflFunctorPlus_finite_eq

-- The Gabriel-theorem endpoint (Corollary 6.8.2) built on top of the above.
#check @Etingof.Corollary6_8_2

-- Signature lock: an admissible ordering exists for every Dynkin orientation.
example {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : Etingof.IsOrientationOf Q adj) :
    ∃ ordering : List (Fin n), Etingof.IsAdmissibleOrdering Q ordering :=
  Etingof.admissibleOrdering_exists hDynkin hOrient
