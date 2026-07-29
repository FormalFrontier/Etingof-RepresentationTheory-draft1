import EtingofRepresentationTheory.Chapter4.Theorem4_2_1

/-!
# Downstream import/`#check` test for Theorem 4.2.1

This file imports `Chapter4/Theorem4_2_1.lean` and pins the public signatures of the
character-basis endpoints. Its purpose is to catch a regression in the source of
Theorem 4.2.1 even when cached oleans would otherwise hide it from the aggregate build:
because this file `import`s the theorem file and re-elaborates the endpoint statements,
it forces a fresh check of their public API.

See issue #7519 (restore fresh-buildable character-basis theorem 4.2.1).
-/

open CategoryTheory FDRep

universe u

-- The four public endpoints must remain importable under these names.
#check @Etingof.Theorem4_2_1
#check @Etingof.Theorem4_2_1_linearIndependent
#check @Etingof.Theorem4_2_1_span_eq_classFunctionSubmodule
#check @Etingof.classFunction_eq_zero_of_orthogonal_simples

-- Signature locks: each `example` fails to elaborate if the corresponding statement drifts.

/-- Spanning: irreducible characters span the class functions. -/
example {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span k (FDRep.character '' { V : FDRep k G | Simple V }) :=
  Etingof.Theorem4_2_1 f hf

/-- Independence: irreducible characters are k-linearly independent. -/
example {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] :
    LinearIndependent k
      (Subtype.val : ↥(FDRep.character '' { V : FDRep k G | Simple V }) → (G → k)) :=
  Etingof.Theorem4_2_1_linearIndependent

/-- The span is the named class-function submodule. -/
example {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] :
    Submodule.span k (FDRep.character '' {V : FDRep k G | Simple V}) =
      Etingof.classFunctionSubmodule k G :=
  Etingof.Theorem4_2_1_span_eq_classFunctionSubmodule

/-- Completeness: a class function orthogonal to every irreducible character is zero. -/
example {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf_class : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hf_orth : ∀ (V : FDRep k G) [Simple V], ∑ g : G, f g * V.character g⁻¹ = 0) :
    f = 0 :=
  Etingof.classFunction_eq_zero_of_orthogonal_simples f hf_class hf_orth
