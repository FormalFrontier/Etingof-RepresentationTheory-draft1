import Mathlib

/-!
# Theorem 5.18.1: Double Centralizer Theorem

Let A be a semisimple subalgebra of End(E) for a finite-dimensional vector space E,
and let B = End_A(E) be the commutant. Then:

(i) A = End_B(E) (the double centralizer property)
(ii) B is semisimple
(iii) As an (A ⊗ B)-module, E ≅ ⊕_{i ∈ I} Vᵢ ⊗ Wᵢ, where {Vᵢ} are the
     distinct irreducible A-modules appearing in E and Wᵢ are the corresponding
     irreducible B-modules.

## Mathlib correspondence

This is a fundamental theorem in the theory of semisimple algebras. Mathlib has
`IsSemisimpleRing` and `Subalgebra.centralizer`. The double centralizer theorem
itself is not yet formalized in Mathlib.
-/

open scoped TensorProduct

namespace Etingof

variable (k : Type*) [Field k]
  (E : Type*) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- Double centralizer theorem, part (i): For a semisimple subalgebra A of End(E) where
E is a faithful A-module, the double centralizer recovers A.

More precisely, if A is a subalgebra of End_k(E) that is semisimple as a ring and E is
faithful over A, then centralizer(centralizer(A)) = A in End_k(E).
(Etingof Theorem 5.18.1, part i) -/
theorem Theorem5_18_1_double_centralizer
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    Subalgebra.centralizer k
      (Subalgebra.centralizer k (A : Set (Module.End k E)) :
        Set (Module.End k E)) = A := by
  sorry

/-- Double centralizer theorem, part (ii): The commutant of a semisimple subalgebra
of End(E) is itself semisimple.

If A is a semisimple subalgebra of End_k(E) with E faithful, then
B = centralizer(A) in End_k(E) is a semisimple ring.
(Etingof Theorem 5.18.1, part ii) -/
theorem Theorem5_18_1_commutant_semisimple
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    IsSemisimpleRing (Subalgebra.centralizer k (A : Set (Module.End k E))) := by
  sorry

/-- Double centralizer theorem, part (iii): Bimodule decomposition.

If A is a semisimple subalgebra of End_k(E) with E faithful, and B = centralizer(A),
then as a module over A ⊗ B^op, E decomposes as a direct sum:
  E ≅ ⊕_i V_i ⊗ W_i
where {V_i} are the distinct simple A-modules appearing in E and W_i = Hom_A(V_i, E)
are the corresponding simple B-modules.

We state this as the existence of an index type, simple modules, and an isomorphism.
(Etingof Theorem 5.18.1, part iii) -/
theorem Theorem5_18_1_decomposition
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V W : ι → Type)
      (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module k (V i))
      (_ : ∀ i, Module A (V i)) (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i, AddCommGroup (W i)) (_ : ∀ i, Module k (W i)),
      Nonempty (E ≃ₗ[k] DirectSum ι (fun i => V i ⊗[k] W i)) := by
  sorry

end Etingof
