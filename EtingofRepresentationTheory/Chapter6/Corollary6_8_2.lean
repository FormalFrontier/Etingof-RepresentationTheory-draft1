import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_3
import EtingofRepresentationTheory.Chapter6.Definition6_4_7
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Theorem6_8_1

/-!
# Corollary 6.8.2: Dimension Vectors Are Positive Roots

For any indecomposable representation V of a Dynkin quiver Q, d(V) is a positive root,
i.e., B(d(V), d(V)) = 2.

The proof: by Theorem 6.8.1, s_{i₁} ⋯ s_{iₘ}(d(V)) = αₚ. Since the sᵢ preserve B,
B(d(V), d(V)) = B(αₚ, αₚ) = 2.

## Mathlib correspondence

Requires dimension vectors, simple reflections preserving the bilinear form,
and Theorem 6.8.1. This is part of Gabriel's theorem (classification of
quivers of finite representation type).
-/

section BilinearFormPreservation

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

/-- Root reflection preserves the bilinear form of a symmetric matrix:
B(sα(v), sα(v)) = B(v, v) when A is symmetric and B(α, α) = 2.

The proof is a direct computation:
  sα(v) = v - B(v, α) · α
  B(sα(v), sα(v)) = B(v,v) - 2·B(v,α)·B(α,v) + B(v,α)²·B(α,α)
                   = B(v,v) - 2·c² + c²·2 = B(v,v)
where c = B(v, α) and we use B(α,v) = B(v,α) (symmetry) and B(α,α) = 2. -/
theorem Etingof.rootReflection_preserves_bilinearForm
    (hA : A.IsSymm)
    (α : Fin n → ℤ) (hα : dotProduct α (A.mulVec α) = 2)
    (v : Fin n → ℤ) :
    dotProduct (Etingof.rootReflection n A α v)
      (A.mulVec (Etingof.rootReflection n A α v)) =
    dotProduct v (A.mulVec v) := by
  unfold Etingof.rootReflection
  set c := dotProduct v (A.mulVec α) with hc_def
  have hsymm : dotProduct α (A.mulVec v) = c := by
    rw [Matrix.dotProduct_mulVec, ← hA.eq, Matrix.vecMul_transpose, dotProduct_comm]
  have h1 : A.mulVec (v - c • α) = A.mulVec v - c • A.mulVec α := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [h1]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hsymm, hα]
  ring

/-- Simple reflection sᵢ preserves the bilinear form when the Cartan matrix is symmetric
and satisfies B(αᵢ, αᵢ) = 2 (which is the standard normalization for simple roots). -/
theorem Etingof.simpleReflection_preserves_bilinearForm
    (hA : A.IsSymm)
    (i : Fin n)
    (hroot : dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2)
    (v : Fin n → ℤ) :
    dotProduct (Etingof.simpleReflection n A i v)
      (A.mulVec (Etingof.simpleReflection n A i v)) =
    dotProduct v (A.mulVec v) :=
  Etingof.rootReflection_preserves_bilinearForm A hA _ hroot v

/-- Iterated simple reflections preserve the bilinear form.
If each simple root αᵢ satisfies B(αᵢ, αᵢ) = 2, then applying any sequence of
simple reflections preserves B(v, v). -/
theorem Etingof.iteratedSimpleReflection_preserves_bilinearForm
    (hA : A.IsSymm)
    (hroots : ∀ i : Fin n, dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2)
    (vertices : List (Fin n)) (v : Fin n → ℤ) :
    dotProduct (Etingof.iteratedSimpleReflection n A vertices v)
      (A.mulVec (Etingof.iteratedSimpleReflection n A vertices v)) =
    dotProduct v (A.mulVec v) := by
  unfold Etingof.iteratedSimpleReflection
  induction vertices generalizing v with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, Etingof.simpleReflection_preserves_bilinearForm A hA j (hroots j)]

end BilinearFormPreservation

section Corollary

/-- The dimension vector of any indecomposable representation of a Dynkin quiver
is a positive root.

Given that d is the dimension vector of an indecomposable representation of a
Dynkin quiver (so d ≥ 0, d ≠ 0, and by Theorem 6.8.1 there exist reflections
reducing d to a simple root), we conclude that d is a positive root:
d ≠ 0, B(d, d) = 2, and all coordinates are nonneg.

The proof reduces to: simple reflections preserve B, and B(αₚ, αₚ) = 2 for
any simple root αₚ.
(Etingof Corollary 6.8.2) -/
theorem Etingof.Corollary6_8_2
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hreflect : ∃ (vertices : List (Fin n)) (p : Fin n),
      Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) vertices d =
        Etingof.simpleRoot n p) :
    Etingof.IsPositiveRoot n adj d := by
  obtain ⟨vertices, p, hrefl⟩ := hreflect
  refine ⟨⟨hd_nonzero, ?_⟩, hd_pos⟩
  -- Need: dotProduct d ((2 • 1 - adj).mulVec d) = 2
  -- The Cartan matrix is A = 2 • 1 - adj = cartanMatrix n adj
  change dotProduct d ((Etingof.cartanMatrix n adj).mulVec d) = 2
  -- By iterated reflection preservation: B(d, d) = B(αₚ, αₚ)
  have hA_symm : (Etingof.cartanMatrix n adj).IsSymm := by
    unfold Etingof.cartanMatrix
    rw [Matrix.IsSymm]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    rw [hDynkin.1.eq]
  have hroots : ∀ i : Fin n,
      dotProduct (Pi.single i 1)
        ((Etingof.cartanMatrix n adj).mulVec (Pi.single i 1)) = 2 := by
    intro i
    unfold Etingof.cartanMatrix
    simp only [Matrix.sub_mulVec]
    simp only [dotProduct_sub]
    have hsmul : (2 • (1 : Matrix (Fin n) (Fin n) ℤ)).mulVec (Pi.single i 1) =
        2 • Pi.single i 1 := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hdot1 : dotProduct (Pi.single i (1 : ℤ)) (2 • Pi.single i (1 : ℤ)) = 2 := by
      simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    have hadj : dotProduct (Pi.single i (1 : ℤ)) (adj.mulVec (Pi.single i 1)) = adj i i := by
      simp [dotProduct, Pi.single_apply, Matrix.mulVec, Finset.sum_ite_eq', Finset.mem_univ]
    rw [hsmul, hdot1, hadj, hDynkin.2.1 i]
    ring
  have h := Etingof.iteratedSimpleReflection_preserves_bilinearForm
    (Etingof.cartanMatrix n adj) hA_symm hroots vertices d
  rw [hrefl] at h
  simp only [Etingof.simpleRoot] at h
  rw [hroots p] at h
  linarith

end Corollary
