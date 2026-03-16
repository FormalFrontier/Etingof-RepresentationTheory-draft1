import Mathlib

/-!
# Example 4.9.1: Tensor Product Multiplicities

Tensor product decomposition tables for S₃, S₄, and A₅.

**S₃ examples:**
- ℂ₊ ⊗ ℂ₋ = ℂ₋
- ℂ₋ ⊗ ℂ₋ = ℂ₊
- ℂ² ⊗ ℂ² = ℂ₊ ⊕ ℂ₋ ⊕ ℂ²

For S₄ and A₅, similar multiplication tables show how tensor products decompose
into irreducibles, computed using the formula:
  n_{ij}^k = (χ_i · χ_j, χ_k) = (1/|G|) Σ_g χ_i(g) χ_j(g) χ_k(g)*

## Mathlib correspondence

Tensor product decomposition multiplicities are not systematically in Mathlib.
-/

set_option linter.style.nativeDecide false in
/-- S₃ has exactly 3 conjugacy classes, hence 3 irreducible representations.
The dimensions must satisfy 1² + 1² + 2² = 6 = |S₃|, giving representations
of dimensions 1, 1, 2. The tensor product table ℂ² ⊗ ℂ² ≅ ℂ₊ ⊕ ℂ₋ ⊕ ℂ²
follows from character inner products. (Etingof Example 4.9.1) -/
theorem Etingof.Example4_9_1_S3_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 3))) = 3 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- S₃ has order 6. Combined with 3 conjugacy classes, the sum-of-squares formula
∑ dᵢ² = |G| forces dimensions 1, 1, 2. (Etingof Example 4.9.1) -/
theorem Etingof.Example4_9_1_S3_card :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  native_decide
