import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer

/-!
# Theorem 5.22.1 (Schur-Weyl L_i, part C-4c): the Schur module is a simple GL_N-rep.

Final assembly step combining the algebraic core
`schurModuleSubmodule_isSimple_centralizer` (the C-4a aggregation, sorry pending the
parallel Schur-Weyl C-4a-i and C-4a-ii sub-issues) with the GL_N transfer
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
(C-4b, in `SchurWeylGLTransfer.lean`).

The deliverable is `schurModule_isSimple`: simplicity of `SchurModule k N λ` as a
`MonoidAlgebra k GL_N(k)`-module.
-/

noncomputable section

namespace Etingof

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]

/-! ## `diagonalActionImage` acts on `SchurModuleSubmodule`.

The diagonal-action subalgebra `diagonalActionImage k V n ⊆ End_k(V^⊗n)` commutes
with `symGroupImage k V n` (containment in the centralizer). In particular it
commutes with `youngSymEndomorphism k N lam ∈ symGroupImage`, hence preserves its
range, which is `SchurModuleSubmodule k N lam`. -/

/-- The diagonal-action subalgebra preserves `SchurModuleSubmodule`. -/
theorem schurModuleSubmodule_smul_mem_aux (N : ℕ) (lam : Fin N → ℕ)
    (b : ↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
    {v : TensorPower k (Fin N → k) (∑ i, lam i)}
    (hv : v ∈ SchurModuleSubmodule k N lam) :
    b.val v ∈ SchurModuleSubmodule k N lam := by
  obtain ⟨w, rfl⟩ := hv
  -- diagonalActionImage ⊆ centralizer(symGroupImage), and youngSymEndo ∈ symGroupImage,
  -- so b.val commutes with youngSymEndo.
  have hb := diagonalActionImage_le_centralizer_symGroupImage k (Fin N → k) (∑ i, lam i)
    b.property
  rw [Subalgebra.mem_centralizer_iff] at hb
  have h_youngSym :
      (youngSymEndomorphism k N lam :
        Module.End k (TensorPower k (Fin N → k) (∑ i, lam i))) ∈
        symGroupImage k (Fin N → k) (∑ i, lam i) := by
    rw [← symGroupAlgHom_range k (Fin N → k) (∑ i, lam i)]
    exact ⟨_, rfl⟩
  -- hb : ∀ g ∈ symGroupImage, g * b = b * g, so youngSymEndo * b.val = b.val * youngSymEndo.
  have h_comm := hb _ h_youngSym
  refine ⟨b.val w, ?_⟩
  exact LinearMap.congr_fun h_comm w

/-- The `SMul` action of `diagonalActionImage` on `SchurModuleSubmodule`. -/
noncomputable instance schurModuleSubmodule_diagonalActionImage_smul
    (N : ℕ) (lam : Fin N → ℕ) :
    SMul (↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
      (SchurModuleSubmodule k N lam) where
  smul b v := ⟨b.val v.val, schurModuleSubmodule_smul_mem_aux k N lam b v.property⟩

@[simp]
lemma schurModuleSubmodule_diagonalActionImage_smul_coe
    (N : ℕ) (lam : Fin N → ℕ)
    (b : ↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
    (v : SchurModuleSubmodule k N lam) :
    ((b • v : SchurModuleSubmodule k N lam) : TensorPower k (Fin N → k) (∑ i, lam i)) =
      b.val v.val := rfl

/-- The `Module` action of `diagonalActionImage` on `SchurModuleSubmodule`,
inherited via the underlying action on `TensorPower`. -/
noncomputable instance schurModuleSubmodule_diagonalActionImage_module
    (N : ℕ) (lam : Fin N → ℕ) :
    Module (↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
      (SchurModuleSubmodule k N lam) where
  one_smul v := by
    apply Subtype.ext
    change (1 : ↥(diagonalActionImage k (Fin N → k) (∑ i, lam i))).val v.val = v.val
    change (1 : Module.End k _) v.val = v.val
    simp
  mul_smul a b v := by
    apply Subtype.ext
    change (a * b).val v.val = a.val (b.val v.val)
    change (a.val * b.val) v.val = a.val (b.val v.val)
    rfl
  smul_zero b := by
    apply Subtype.ext
    change b.val (0 : SchurModuleSubmodule k N lam).val = 0
    change b.val (0 : TensorPower k (Fin N → k) _) = 0
    simp
  smul_add b v w := by
    apply Subtype.ext
    change b.val (v + w).val = b.val v.val + b.val w.val
    change b.val (v.val + w.val) = b.val v.val + b.val w.val
    simp
  add_smul a b v := by
    apply Subtype.ext
    change (a + b).val v.val = a.val v.val + b.val v.val
    change (a.val + b.val) v.val = a.val v.val + b.val v.val
    rfl
  zero_smul v := by
    apply Subtype.ext
    change (0 : ↥(diagonalActionImage k (Fin N → k) _)).val v.val = 0
    change (0 : Module.End k _) v.val = 0
    simp

/-- The `diagonalActionImage`-action on `SchurModuleSubmodule` is compatible with the
`k`-action via the canonical `IsScalarTower` (the underlying action on `TensorPower`
satisfies `c • (b.val v) = b.val (c • v)` for scalars `c : k`). -/
instance schurModuleSubmodule_diagonalActionImage_isScalarTower
    (N : ℕ) (lam : Fin N → ℕ) :
    IsScalarTower k (↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
      (SchurModuleSubmodule k N lam) where
  smul_assoc c b v := by
    apply Subtype.ext
    change (c • b).val v.val = c • b.val v.val
    change (c • b.val) v.val = c • b.val v.val
    rfl

/-! ## C-4a aggregation (sorry pending parallel work)

`schurModuleSubmodule_isSimple_centralizer` aggregates the C-4a sub-pieces:
* sub-α: bimodule decomposition (already in Mathlib + `Theorem5_18_4`),
* sub-β: off-block vanishing (#2683 in flight as PR #2697, #2684 blocked),
* sub-γ: rank-1 scaled-projection structure (#2694 in flight: γ.A; #2693
  blocked: γ.B),
* C-4a-ii: `image_of_primitive_idempotent_isSimple_centralizer` (PR #2698
  in flight, #2695 closed).

This sorry will be discharged by a follow-up issue once the in-flight pieces
land. The statement is precisely what the C-4a chain delivers. -/

/-- **Schur-Weyl L_i, part C-4a (aggregated).**

The Schur module submodule `SchurModuleSubmodule k N λ`, viewed as a
`diagonalActionImage k V n`-module via the canonical action above, is simple.

Equivalently, by `Theorem5_18_4_centralizers` (which requires `n ≤ N`),
it is simple as a `centralizer(symGroupImage)`-module. The proof aggregates
the pieces `sub-α`, `sub-β`, `sub-γ`, `C-4a-ii` of the C-4a programme via
`image_of_primitive_idempotent_isSimple_centralizer`
(`PrimitiveIdempotentSimplicity.lean`). -/
theorem schurModuleSubmodule_isSimple_centralizer
    (N : ℕ) (lam : Fin N → ℕ) (_hlam : Antitone lam) (_hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule
      (↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
      (SchurModuleSubmodule k N lam) := by
  sorry

/-! ## Final assembly: `schurModule_isSimple` -/

/-- **Theorem 5.22.1 (Schur-Weyl L_i, part C-4c):** The Schur module
`SchurModule k N λ` is simple as a `GL_N(k)`-representation.

Combines the algebraic core `schurModuleSubmodule_isSimple_centralizer` (C-4a)
with the GL_N transfer `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
(C-4b in `SchurWeylGLTransfer.lean`): the canonical
`diagonalActionImage`-module structure on `SchurModuleSubmodule` makes the
GL-action factor as `g • v ↦ ⟨g^⊗n, _⟩ • v`, so `diagonalActionImage`-simplicity
transfers to `MonoidAlgebra k GL_N`-simplicity. -/
theorem schurModule_isSimple
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (SchurModule k N lam).ρ) := by
  haveI := schurModuleSubmodule_isSimple_centralizer k N lam hlam hN
  refine isSimpleModule_monoidAlgebra_GL_of_centralizer_simple k
    (N := N) (n := ∑ i, lam i)
    (M := ↥(SchurModuleSubmodule k N lam))
    (schurModuleRep k N lam) ?_
  intro g x
  -- Both sides apply `g^⊗n` to `x.val` and re-bundle into `SchurModuleSubmodule`.
  -- LHS: `(schurModuleRep g) x = (glTensorRep g).restrict ... x`.
  -- RHS: `(⟨g^⊗n, _⟩ : diagonalActionImage) • x = ⟨g^⊗n x.val, _⟩`
  -- These are definitionally equal after Subtype.ext.
  apply Subtype.ext
  rfl

end Etingof

end
