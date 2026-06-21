import Mathlib
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer

/-!
# Schur-Weyl L_i distinctness (Part 1): GL-equivariant ⟹ centralizer-linear

For the Schur-Weyl multiplicity spaces `M = ↥S →ₗ[A] E` with
`A = symGroupImage k V n` and `E = TensorPower k V n`, the centralizer
`C = centralizer(A) = diagonalActionImage k V n` acts by post-composition
(`b • l = b.val.comp l`, the `centralizerModuleHom` instance). The GL_N action on
the corresponding `L i = FDRep.of (ρ i)` is post-composition by `g^{⊗n}` for
`g ∈ GL_N(k)`.

Since `C = Algebra.adjoin k {g^{⊗n} : g ∈ (End k V)ˣ}`
(`adjoin_unitsTensorPow_eq_diagonalActionImage` composed with the centralizer
equality), a `k`-linear map between two multiplicity spaces that intertwines
post-composition by every `g^{⊗n}` is automatically `C`-linear: the predicate
"intertwines `c • -`" is closed under the algebra operations and holds on the
generators, so an `Algebra.adjoin_induction` propagates it to all of `C`.

This is **Part 1** of the GL-side distinctness output for
`glTensorRep_equivariant_schurWeyl_decomposition` (parent issue #4731). Part 2
(the B-side distinctness `M_i ≅_C M_j ⟹ i = j`, via the symmetric double
centralizer) consumes the `≃ₗ[C]` upgrade produced here.
-/

namespace Etingof

open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

section

variable {V : Type u} [AddCommGroup V] [Module k V]

-- Heartbeats bumped: the centralizer-membership proof goes through the
-- `Subalgebra → Module.End` instance chain, overrunning the default 20000.
set_option synthInstance.maxHeartbeats 400000 in
/-- For a unit `g : (End k V)ˣ`, the diagonal power `g^{⊗n}` packaged as an
element of the centralizer `C = centralizer(symGroupImage k V n)` (it commutes
with all permutation operators, via
`diagonalActionImage_le_centralizer_symGroupImage`). -/
noncomputable def unitTensorPowCentralizer [Module.Finite k V] (g : (Module.End k V)ˣ) (n : ℕ) :
    ↥(Subalgebra.centralizer k
      (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))) :=
  ⟨PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)),
    diagonalActionImage_le_centralizer_symGroupImage k V n
      (Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩)⟩

-- Heartbeats bumped: the multiplicity-space `Module ↥(symGroupImage) ↥S`
-- instances (a `Subalgebra → Ring → Module.End` chain) and the
-- `centralizerModuleHom` smul defeq overrun the default 20000 / 200000
-- budgets, exactly as in the source theorems (`Theorem5_18_1`,
-- `SchurWeylGLTransfer`).
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Part 1 (pointwise).** A `k`-linear equiv `ψ` between two Schur-Weyl
multiplicity spaces over `A = symGroupImage k V n` that intertwines
post-composition by every `g^{⊗n}` (`g` a unit in `End k V`) is automatically
linear over the centralizer `C = centralizer(A)`.

The generating set `{g^{⊗n} : g ∈ (End k V)ˣ}` of `C` (via
`adjoin_unitsTensorPow_eq_diagonalActionImage` and the centralizer equality)
drives an `Algebra.adjoin_induction`: the intertwining property is closed under
`+`, `*` (`mul_smul`), `algebraMap` (`ψ` is `k`-linear), and holds on the
generators by hypothesis. -/
theorem homA_centralizer_smul_comm_of_unitTensorPow_intertwine
    [Module.Finite k V] [Infinite k] [CharZero k] {n : ℕ}
    (hN : n ≤ Module.finrank k V)
    {S W : Submodule (symGroupImage k V n) (TensorPower k V n)}
    (ψ : (↥S →ₗ[symGroupImage k V n] TensorPower k V n) ≃ₗ[k]
        (↥W →ₗ[symGroupImage k V n] TensorPower k V n))
    (h_int : ∀ (g : (Module.End k V)ˣ)
        (l : ↥S →ₗ[symGroupImage k V n] TensorPower k V n),
        ψ (unitTensorPowCentralizer g n • l) = unitTensorPowCentralizer g n • ψ l)
    (c : ↥(Subalgebra.centralizer k
        (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))))
    (l : ↥S →ₗ[symGroupImage k V n] TensorPower k V n) :
    ψ (c • l) = c • ψ l := by
  classical
  -- Destructure `c` up front so the goal is literally in `⟨cval, hcmem⟩` form
  -- (the form the `adjoin_induction` predicate produces — avoids a `Subtype`
  -- eta mismatch at the end).
  obtain ⟨cval, hcmem⟩ := c
  -- Keep `C` abstract for brevity; do NOT `set` `symGroupImage`/`TensorPower`,
  -- as those appear inside the types of `S`, `W`, `ψ` and abstracting them
  -- reintroduces a shadowed `S✝` that no longer matches `ψ`'s domain.
  set C := Subalgebra.centralizer k
    (symGroupImage k V n : Set (Module.End k (TensorPower k V n))) with hC
  -- `k`-scalar-tower for the post-composition `C`-action on the hom-spaces
  -- (not a global instance; built locally as in `SchurWeylGLTransfer`).
  haveI hstS : IsScalarTower k (↥C)
      (↥S →ₗ[symGroupImage k V n] TensorPower k V n) :=
    ⟨fun a c f => by
      refine LinearMap.ext fun v => ?_
      change (a • c).val (f v) = a • c.val (f v)
      rw [SetLike.val_smul]
      exact LinearMap.smul_apply a c.val (f v)⟩
  haveI hstW : IsScalarTower k (↥C)
      (↥W →ₗ[symGroupImage k V n] TensorPower k V n) :=
    ⟨fun a c f => by
      refine LinearMap.ext fun v => ?_
      change (a • c).val (f v) = a • c.val (f v)
      rw [SetLike.val_smul]
      exact LinearMap.smul_apply a c.val (f v)⟩
  -- `C = Algebra.adjoin k {g^{⊗n} : g unit}`.
  have hCeq : C = Algebra.adjoin k (Set.range fun (g : (Module.End k V)ˣ) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) := by
    rw [hC, centralizer_symGroupImage_eq_diagonalActionImage k V n hN,
      ← adjoin_unitsTensorPow_eq_diagonalActionImage k (V := V) (n := n)]
  -- Reduce to an adjoin induction over `cval ∈ adjoin k {g^{⊗n}}`.
  have hgen : cval ∈ Algebra.adjoin k
      (Set.range fun (g : (Module.End k V)ˣ) =>
        PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) := by
    rw [← hCeq]; exact hcmem
  refine Algebra.adjoin_induction
    (s := Set.range fun (g : (Module.End k V)ˣ) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)))
    (p := fun x _ => ∀ (hx : x ∈ C)
        (l : ↥S →ₗ[symGroupImage k V n] TensorPower k V n),
        ψ ((⟨x, hx⟩ : ↥C) • l) = (⟨x, hx⟩ : ↥C) • ψ l)
    ?_ ?_ ?_ ?_ hgen hcmem l
  · -- Generator: x = g^{⊗n} for `g` a unit. The packaged element
    -- `unitTensorPowCentralizer g n` has the same `.val`, so the smuls are
    -- defeq (proof irrelevance on the membership), closing the goal directly.
    rintro x ⟨g, rfl⟩ hx l
    exact h_int g l
  · -- algebraMap r:
    intro r hx l
    have e1 : (⟨algebraMap k (Module.End k (TensorPower k V n)) r, hx⟩ : ↥C) • l = r • l := by
      rw [show (⟨algebraMap k (Module.End k (TensorPower k V n)) r, hx⟩ : ↥C)
          = algebraMap k (↥C) r from rfl,
        Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    have e2 : (⟨algebraMap k (Module.End k (TensorPower k V n)) r, hx⟩ : ↥C) • ψ l = r • ψ l := by
      rw [show (⟨algebraMap k (Module.End k (TensorPower k V n)) r, hx⟩ : ↥C)
          = algebraMap k (↥C) r from rfl,
        Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    rw [e1, e2, map_smul]
  · -- Add:
    rintro x y hx_adj hy_adj ihx ihy hxy l
    have hxC : x ∈ C := hCeq ▸ hx_adj
    have hyC : y ∈ C := hCeq ▸ hy_adj
    rw [show (⟨x + y, hxy⟩ : ↥C) = (⟨x, hxC⟩ : ↥C) + (⟨y, hyC⟩ : ↥C) from rfl,
      add_smul, map_add, ihx hxC l, ihy hyC l, add_smul]
  · -- Mul:
    rintro x y hx_adj hy_adj ihx ihy hxy l
    have hxC : x ∈ C := hCeq ▸ hx_adj
    have hyC : y ∈ C := hCeq ▸ hy_adj
    rw [show (⟨x * y, hxy⟩ : ↥C) = (⟨x, hxC⟩ : ↥C) * (⟨y, hyC⟩ : ↥C) from rfl,
      mul_smul, ihx hxC ((⟨y, hyC⟩ : ↥C) • l), ihy hyC l, mul_smul]

-- Heartbeats bumped for the same reason as the pointwise lemma above: the
-- packaged `≃ₗ[C]` carries the heavy multiplicity-space `Module` instances.
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Part 1 (packaged).** Upgrade a `k`-linear equiv `ψ` of multiplicity spaces
that intertwines post-composition by every `g^{⊗n}` to a `C`-linear equiv over
the centralizer `C = centralizer(symGroupImage k V n)`. -/
noncomputable def homACentralizerLinearEquivOfUnitTensorPowIntertwine
    [Module.Finite k V] [Infinite k] [CharZero k] {n : ℕ}
    (hN : n ≤ Module.finrank k V)
    {S W : Submodule (symGroupImage k V n) (TensorPower k V n)}
    (ψ : (↥S →ₗ[symGroupImage k V n] TensorPower k V n) ≃ₗ[k]
        (↥W →ₗ[symGroupImage k V n] TensorPower k V n))
    (h_int : ∀ (g : (Module.End k V)ˣ)
        (l : ↥S →ₗ[symGroupImage k V n] TensorPower k V n),
        ψ (unitTensorPowCentralizer g n • l) = unitTensorPowCentralizer g n • ψ l) :
    (↥S →ₗ[symGroupImage k V n] TensorPower k V n) ≃ₗ[↥(Subalgebra.centralizer k
        (symGroupImage k V n : Set (Module.End k (TensorPower k V n))))]
      (↥W →ₗ[symGroupImage k V n] TensorPower k V n) where
  toFun := ψ
  invFun := ψ.symm
  map_add' := ψ.map_add
  map_smul' c l :=
    homA_centralizer_smul_comm_of_unitTensorPow_intertwine hN ψ h_int c l
  left_inv := ψ.left_inv
  right_inv := ψ.right_inv

end

end Etingof
