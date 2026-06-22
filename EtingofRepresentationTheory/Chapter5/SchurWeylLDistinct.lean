import Mathlib
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer
import EtingofRepresentationTheory.Chapter5.MultiplicitySpaceBiduality

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
    rw [hC, centralizer_symGroupImage_eq_diagonalActionImage k V n,
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
    homA_centralizer_smul_comm_of_unitTensorPow_intertwine ψ h_int c l
  left_inv := ψ.left_inv
  right_inv := ψ.right_inv

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- The centralizer post-composition action `unitTensorPowCentralizer g n • f`
is, by definition of `centralizerModuleHom`, composition with
`centralizerToEndA … (g^{⊗n})`. Stated abstractly (over a general carrier `V`) so
that the centralizer `•` is resolved here once; downstream uses with the concrete
carrier `V = Fin N → k` rewrite with this lemma instead of re-synthesizing the
centralizer action, whose typeclass search does not go through for `Fin N → k`. -/
theorem unitTensorPowCentralizer_smul_eq [Module.Finite k V] {n : ℕ}
    {S : Submodule (symGroupImage k V n) (TensorPower k V n)}
    (g : (Module.End k V)ˣ)
    (f : ↥S →ₗ[symGroupImage k V n] TensorPower k V n) :
    unitTensorPowCentralizer g n • f
      = (centralizerToEndA k (TensorPower k V n) (symGroupImage k V n)
          (unitTensorPowCentralizer g n)).comp f := rfl

end

/-! ### Part 2 wiring: GL-side pairwise distinctness of the Schur-Weyl simples

Assembling Part 1 (the GL-equivariant ⟹ centralizer-linear upgrade above) with
the B-side distinctness `multiplicitySpace_Cdistinct`
(`MultiplicitySpaceBiduality.lean`) yields the GL-side output targeted by issue
#4849/#4860: the abstract simple summands `L i` of `V^{⊗n}` produced by the
explicit Schur-Weyl decomposition are pairwise non-isomorphic. -/

section GLDistinct

variable [IsAlgClosed k] [CharZero k]

open scoped TensorProduct

omit [IsAlgClosed k] [CharZero k] in
/-- Every unit of `End k (Fin N → k)` is `Matrix.mulVecLin` of a `GL_N(k)`
matrix (the units of `End k (Fin N → k)` are exactly the general linear group,
via `Matrix.GeneralLinearGroup.toLin`). -/
theorem exists_gl_mulVecLin_eq {N : ℕ} (g : (Module.End k (Fin N → k))ˣ) :
    ∃ h : Matrix.GeneralLinearGroup (Fin N) k,
      Matrix.mulVecLin (R := k) (h : Matrix (Fin N) (Fin N) k)
        = (g : Module.End k (Fin N → k)) := by
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_⟩
  rw [← Matrix.GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **GL-side distinctness (Part 2 wiring).** Given the explicit Schur-Weyl
decomposition data of `V^{⊗n}` (`V = Fin N → k`) from
`Theorem5_18_4_GL_rep_decomposition_explicit_simple` — the Specht submodules
`S' i` (simple and pairwise non-isomorphic over `A = symGroupImage k V n`), the
abstract simple polynomial `GL_N`-reps `L i`, the carrier identifications
`L_carrier i : L i ≃ₗ[k] (↥(S' i) →ₗ[A] V^{⊗n})`, and the action formula
`h_act` — the `L i` are pairwise non-isomorphic as `GL_N`-representations.

The proof transports an FDRep iso `L i ≅ L j` through `L_carrier i`, `L_carrier
j` to a `k`-linear equiv `ψ` of multiplicity spaces, shows `ψ` intertwines
post-composition by every `g^{⊗n}` (from `h_act` and the FDRep-iso equivariance,
using that every unit of `End k V` comes from `GL_N`), upgrades it to a
`C`-linear equiv via `homACentralizerLinearEquivOfUnitTensorPowIntertwine`
(Part 1), and concludes `i = j` from `multiplicitySpace_Cdistinct` (Part 2). -/
theorem schurWeyl_L_pairwise_distinct_of_explicit
    (N n : ℕ)
    {ι : Type}
    (S' : ι → Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    (hS'_simp : ∀ i, IsSimpleModule (symGroupImage k (Fin N → k) n) (S' i))
    (hS'_dist : ∀ i j,
      Nonempty (↥(S' i) ≃ₗ[symGroupImage k (Fin N → k) n] ↥(S' j)) → i = j)
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (L_carrier : ∀ i, (L i : Type u) ≃ₗ[k]
      (↥(S' i) →ₗ[symGroupImage k (Fin N → k) n] TensorPower k (Fin N → k) n))
    (h_act : ∀ (i : ι) (g : Matrix.GeneralLinearGroup (Fin N) k)
        (l : (L i : Type u)) (v : ↥(S' i)),
        (L_carrier i ((L i).ρ g l)) v =
          PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val)
            ((L_carrier i l) v)) :
    Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))) := by
  classical
  haveI : FaithfulSMul (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n) := symGroupImage_faithfulSMul k (Fin N → k) n
  haveI hsimp : ∀ i, IsSimpleModule (symGroupImage k (Fin N → k) n) (S' i) := hS'_simp
  intro i j hij
  rintro ⟨f⟩
  apply hij
  -- Underlying `k`-linear equiv of the FDRep iso, with its `g`-equivariance.
  set φ : (L i : Type u) ≃ₗ[k] (L j : Type u) := FDRep.isoToLinearEquiv f with hφdef
  have hφ : ∀ (h : Matrix.GeneralLinearGroup (Fin N) k) (x : (L i : Type u)),
      φ ((L i).ρ h x) = (L j).ρ h (φ x) := by
    intro h x
    have hc := FDRep.Iso.conj_ρ f h
    have hconj : (FDRep.isoToLinearEquiv f).conj ((L i).ρ h) (φ x) = φ ((L i).ρ h x) := by
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      change φ (((L i).ρ h) (φ.symm (φ x))) = φ (((L i).ρ h) x)
      rw [φ.symm_apply_apply]
    rw [← hconj, hc]
  -- The transported `k`-linear equiv of multiplicity spaces.
  set ψ : (↥(S' i) →ₗ[symGroupImage k (Fin N → k) n] TensorPower k (Fin N → k) n)
      ≃ₗ[k] (↥(S' j) →ₗ[symGroupImage k (Fin N → k) n] TensorPower k (Fin N → k) n) :=
    (L_carrier i).symm.trans (φ.trans (L_carrier j)) with hψdef
  -- Upgrade `ψ` to a `C`-linear equiv (Part 1) and conclude `i = j` (Part 2). The
  -- intertwining goal is produced by *specializing* Part 1's `•` signature
  -- (`refine … ?_`), so the centralizer `•` is never synthesized freshly here;
  -- the proof of that goal stays entirely `•`-free via `unitTensorPowCentralizer_smul_eq`.
  refine multiplicitySpace_Cdistinct k (TensorPower k (Fin N → k) n)
    (symGroupImage k (Fin N → k) n) S' hS'_dist i j
    ⟨homACentralizerLinearEquivOfUnitTensorPowIntertwine ψ ?_⟩
  intro g l
  obtain ⟨h, hgh⟩ := exists_gl_mulVecLin_eq g
  -- The `•`-free key relation: post-composition by `D = centralizerToEndA … g^{⊗n}`
  -- corresponds under `L_carrier m` to the `GL_N` action `(L m).ρ h`.
  have hrel : ∀ (m : ι) (y : (L m : Type u)),
      (centralizerToEndA k (TensorPower k (Fin N → k) n) (symGroupImage k (Fin N → k) n)
          (unitTensorPowCentralizer g n)).comp (L_carrier m y)
        = L_carrier m ((L m).ρ h y) := by
    intro m y
    refine LinearMap.ext fun v => ?_
    rw [h_act m h y v]
    -- `(D.comp (L_carrier m y)) v = D ((L_carrier m y) v) = g^{⊗n} ((L_carrier m y) v)`
    -- (defeq through `centralizerToEndA`/`unitTensorPowCentralizer`), then match the
    -- diagonal-action map functions via `hgh : mulVecLin h.val = g`.
    show PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k (Fin N → k)))
          ((L_carrier m y) v)
        = PiTensorProduct.map (R := k)
            (fun _ : Fin n => Matrix.mulVecLin (R := k) (h : Matrix (Fin N) (Fin N) k))
            ((L_carrier m y) v)
    rw [show (fun _ : Fin n => Matrix.mulVecLin (R := k) (h : Matrix (Fin N) (Fin N) k))
        = (fun _ : Fin n => (g : Module.End k (Fin N → k))) from funext fun _ => hgh]
  -- Reduce the centralizer `•` goal to its `•`-free form and chain the relations.
  simp only [unitTensorPowCentralizer_smul_eq, hψdef, LinearEquiv.trans_apply]
  have e1 : (L_carrier i).symm
        ((centralizerToEndA k (TensorPower k (Fin N → k) n) (symGroupImage k (Fin N → k) n)
            (unitTensorPowCentralizer g n)).comp l)
      = (L i).ρ h ((L_carrier i).symm l) := by
    apply (L_carrier i).injective
    rw [LinearEquiv.apply_symm_apply, ← hrel i ((L_carrier i).symm l),
      LinearEquiv.apply_symm_apply]
  rw [e1, hφ h ((L_carrier i).symm l), ← hrel j (φ ((L_carrier i).symm l))]

end GLDistinct

end Etingof
