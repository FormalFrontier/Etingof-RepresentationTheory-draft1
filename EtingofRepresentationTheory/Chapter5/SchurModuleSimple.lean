import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import EtingofRepresentationTheory.Chapter5.SchurModuleSpecialBlock
import EtingofRepresentationTheory.Chapter5.PrimitiveIdempotentSimplicity

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

/-! ## C-4a aggregation

`schurModuleSubmodule_isSimple_centralizer` aggregates the C-4a sub-pieces over `ℂ`:
* sub-α: bimodule decomposition `Theorem5_18_4_bimodule_decomposition_explicit`;
* sub-A (#4634): `exists_unique_special_block` — the unique block labelled
  `weightToPartition N lam`;
* sub-β: off-block vanishing (`youngSym_action_vanishes_off_block`);
* sub-γ: rank-1 scaled projection (`youngSym_action_on_special_block_rank_one_scaled_proj`);
* C-4a-ii: `image_of_primitive_idempotent_isSimple_centralizer`.

The two substantial steps are factored as `schurBlock_imageSubmoduleB_isSimple`
(the interface application, simplicity of `imageSubmoduleB c` over the centralizer)
and the transfer to `diagonalActionImage`/`SchurModuleSubmodule`. -/

section CAggregation

variable (N : ℕ) (lam : Fin N → ℕ)

/-- `n ≤ Module.finrank ℂ (Fin N → ℂ)`, the dimension bound needed by the
bimodule decomposition and the centralizer equality. -/
private lemma finrank_bound (hN : (∑ i, lam i) ≤ N) :
    (∑ i, lam i) ≤ Module.finrank ℂ (Fin N → ℂ) := by
  rw [Module.finrank_pi, Fintype.card_fin]; exact hN

/-- The Young-symmetrizer endomorphism preserves each `symGroupImage`-stable
submodule (as a `ℂ`-submodule via `restrictScalars`). The membership proof used
to build `LinearMap.restrict`; proof-irrelevant, so it matches the (private)
proof inside the off-block / rank-one lemmas. -/
private lemma youngSymEndo_mem_restrictScalars
    (S : Submodule (symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))
      (TensorPower ℂ (Fin N → ℂ) (∑ i, lam i)))
    (x : TensorPower ℂ (Fin N → ℂ) (∑ i, lam i))
    (hx : x ∈ S.restrictScalars ℂ) :
    youngSymEndomorphism ℂ N lam x ∈ S.restrictScalars ℂ := by
  rw [Submodule.restrictScalars_mem] at hx ⊢
  have h := S.smul_mem (youngSymElement ℂ N lam) hx
  rwa [Subalgebra.smul_def, Module.End.smul_def, youngSymElement_val] at h

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- **Schur-Weyl L_i, C-4a interface step.** The image of the Young symmetrizer
`c = youngSymElement ℂ N lam`, packaged as `imageSubmoduleB c`, is simple as a
module over `centralizer(symGroupImage)`. This is the application of
`image_of_primitive_idempotent_isSimple_centralizer` to the explicit Schur-Weyl
bimodule decomposition, feeding it off-block vanishing (sub-β) and the rank-1
scaled projection on the special block (sub-γ). -/
private theorem schurBlock_imageSubmoduleB_isSimple
    (hlam : Antitone lam) (hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule
      (↥(Subalgebra.centralizer ℂ
        (symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i) :
          Set (Module.End ℂ (TensorPower ℂ (Fin N → ℂ) (∑ i, lam i))))))
      ↥(imageSubmoduleB (youngSymElement ℂ N lam)) := by
  classical
  have hN' : (∑ i, lam i) ≤ Module.finrank ℂ (Fin N → ℂ) := finrank_bound N lam hN
  -- sub-α: explicit bimodule decomposition.
  obtain ⟨ι, _, _, S, hSimp, hDist, hSfin, _hLsimp, e, he⟩ :=
    Theorem5_18_4_bimodule_decomposition_explicit
      (k := ℂ) (V := Fin N → ℂ) (n := ∑ i, lam i) hN'
  haveI : IsSemisimpleModule (symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i))
      (TensorPower ℂ (Fin N → ℂ) (∑ i, lam i)) := IsSemisimpleRing.isSemisimpleModule
  -- sub-A (#4634): the unique special block.
  obtain ⟨iLam, hLabel_iLam, hLabel_other⟩ :=
    exists_unique_special_block N lam hlam S hSimp hDist hSfin e he
  -- The scalar `α` with `c² = α • c` (directly over ℂ); nonvanishing is deferred
  -- to the reconciliation `α = α'` below (`α'` is the rank-1 lemma's nonzero scalar).
  obtain ⟨α, hα_sq⟩ := YoungSymmetrizerK_sq_scalar ℂ (∑ i, lam i) (weightToPartition N lam)
  -- `c = youngSymElement`, with `c² = α • c`.
  have hc_sq : youngSymElement ℂ N lam * youngSymElement ℂ N lam =
      α • youngSymElement ℂ N lam := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_smul, youngSymElement_val]
    exact youngSymEndomorphism_sq_scalar ℂ N lam α hα_sq
  -- The per-block `ℂ`-linear maps `f i = c|_{S i}`.
  let f : ∀ i, ↥(S i) →ₗ[ℂ] ↥(S i) := fun i =>
    (youngSymEndomorphism ℂ N lam).restrict
      (p := (S i).restrictScalars ℂ) (q := (S i).restrictScalars ℂ)
      (youngSymEndo_mem_restrictScalars N lam (S i))
  -- Block factorization (sub-(1)).
  have hf_block : ∀ (i : ι) (v : ↥(S i))
      (l : ↥(S i) →ₗ[symGroupImage ℂ (Fin N → ℂ) (∑ i, lam i)]
        TensorPower ℂ (Fin N → ℂ) (∑ i, lam i)),
      e ((youngSymElement ℂ N lam).val (e.symm (DirectSum.of _ i (v ⊗ₜ[ℂ] l)))) =
        DirectSum.of _ i (f i v ⊗ₜ[ℂ] l) := by
    intro i v l
    exact youngSym_block_factorization ℂ N lam S e he i v l
  -- sub-β: off blocks vanish.
  have hf_zero : ∀ i, i ≠ iLam → f i = 0 := by
    intro i hi
    obtain ⟨la', hla'_ne, hla'_trace⟩ := hLabel_other i hi
    haveI : Module.Finite ℂ ↥((S i).restrictScalars ℂ) := hSfin i
    exact youngSym_action_vanishes_off_block N lam (S i) la' hla'_trace hla'_ne
  -- sub-γ: rank-1 scaled projection on the special block.
  haveI : Module.Finite ℂ ↥((S iLam).restrictScalars ℂ) := hSfin iLam
  obtain ⟨α', π', hα'_ne, hπ'_idem, hπ'_rank, hf_eq_raw⟩ :=
    youngSym_action_on_special_block_rank_one_scaled_proj N lam (S iLam) hLabel_iLam
  have hf_eq : f iLam = α' • π' := hf_eq_raw
  -- Reconcile `α' = α` using `f iLam² = α • f iLam` and `f iLam = α' • π'`.
  have hf_sq : f iLam * f iLam = α • f iLam :=
    youngSymEndomorphism_restrict_sq_scalar (k := ℂ) N lam (S iLam) α hα_sq
  have hπ'_ne : π' ≠ 0 := by
    intro h0
    rw [h0, LinearMap.range_zero, finrank_bot] at hπ'_rank
    exact one_ne_zero hπ'_rank.symm
  have hαeq : α' = α := by
    have h1 : f iLam * f iLam = (α' * α') • π' := by
      rw [hf_eq, smul_mul_smul_comm, hπ'_idem]
    have h2 : α • f iLam = (α * α') • π' := by rw [hf_eq, smul_smul]
    have key : (α' * α') • π' = (α * α') • π' := by rw [← h1, hf_sq, h2]
    have hscal : α' * α' = α * α' := smul_left_injective ℂ hπ'_ne key
    exact mul_right_cancel₀ hα'_ne hscal
  have hα_ne : α ≠ 0 := hαeq ▸ hα'_ne
  have hf_special : f iLam = α • π' := by rw [hf_eq, hαeq]
  -- Apply the interface.
  exact image_of_primitive_idempotent_isSimple_centralizer
    (youngSymElement ℂ N lam) α hα_ne hc_sq S e he iLam (hSimp iLam)
    f hf_block hf_zero π' hπ'_idem hπ'_rank hf_special

end CAggregation

/-- **Schur-Weyl L_i, part C-4a (aggregated, over ℂ).**

The Schur module submodule `SchurModuleSubmodule ℂ N λ`, viewed as a
`diagonalActionImage ℂ V n`-module via the canonical action above, is simple.

Equivalently, by `Theorem5_18_4_centralizers` (which requires `n ≤ N`),
it is simple as a `centralizer(symGroupImage)`-module. The proof aggregates
the pieces `sub-α`, `sub-A`, `sub-β`, `sub-γ`, `C-4a-ii` of the C-4a programme via
`image_of_primitive_idempotent_isSimple_centralizer`
(`PrimitiveIdempotentSimplicity.lean`) in `schurBlock_imageSubmoduleB_isSimple`,
then transfers along the centralizer equality `diagonalActionImage = centralizer`
and the carrier identity `imageSubmoduleB c = SchurModuleSubmodule`. -/
theorem schurModuleSubmodule_isSimple_centralizer
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule
      (↥(diagonalActionImage ℂ (Fin N → ℂ) (∑ i, lam i)))
      (SchurModuleSubmodule ℂ N lam) := by
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
    IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
      (Representation.asModule (SchurModule ℂ N lam).ρ) := by
  haveI := schurModuleSubmodule_isSimple_centralizer N lam hlam hN
  refine isSimpleModule_monoidAlgebra_GL_of_centralizer_simple ℂ
    (N := N) (n := ∑ i, lam i)
    (M := ↥(SchurModuleSubmodule ℂ N lam))
    (schurModuleRep ℂ N lam) ?_
  intro g x
  -- Both sides apply `g^⊗n` to `x.val` and re-bundle into `SchurModuleSubmodule`.
  -- LHS: `(schurModuleRep g) x = (glTensorRep g).restrict ... x`.
  -- RHS: `(⟨g^⊗n, _⟩ : diagonalActionImage) • x = ⟨g^⊗n x.val, _⟩`
  -- These are definitionally equal after Subtype.ext.
  apply Subtype.ext
  rfl

end Etingof

end
