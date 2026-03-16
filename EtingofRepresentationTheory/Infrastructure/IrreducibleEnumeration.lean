import Mathlib

/-!
# Infrastructure: Wedderburn-Artin Decomposition for Group Algebras

This file connects Mathlib's Wedderburn-Artin theorem to the representation theory
of finite groups. For a finite group G over an algebraically closed field k with
char(k) ∤ |G|, we establish:

1. `MonoidAlgebra k G` is a finite-dimensional semisimple k-algebra
2. By Wedderburn-Artin, `k[G] ≃ₐ[k] Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`
3. The dimension formula `|G| = Σ i, (d i)²`
4. The number of components `n` corresponds to the number of isomorphism classes
   of simple `FDRep k G` objects

## References

- Etingof, *Introduction to Representation Theory*, Theorem 4.1.1
- Mathlib: `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
- Mathlib: `Rep.equivalenceModuleMonoidAlgebra`
-/

open CategoryTheory

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]

/-! ### Finite-dimensionality and semisimplicity of k[G] -/

omit [Fintype G] in
noncomputable instance MonoidAlgebra.instFiniteDimensional [Finite G] :
    FiniteDimensional k (MonoidAlgebra k G) :=
  inferInstance

omit [Fintype G] in
instance MonoidAlgebra.instIsSemisimpleRing [Finite G] [NeZero (Nat.card G : k)] :
    IsSemisimpleRing (MonoidAlgebra k G) :=
  inferInstance

/-! ### Wedderburn-Artin decomposition -/

omit [Fintype G] in
/-- The Wedderburn-Artin decomposition of `k[G]`: there exist `n` matrix blocks of sizes
`d i` such that `k[G] ≃ₐ[k] Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`.
This is a direct application of `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`. -/
theorem MonoidAlgebra.wedderburnArtin [Finite G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    (F := k) (R := MonoidAlgebra k G)

/-! ### IrrepDecomp structure -/

/-- Bundled Wedderburn-Artin decomposition data for the group algebra `k[G]`.
Packages the number of irreducible representations `n`, their dimensions `d`,
and the algebra isomorphism. -/
structure IrrepDecomp (k G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] where
  /-- Number of isomorphism classes of irreducible representations -/
  n : ℕ
  /-- Dimensions of the irreducible representations -/
  d : Fin n → ℕ
  /-- Each dimension is positive -/
  d_pos : ∀ i, NeZero (d i)
  /-- The Wedderburn-Artin algebra isomorphism -/
  iso : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k

/-- Existence of the irreducible decomposition. -/
noncomputable def IrrepDecomp.mk' [NeZero (Nat.card G : k)] :
    IrrepDecomp k G := by
  choose n d hd he using MonoidAlgebra.wedderburnArtin (k := k) (G := G)
  exact ⟨n, d, hd, he.some⟩

/-! ### Dimension formula -/

omit [IsAlgClosed k] [Group G] in
/-- The dimension of `k[G]` equals `|G|`. -/
theorem MonoidAlgebra.finrank_eq_card :
    Module.finrank k (MonoidAlgebra k G) = Fintype.card G := by
  change Module.finrank k (G →₀ k) = _
  simp

omit [IsAlgClosed k] [Group G] [Fintype G] in
/-- The dimension of a product of matrix algebras is the sum of squares of the sizes. -/
theorem finrank_pi_matrix (n : ℕ) (d : Fin n → ℕ) :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) =
      ∑ i, (d i) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  congr 1
  ext i
  simp [Module.finrank_matrix, Fintype.card_fin, sq]

/-- **Sum-of-squares formula**: `|G| = Σ i, (d i)²` where `d i` are the dimensions of the
irreducible representations of G. This is the key dimension identity from Theorem 4.1.1(ii). -/
theorem IrrepDecomp.sum_sq_eq_card [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∑ i, (D.d i) ^ 2 = Fintype.card G := by
  have hfr := MonoidAlgebra.finrank_eq_card (k := k) (G := G)
  have hiso := D.iso.toLinearEquiv.finrank_eq
  rw [hfr] at hiso
  rw [finrank_pi_matrix] at hiso
  omega

/-! ### Helper lemmas for FDRep connection -/

/-- Column vectors `Fin n → k` form a simple module over `Matrix (Fin n) (Fin n) k`.
For any nonzero vector `w`, the orbit `Mat_n(k) · w` spans all of `k^n`. -/
instance Matrix.instIsSimpleModule {k : Type*} [Field k] (n : ℕ) [NeZero n] :
    IsSimpleModule (Matrix (Fin n) (Fin n) k) (Fin n → k) where
  eq_bot_or_eq_top m := by
    by_cases hm : m = ⊥
    · left; exact hm
    · right; rw [Submodule.eq_top_iff']
      intro v
      obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra h; push_neg at h; exact hwne (funext h)
      -- For any target v, construct M with M.mulVec w = v
      let M : Matrix (Fin n) (Fin n) k := fun j l => if l = i then v j * (w i)⁻¹ else 0
      have : M.mulVec w = v := by
        ext j; simp only [Matrix.mulVec, M, dotProduct]; simp [mul_assoc, inv_mul_cancel₀ hi]
      rw [← this]; exact m.smul_mem M hw

/-- If `f : R →+* S` is surjective and `M` is a simple `S`-module, then `M` is a simple
`R`-module via `Module.compHom`. R-submodules equal S-submodules since every S-scalar
is in the image of `f`. -/
lemma IsSimpleModule.compHom {R S M : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : Function.Surjective f) [hM : IsSimpleModule S M] :
    @IsSimpleModule R _ M _ (Module.compHom M f) := by
  letI : Module R M := Module.compHom M f
  have key : ∀ m : Submodule R M, m = ⊥ ∨ m = ⊤ := by
    intro m
    let m' : Submodule S M := {
      toAddSubmonoid := m.toAddSubmonoid
      smul_mem' := fun s x hx => by obtain ⟨r, rfl⟩ := hf s; exact m.smul_mem r hx
    }
    have hcarrier : ∀ x, x ∈ m' ↔ x ∈ m := fun _ => Iff.rfl
    cases hM.eq_bot_or_eq_top m' with
    | inl h =>
      left; ext x; constructor
      · intro hx; have := (hcarrier x).mpr hx; rw [h] at this; simpa using this
      · intro hx; simp at hx; rw [hx]; exact m.zero_mem'
    | inr h =>
      right; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _; exact (hcarrier x).mp (h ▸ Submodule.mem_top)
  haveI : Nontrivial (Submodule R M) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    obtain ⟨a, b, hab⟩ := @IsSimpleModule.nontrivial S _ M _ _ hM
    have ha : a ∈ (⊥ : Submodule R M) := by rw [h]; exact trivial
    have hb : b ∈ (⊥ : Submodule R M) := by rw [h]; exact trivial
    simp at ha hb; exact hab (ha ▸ hb.symm)
  exact { eq_bot_or_eq_top := key }

/-! ### Column vector representations -/

/-- The projection ring homomorphism from `k[G]` to the i-th matrix factor
of the Wedderburn-Artin decomposition. -/
noncomputable def IrrepDecomp.projRingHom [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    MonoidAlgebra k G →+* Matrix (Fin (D.d i)) (Fin (D.d i)) k :=
  (Pi.evalRingHom (fun i => Matrix (Fin (D.d i)) (Fin (D.d i)) k) i).comp
    D.iso.toRingEquiv.toRingHom

/-- The projection to the i-th factor is surjective (since `D.iso` is an isomorphism). -/
lemma IrrepDecomp.projRingHom_surjective [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Function.Surjective (D.projRingHom i) := by
  intro M
  exact ⟨D.iso.symm (Pi.single i M), by simp [projRingHom, Pi.evalRingHom, Pi.single]⟩

/-- The column vector representation: `G` acts on `Fin (D.d i) → k` via the i-th matrix factor
of the Wedderburn-Artin decomposition. -/
noncomputable def IrrepDecomp.columnRep [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Representation k G (Fin (D.d i) → k) where
  toFun g := Matrix.mulVecLin (D.projRingHom i (MonoidAlgebra.of k G g))
  map_one' := by rw [map_one, map_one, Matrix.mulVecLin_one]; rfl
  map_mul' g h := by rw [map_mul, map_mul, Matrix.mulVecLin_mul]; rfl

/-- The column vector FDRep: the i-th irreducible representation of G. -/
noncomputable def IrrepDecomp.columnFDRep [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) : FDRep k G :=
  FDRep.of (D.columnRep i)

/-- The dimension of the i-th column vector representation equals `D.d i`. -/
lemma IrrepDecomp.finrank_columnFDRep [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Module.finrank k (D.columnFDRep i) = D.d i := by
  simp [columnFDRep, FDRep.of]

/-! ### Connection to FDRep -/

/-- The number of Wedderburn-Artin components equals the number of isomorphism classes
of simple `FDRep k G` objects. This is a key structural result connecting the algebraic
decomposition to the representation-theoretic classification.

The proof requires establishing that simple `MonoidAlgebra k G`-modules correspond
bijectively to simple objects in `FDRep k G`. Mathlib provides the equivalence
`Rep.equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat k[G]` but the finite-dimensional
restriction `FDRep k G ≌ FGModuleCat k[G]` is not yet formalized. -/
theorem IrrepDecomp.n_eq_card_simples [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∃ (V : Fin D.n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) := by
  refine ⟨D.columnFDRep, ?_, ?_, ?_⟩
  -- Simplicity: each columnFDRep is simple
  -- Proved helpers: Matrix.instIsSimpleModule, IsSimpleModule.compHom, projRingHom_surjective
  -- Missing link: connecting IsSimpleModule k[G] to Simple (FDRep k G)
  · intro i; sorry
  -- Injectivity: non-isomorphic for distinct indices
  -- Key idea: if V_i ≅ V_j then dim(V_i) = dim(V_j) AND the k[G]-module structures
  -- factor through different matrix blocks, so annihilator ideals differ
  · intro i j hij; sorry
  -- Surjectivity: every simple FDRep is isomorphic to some columnFDRep
  -- Key idea: a simple FDRep gives a simple k[G]-module, which must be one of the
  -- column vector modules (classification of simples over semisimple algebras)
  · intro W hW; sorry

/-- Each dimension `d i` in the Wedderburn-Artin decomposition equals the
`Module.finrank k` of the corresponding irreducible representation. -/
theorem IrrepDecomp.d_eq_finrank [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∀ i, D.d i = Module.finrank k (V i) := by
  sorry
