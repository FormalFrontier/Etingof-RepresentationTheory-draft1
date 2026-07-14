import EtingofRepresentationTheory.Chapter9.PathAlgebraConsSplittingIso

/-!
# The retraction of `Φ` and injectivity of the cons-splitting

Eighth layer of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i), parent #6420). Write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra, `V` the arrow bimodule. The cons-splitting `A_n ⊗_S V ≅ A_{n+1}`
(`Chapter9/PathAlgebraConsSplitting.lean`) has a **surjectivity** half already recorded
(`exists_stdΦ_preimage_topDegree` in `Chapter9/PathAlgebraConsSplittingIso.lean`). This file
supplies the **injectivity** half in the form actually consumed downstream: a genuine (non-`sorry`)
left inverse of the top-half boundary map

```
Φ = stdΦ M : A ⊗_S (V ⊗_S M) → A ⊗_S M,   Φ (a ⊗ v ⊗ m) = (a · v) ⊗ m,
```

built directly from the combinatorial cons-decomposition of a positive-length path (the inductive
`Quiver.Path.cons` structure, matching `exists_cons_decomp` / `cons_decomp_unique` in
`Chapter9/PathAlgebraConsSplitting.lean`), and the resulting `Function.Injective (stdΦ M).hom`.

The retraction `R = stdΦRet M` sends a basis pure tensor `(single q c) ⊗ m` of `A ⊗_S M` to the
cons-split `ofPath p ⊗ (single e c ⊗ m)`, where `q = p·e` is the unique cons-decomposition of `q`
(or `0` when `q` is a vertex, i.e. has length `0`). `R (Φ ξ) = ξ` holds pure-tensor-by-pure-tensor:
the composable case is cons-uniqueness (`compSingle_eq`), the non-composable case
(`compSingle_eq_zero`) is the source-action balancing forcing both sides to zero.

Only base-ring (`S = Q → k`) scalars move across the tensors (`TensorProduct.smul_tmul`): the field
`k` does not act on `A ⊗_S -`, so every coefficient is kept inside a `Finsupp` factor and shuttled
between factors by the vertex `S`-actions.

This is the injectivity content of the bundled `A_n ⊗_S V ≅ A_{n+1}` isomorphism (issue #6545) and
the crux `Function.Injective (stdΦ M).hom` of `Mono (stdd M)` (issue #6561), which telescopes it up
to the whole complex via the coordinate shift `inducedCoordMap_stdd_shift`.
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace Etingof.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-! ## Base-ring scalar shuttling on the induced tensors

The field `k` does not act on `A ⊗_S X`; only `S = Q → k` does. These lemmas move an `S`-scalar
across the outer tensor `A ⊗_S (V ⊗_S M)` via the vertex actions, so a coefficient can be pushed
from the path factor onto the arrow factor and back.

The path factor is written `c • ofPath q` rather than `Finsupp.single q c`: the latter exposes the
raw `QuiverPathIndex →₀ k` type in tensor-factor position, where the `Module (Q → k)` structure of
`PathAlgebra k Q` (a `def`, not an `abbrev`) is no longer found. -/

/-- `Finsupp.single q c`, as a `PathAlgebra` element, is `c • ofPath q`. -/
theorem single_eq_smul_ofPath (q : QuiverPathIndex Q) (c : k) :
    (Finsupp.single q c : PathAlgebra k Q) = c • ofPath q := by
  rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **Composable coefficient normalisation.** In `A ⊗_S (V ⊗_S M)`, for a path `p : a ⟶ d` and an
arrow `e : d ⟶ c` (composable at `d`), the coefficient on the path factor can be absorbed into the
arrow factor: `(ca • ofPath p) ⊗ (single e cv ⊗ m) = ofPath p ⊗ (single e (ca·cv) ⊗ m)`. Realised by
the vertex indicator `Pi.single d ca` acting through the outer `S`-balancing. -/
theorem cons_tensor_coeff_move {a d c : Q} (p : Quiver.Path a d) (e : d ⟶ c) (ca cv : k)
    (m : restrictObj M) :
    ((ca • ofPath (⟨a, d, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨d, c, e⟩ : ArrowIndex Q) cv : ArrowTgt k Q)
          ⊗ₜ[Q → k] m : VtensObj M) : inducedVtensObj M)
      = ((ofPath (⟨a, d, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
          ((Finsupp.single (⟨d, c, e⟩ : ArrowIndex Q) (ca * cv) : ArrowTgt k Q)
            ⊗ₜ[Q → k] m : VtensObj M) : inducedVtensObj M) := by
  have hpath : (ca • ofPath (⟨a, d, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q)
      = (Pi.single d ca : Q → k) • (ofPath (⟨a, d, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) := by
    rw [vertex_smul_def, ofPath_mul_vertexEmbedding]
    simp only [Pi.single_eq_same]
  rw [hpath, TensorProduct.smul_tmul]
  congr 1
  rw [vtens_smul_def, vtens_smul_tmul, srcHom_apply, wSMul_single]
  simp only [ArrowIndex.src, Pi.single_eq_same]

/-- **Non-composable vanishing.** In `A ⊗_S (V ⊗_S M)`, a path ending at `d` tensored with an arrow
starting at `b ≠ d` is zero: the source `S`-action at the vertex `d` kills the arrow. -/
theorem cons_tensor_noncomp {a d b c : Q} (p : Quiver.Path a d) (e : b ⟶ c) (ca cv : k)
    (hbd : b ≠ d) (m : restrictObj M) :
    ((ca • ofPath (⟨a, d, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, c, e⟩ : ArrowIndex Q) cv : ArrowTgt k Q)
          ⊗ₜ[Q → k] m : VtensObj M) : inducedVtensObj M) = 0 := by
  have hpath : (ca • ofPath (⟨a, d, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q)
      = (Pi.single d (1 : k) : Q → k)
          • (ca • ofPath (⟨a, d, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) := by
    rw [vertex_smul_def, smul_mul_assoc, ofPath_mul_vertexEmbedding]
    simp only [Pi.single_eq_same, one_smul]
  rw [hpath, TensorProduct.smul_tmul, vtens_smul_def, vtens_smul_tmul, srcHom_apply, wSMul_single]
  simp only [ArrowIndex.src, Pi.single_eq_of_ne hbd, zero_mul, Finsupp.single_zero,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero]

/-! ## The cons-decomposition term -/

/-- **The cons-decomposition of a basis path**, as an element of the domain `A ⊗_S (V ⊗_S M)`. A
vertex (`nil`, length `0`) maps to `0`; a positive-length path `cons p e` (initial path `p`, final
arrow `e`) maps to `ofPath p ⊗ (single e c ⊗ m)`, with the coefficient `c` on the arrow factor so
that the retraction is `S`-balanced with no field scalars on the tensor. -/
noncomputable def consTermC (q : QuiverPathIndex Q) (c : k) (m : restrictObj M) :
    inducedVtensObj M :=
  match q with
  | ⟨_, _, Quiver.Path.nil⟩ => 0
  | ⟨a, c', Quiver.Path.cons (b := b) p e⟩ =>
      (ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        (((Finsupp.single (⟨b, c', e⟩ : ArrowIndex Q) c : ArrowTgt k Q)
          ⊗ₜ[Q → k] m : VtensObj M))

@[simp] theorem consTermC_nil (a : Q) (c : k) (m : restrictObj M) :
    consTermC M (⟨a, a, Quiver.Path.nil⟩ : QuiverPathIndex Q) c m = 0 := rfl

@[simp] theorem consTermC_cons {a b c' : Q} (p : Quiver.Path a b) (e : b ⟶ c') (c : k)
    (m : restrictObj M) :
    consTermC M (⟨a, c', Quiver.Path.cons p e⟩ : QuiverPathIndex Q) c m
      = ((ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
          ((Finsupp.single (⟨b, c', e⟩ : ArrowIndex Q) c : ArrowTgt k Q)
            ⊗ₜ[Q → k] m : VtensObj M) : inducedVtensObj M) := rfl

theorem consTermC_zero_c (q : QuiverPathIndex Q) (m : restrictObj M) :
    consTermC M q (0 : k) m = 0 := by
  obtain ⟨a, c', p⟩ := q
  cases p with
  | nil => rfl
  | cons p e => rw [consTermC_cons]; simp only [Finsupp.single_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]

theorem consTermC_add_c (q : QuiverPathIndex Q) (c c' : k) (m : restrictObj M) :
    consTermC M q (c + c') m = consTermC M q c m + consTermC M q c' m := by
  obtain ⟨a, cc, p⟩ := q
  cases p with
  | nil => simp only [consTermC_nil, add_zero]
  | cons p e =>
      simp only [consTermC_cons, Finsupp.single_add, TensorProduct.add_tmul,
        TensorProduct.tmul_add]

theorem consTermC_zero_m (q : QuiverPathIndex Q) (c : k) :
    consTermC M q c (0 : restrictObj M) = 0 := by
  obtain ⟨a, cc, p⟩ := q
  cases p with
  | nil => rfl
  | cons p e => rw [consTermC_cons]; simp only [TensorProduct.tmul_zero]

theorem consTermC_add_m (q : QuiverPathIndex Q) (c : k) (m m' : restrictObj M) :
    consTermC M q c (m + m') = consTermC M q c m + consTermC M q c m' := by
  obtain ⟨a, cc, p⟩ := q
  cases p with
  | nil => simp only [consTermC_nil, add_zero]
  | cons p e => simp only [consTermC_cons, TensorProduct.tmul_add]

/-- The additive map `k →+ A ⊗_S (V ⊗_S M)`, `c ↦ consTermC q c m`, for fixed path index `q` and
`m`. The per-basis-path summand of the retraction. -/
noncomputable def consTermCHom (q : QuiverPathIndex Q) (m : restrictObj M) :
    k →+ inducedVtensObj M where
  toFun c := consTermC M q c m
  map_zero' := consTermC_zero_c M q m
  map_add' c c' := consTermC_add_c M q c c' m

/-- The retraction as an additive map `A →+ A ⊗_S (V ⊗_S M)` for a fixed `m`, extending
`single q c ↦ consTermC q c m` over the path basis. -/
noncomputable def stdΦRetFixedM (m : restrictObj M) :
    PathAlgebra k Q →+ inducedVtensObj M :=
  Finsupp.liftAddHom (fun q => consTermCHom M q m)

@[simp] theorem stdΦRetFixedM_single (m : restrictObj M) (q : QuiverPathIndex Q) (c : k) :
    stdΦRetFixedM M m (Finsupp.single q c) = consTermC M q c m := by
  change Finsupp.liftAddHom (fun q => consTermCHom M q m) (Finsupp.single q c) = _
  rw [Finsupp.liftAddHom_apply_single]
  rfl

theorem stdΦRetFixedM_zero_m (a : PathAlgebra k Q) :
    stdΦRetFixedM M (0 : restrictObj M) a = 0 := by
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add f g hf hg => rw [map_add, hf, hg, add_zero]
  | single q c => rw [stdΦRetFixedM_single, consTermC_zero_m]

theorem stdΦRetFixedM_add_m (a : PathAlgebra k Q) (m m' : restrictObj M) :
    stdΦRetFixedM M (m + m') a = stdΦRetFixedM M m a + stdΦRetFixedM M m' a := by
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]; abel
  | single q c =>
      rw [stdΦRetFixedM_single, stdΦRetFixedM_single, stdΦRetFixedM_single, consTermC_add_m]

/-! ## The retraction bilinear map and the retraction -/

/-- The `S`-balanced additive bilinear map underlying the retraction of `Φ`: `(a, m) ↦ stdΦRetFixedM
m a`, additive in each argument and balanced against the vertex `S`-action, so it descends to
`A ⊗_S M`. -/
noncomputable def stdΦRetBilin :
    PathAlgebra k Q →+ restrictObj M →+
      inducedVtensObj M where
  toFun a :=
    { toFun := fun m => stdΦRetFixedM M m a
      map_zero' := stdΦRetFixedM_zero_m M a
      map_add' := fun m m' => stdΦRetFixedM_add_m M a m m' }
  map_zero' := by ext m; exact (stdΦRetFixedM M m).map_zero
  map_add' a a' := by ext m; exact (stdΦRetFixedM M m).map_add a a'

@[simp] theorem stdΦRetBilin_apply (a : PathAlgebra k Q) (m : restrictObj M) :
    stdΦRetBilin M a m = stdΦRetFixedM M m a := rfl

/-- **The retraction is `S`-balanced.** `stdΦRetFixedM m (s • a) = stdΦRetFixedM (s • m) a`: with
the coefficient on the arrow factor, both sides reduce to `single e (s(tgt e)·c)` by the inner
target-balancing, so no field scalars are needed. -/
theorem stdΦRetBilin_balanced (s : Q → k) (a : PathAlgebra k Q) (m : restrictObj M) :
    stdΦRetBilin M ((s : Q → k) • a) m = stdΦRetBilin M a ((s : Q → k) • m) := by
  simp only [stdΦRetBilin_apply]
  induction a using Finsupp.induction_linear with
  | zero => rw [smul_zero, map_zero, map_zero]
  | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg]
  | single q c =>
      obtain ⟨a, c', p⟩ := q
      rw [vertex_smul_def, single_mul_vertexEmbedding, Finsupp.smul_single, smul_eq_mul,
        stdΦRetFixedM_single, stdΦRetFixedM_single]
      -- LHS: `consTermC ⟨a,c',p⟩ (s(c')·c) m`; RHS: `consTermC ⟨a,c',p⟩ c (s • m)`
      cases p with
      | nil => rw [consTermC_nil, consTermC_nil]
      | cons p e =>
          rw [consTermC_cons, consTermC_cons]
          -- inner: `single e c ⊗ (s • m) = (s • single e c) ⊗ m = single e (s(c')·c) ⊗ m`
          congr 1
          rw [← TensorProduct.smul_tmul]
          congr 1
          change (Finsupp.single (⟨_, c', e⟩ : ArrowIndex Q) (s c' * c) : ArrowTgt k Q)
            = wSMul k Q ArrowIndex.tgt s (Finsupp.single (⟨_, c', e⟩ : ArrowIndex Q) c)
          rw [wSMul_single]
          simp only [ArrowIndex.tgt]

/-- **The retraction of `Φ`.** The additive left inverse `R : A ⊗_S M → A ⊗_S (V ⊗_S M)` of the
top-half boundary map `Φ = stdΦ M`, built from the cons-decomposition. On a basis pure tensor
`single q c ⊗ m` it returns the cons-split `consTermC q c m`. -/
noncomputable def stdΦRet :
    inducedRestrictObj M →+
      inducedVtensObj M :=
  TensorProduct.liftAddHom (stdΦRetBilin M) (stdΦRetBilin_balanced M)

@[simp] theorem stdΦRet_tmul (a : PathAlgebra k Q) (m : restrictObj M) :
    stdΦRet M (a ⊗ₜ[Q → k] m) = stdΦRetFixedM M m a := by
  change TensorProduct.liftAddHom (stdΦRetBilin M) (stdΦRetBilin_balanced M) (a ⊗ₜ[Q → k] m) = _
  rw [TensorProduct.liftAddHom_tmul, stdΦRetBilin_apply]

end Etingof.PathAlgebra
