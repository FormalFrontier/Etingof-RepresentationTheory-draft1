import EtingofRepresentationTheory.Chapter3.Theorem3_3_1

/-!
# Downstream import/`#check` test for the Theorem 3.3.1 transpose/dual route

This file imports `Chapter3/Theorem3_3_1.lean` and pins the public signatures of the
transpose/dual-route ingredients added for Etingof Theorem 3.3.1:

* `regularDecomp` — the regular-module decomposition `A ≅ ⊕ᵢ dᵢ Vᵢ`;
* `colVec` / `colMap` — the single-factor column building blocks;
* `matrixTransposeSelfDuality` / `matProdTransposeSelfDuality` — the transpose self-duality
  `Mat_d(k) ≅ Mat_d(k)ᵐᵒᵖ` and its product form `A ≅ Aᵐᵒᵖ`;
* `dualMap_injective_of_surjective` — the dual-of-surjection bridge.

Because this file re-elaborates the endpoint statements, it forces a fresh check of their
public API even when cached oleans would otherwise hide a source regression.

See issue #7517.
-/

open scoped DirectSum

-- The public endpoints must remain importable under these names.
#check @regularDecomp
#check @regularDecomp_apply
#check @colVec
#check @colMap
#check @matrixTransposeSelfDuality
#check @matProdTransposeSelfDuality
#check @piMulOppositeRingEquiv
#check @dualMap_injective_of_surjective

-- Signature locks: each `example` fails to elaborate if the corresponding statement drifts.
-- (`regularDecomp`/`regularDecomp_apply` reference the file-local `vModuleProd` action, which
-- is not exported, so they are pinned via `#check` above rather than re-ascribed here.)

/-- Transpose self-duality of a single matrix algebra, as a `k`-algebra isomorphism to the
opposite algebra. -/
example (k : Type*) [Field k] (D : ℕ) :
    Matrix (Fin D) (Fin D) k ≃ₐ[k] (Matrix (Fin D) (Fin D) k)ᵐᵒᵖ :=
  matrixTransposeSelfDuality k D

/-- Transpose self-duality of `A = ⊕ᵢ Mat_{dᵢ}(k)`, as a ring isomorphism `A ≅ Aᵐᵒᵖ`. -/
example {k : Type*} [Field k] {r : ℕ} (d : Fin r → ℕ) :
    MatProd k d ≃+* (MatProd k d)ᵐᵒᵖ :=
  matProdTransposeSelfDuality d

/-- The `k`-dual of a surjection is an injection. -/
example {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {φ : M →ₗ[k] N} (hφ : Function.Surjective φ) : Function.Injective φ.dualMap :=
  dualMap_injective_of_surjective hφ
