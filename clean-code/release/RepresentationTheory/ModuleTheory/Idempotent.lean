/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.ModuleTheory.Idempotent

/-- The linear maps from the span of an idempotent element are equivalent to module elements fixed by that idempotent. -/
@[source_ref "Chapter5/Discussion_proof_of_Lemma5.13.4" (role := primary),
  source_ref "Chapter5/Introduction_5.13" (role := supporting),
  source_ref "Chapter5/Lemma5.13.4" (role := primary)]
noncomputable def linearMapSpanSingletonEquivFixedByIdempotent
    {A : Type*} [Ring A]
    (e : A) (he : IsIdempotentElem e)
    (M : Type*) [AddCommGroup M] [Module A M] :
    (↥(Submodule.span A ({e} : Set A)) →ₗ[A] M) ≃ {m : M // e • m = m} where
  toFun φ :=
    let e' : ↥(Submodule.span A ({e} : Set A)) := ⟨e, Submodule.subset_span rfl⟩
    have he' : e • e' = e' := Subtype.ext (by change e * e = e; exact he.eq)
    ⟨φ e', by rw [← φ.map_smul, he']⟩
  invFun p :=
    { toFun := fun ⟨x, _⟩ => x • p.1
      map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => add_smul x y p.1
      map_smul' := fun a ⟨x, _⟩ => by dsimp; exact mul_smul a x p.1 }
  left_inv φ := by
    ext ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    have he' : e • (⟨e, Submodule.subset_span rfl⟩ :
        ↥(Submodule.span A ({e} : Set A))) = ⟨e, Submodule.subset_span rfl⟩ :=
      Subtype.ext (show e * e = e from he.eq)
    have h1 : (a • e) • φ ⟨e, Submodule.subset_span rfl⟩ =
        a • (e • φ ⟨e, Submodule.subset_span rfl⟩) := mul_smul a e _
    have h2 : e • φ ⟨e, Submodule.subset_span rfl⟩ =
        φ ⟨e, Submodule.subset_span rfl⟩ := by rw [← φ.map_smul, he']
    rw [h1, h2, ← φ.map_smul]; rfl
  right_inv p := Subtype.ext p.2

end RepresentationTheory.ModuleTheory.Idempotent
