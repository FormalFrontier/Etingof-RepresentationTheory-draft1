import EtingofRepresentationTheory.Chapter2.Problem2_7_5_Exhaustive

/-!
# Problem 2.7.5(b): the converse half, and the book's iff

Part (b) of the problem asks *for which `q`* the `q`-Weyl algebra `A = qWeylAlgebra ℂ q` has
finite dimensional representations. That is an iff, and `Problem2_7_5.lean` proves only the
necessary direction: `isOfFinOrder_of_nontrivial_finrep` says that a nonzero finite dimensional
representation forces `q` to be a root of unity (the determinant obstruction of the book's hint,
`q_pow_finrank_eq_one`).

This file supplies the converse. No new mathematics is needed: the classifying family of part (c)
is already a supply of witnesses. For `q` a root of unity of order `n`, the module `V(α,β)` of
`Problem2_7_5_Family.lean` is `n`-dimensional (`fam_finrank`) and simple
(`famModule_isSimpleModule`), so `V(1,1)` is a nonzero finite dimensional representation. The two
directions are then packaged as `isOfFinOrder_iff_exists_nontrivial_finrep`.

## Main results

* `Etingof.Problem2_7_5.fam_isSimpleModule` — simplicity of `V(α,β)`, transported from the
  concrete carrier `Fin N → ℂ` to the parameter-indexed carrier `Fam q α β`.
* `Etingof.Problem2_7_5.exists_nontrivial_finrep_of_isOfFinOrder` — **the converse half of (b)**:
  every root of unity `q` admits a nonzero finite dimensional representation. The witness is a
  genuinely constructed module, not an abstract existence claim: it is `V(1,1)`, of dimension
  exactly `orderOf q`, and it is irreducible.
* `Etingof.Problem2_7_5.isOfFinOrder_iff_exists_nontrivial_finrep` — **Problem 2.7.5(b)**: the
  `q`-Weyl algebra has a nonzero finite dimensional representation iff `q` is a root of unity.
-/

namespace Etingof.Problem2_7_5

open Etingof

section Converse

variable (q α β : ℂˣ)

/-- `V(α,β)` is finite dimensional over `ℂ`: its carrier is the type synonym `Fin (orderOf q) → ℂ`,
and the `ℂ`-structure is the standard one. -/
instance : FiniteDimensional ℂ (Fam q α β) :=
  inferInstanceAs (FiniteDimensional ℂ (Fin (orderOf q) → ℂ))

variable [NeZero (orderOf q)]

/-- **`V(α,β)` is a simple `qWeylAlgebra ℂ q`-module**, stated on the parameter-indexed carrier
`Fam q α β`. This is `famModule_isSimpleModule` transported along the definitional equality
`Fam q α β = (Fin (orderOf q) → ℂ)`, exactly as the `IsScalarTower` instance of
`Problem2_7_5_Iso.lean` is. -/
theorem fam_isSimpleModule : IsSimpleModule (qWeylAlgebra ℂ q) (Fam q α β) :=
  famModule_isSimpleModule q α β (orderOf q) rfl

omit [NeZero (orderOf q)] in
/-- **Problem 2.7.5(b), converse half.** If `q` is a root of unity, the `q`-Weyl algebra does have
a nonzero finite dimensional representation.

The witness is the constructed module `V(1,1) = Fam q 1 1` of part (c), so the conclusion records
more than bare existence: the representation is irreducible and has dimension exactly `orderOf q`,
which is the dimension forced on every finite dimensional irreducible by
`finrank_irreducible_eq_orderOf`. -/
theorem exists_nontrivial_finrep_of_isOfFinOrder (hq : IsOfFinOrder q) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module (qWeylAlgebra ℂ q) V)
      (_ : IsScalarTower ℂ (qWeylAlgebra ℂ q) V),
      Nontrivial V ∧ FiniteDimensional ℂ V ∧ IsSimpleModule (qWeylAlgebra ℂ q) V ∧
        Module.finrank ℂ V = orderOf q := by
  haveI : NeZero (orderOf q) := ⟨(orderOf_pos_iff.mpr hq).ne'⟩
  exact ⟨Fam q 1 1, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, fam_isSimpleModule q 1 1, fam_finrank q 1 1⟩

omit [NeZero (orderOf q)] in
/-- **Problem 2.7.5(b).** The `q`-Weyl algebra over `ℂ` has a nonzero finite dimensional
representation if and only if `q` is a root of unity.

Forward: the determinant obstruction `isOfFinOrder_of_nontrivial_finrep`. Backward: the
explicit witness `V(1,1)` of `exists_nontrivial_finrep_of_isOfFinOrder`. -/
theorem isOfFinOrder_iff_exists_nontrivial_finrep :
    IsOfFinOrder q ↔
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module (qWeylAlgebra ℂ q) V)
        (_ : IsScalarTower ℂ (qWeylAlgebra ℂ q) V), Nontrivial V ∧ FiniteDimensional ℂ V := by
  constructor
  · intro hq
    obtain ⟨V, iag, imc, imq, ist, hnt, hfd, -, -⟩ :=
      exists_nontrivial_finrep_of_isOfFinOrder q hq
    exact ⟨V, iag, imc, imq, ist, hnt, hfd⟩
  · rintro ⟨V, iag, imc, imq, ist, hnt, hfd⟩
    letI := iag; letI := imc; letI := imq; letI := ist
    haveI := hnt; haveI := hfd
    exact isOfFinOrder_of_nontrivial_finrep q V

end Converse

end Etingof.Problem2_7_5
