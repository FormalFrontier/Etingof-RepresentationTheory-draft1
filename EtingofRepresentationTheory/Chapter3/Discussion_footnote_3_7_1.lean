import EtingofRepresentationTheory.Chapter3.Theorem3_6_2

/-!
# Footnote 5 to Theorem 3.7.1: the character of `pV` vanishes in characteristic `p`

The character proof of the Jordan-Hölder theorem (Theorem 3.7.1, first proof) works only in
characteristic zero. Etingof's footnote explains why:

> This proof does not work in characteristic `p` because it only implies that the
> multiplicities of `Wᵢ` and `W'ᵢ` are the same modulo `p`, which is not sufficient. In fact,
> the character of the representation `pV`, where `V` is any representation, is zero.

We formalize the concrete assertion of the footnote: for any finite-dimensional representation
`V` of `A` (a `k`-algebra with `IsScalarTower k A V`), the character of the `p`-fold direct sum
`pV` is `p` times the character of `V`, and hence vanishes when `k` has characteristic `p`.

We model the `p`-fold direct sum `pV` as the diagonal representation on `Fin p → V`: the
`A`-action is the pointwise (`Pi`) action `a • g = fun i => a • g i`. Over the field `k` this is
a finite free `k`-module, so its character `Etingof.character` (see `Theorem3_6_2`) is defined.

The key computation is that the trace of the coordinatewise endomorphism of `ι → V` induced by
`f : V →ₗ[k] V` is `card ι` times the trace of `f`. We prove this by induction on `n` for
`ι = Fin n`, splitting `Fin (n+1) → V ≃ₗ V × (Fin n → V)` via `Fin.consLinearEquiv` and using
additivity of the trace along a product (`LinearMap.trace_prodMap'`). Specialising `f` to the
action `a • ·` gives the character identity `χ_{pV} = p • χ_V`, and `CharP.cast_eq_zero` finishes.
-/

open Module

namespace Etingof

section Diagonal

variable (k : Type*) (V : Type*)
  [CommRing k] [AddCommGroup V] [Module k V]

/-- The coordinatewise ("diagonal") endomorphism of `ι → V` induced by `f : V →ₗ[k] V`:
it sends `g` to `fun i => f (g i)`. For the action endomorphism `f = a • ·` this is exactly the
`A`-action on the direct sum `ι → V`. -/
def diagPi {ι : Type*} (f : V →ₗ[k] V) : (ι → V) →ₗ[k] (ι → V) :=
  LinearMap.pi fun i => f ∘ₗ LinearMap.proj i

/-- Applying the diagonal endomorphism acts by `f` in every coordinate. -/
@[simp]
lemma diagPi_apply {ι : Type*} (f : V →ₗ[k] V) (g : ι → V) (i : ι) :
    diagPi k V f g i = f (g i) := rfl

variable [Module.Free k V] [Module.Finite k V]

/-- The trace of the diagonal endomorphism of `Fin n → V` induced by `f` is `n` times the trace
of `f`. This is the direct-sum additivity of the trace applied to `n` identical summands. -/
lemma trace_diagPi_fin (n : ℕ) (f : V →ₗ[k] V) :
    LinearMap.trace k (Fin n → V) (diagPi k V f) = n • LinearMap.trace k V f := by
  induction n with
  | zero =>
    rw [zero_smul, Subsingleton.elim (diagPi k V f) 0, map_zero]
  | succ n ih =>
    -- Split `Fin (n+1) → V` as `V × (Fin n → V)`; under this splitting the diagonal
    -- endomorphism becomes `prodMap f (diagPi f)`.
    set e := (Fin.consLinearEquiv k (fun _ : Fin (n + 1) => V)).symm with he
    have key : e.conj (diagPi k V f) = LinearMap.prodMap f (diagPi k V f) := by
      apply LinearMap.ext
      rintro ⟨v, w⟩
      rw [LinearEquiv.conj_apply, LinearMap.prodMap_apply]
      apply Prod.ext
      · simp [he, diagPi]
      · funext i
        simp [he, diagPi, Fin.tail]
    calc LinearMap.trace k (Fin (n + 1) → V) (diagPi k V f)
        = LinearMap.trace k (V × (Fin n → V)) (e.conj (diagPi k V f)) :=
          (LinearMap.trace_conj' _ _).symm
      _ = LinearMap.trace k (V × (Fin n → V)) (LinearMap.prodMap f (diagPi k V f)) := by rw [key]
      _ = LinearMap.trace k V f + LinearMap.trace k (Fin n → V) (diagPi k V f) :=
          LinearMap.trace_prodMap' f (diagPi k V f)
      _ = LinearMap.trace k V f + n • LinearMap.trace k V f := by rw [ih]
      _ = (n + 1) • LinearMap.trace k V f := by rw [succ_nsmul, add_comm]

end Diagonal

section Footnote

variable (k : Type*) (A : Type*) (V : Type*)
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [Module.Free k V] [Module.Finite k V]

/-- **Character of the `p`-fold direct sum, general form.** For any finite-dimensional
representation `V` and any `n`, the character of the diagonal representation on `Fin n → V`
(the `n`-fold direct sum `nV`) is `n` times the character of `V`. -/
theorem character_fin_pi (n : ℕ) (a : A) :
    Etingof.character k A (Fin n → V) a = n • Etingof.character k A V a := by
  -- The action endomorphism of `Fin n → V` is the diagonal endomorphism induced by the
  -- action endomorphism of `V`.
  have h1 : (Algebra.lsmul k k (Fin n → V) : A →ₐ[k] Module.End k (Fin n → V)) a
      = diagPi k V ((Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a) := by
    apply LinearMap.ext
    intro g
    funext i
    rfl
  simp only [Etingof.character, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h1]
  exact trace_diagPi_fin k V n _

/-- **Footnote 5 to Theorem 3.7.1.** In characteristic `p`, the character of the `p`-fold direct
sum `pV` of any finite-dimensional representation `V` is zero. This is the concrete degeneracy
that makes the characteristic-zero character argument for Jordan-Hölder fail: multiplicities are
only determined modulo `p`. -/
theorem character_pcopies_eq_zero (p : ℕ) [CharP k p] :
    Etingof.character k A (Fin p → V) = 0 := by
  ext a
  rw [character_fin_pi k A V p a, LinearMap.zero_apply, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

end Footnote

end Etingof
