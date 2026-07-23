import EtingofRepresentationTheory.Chapter6.Theorem6_5_2

/-!
# Downstream import/`#check` test for Gabriel's theorem (Theorem 6.5.2)

This file imports `Chapter6/Theorem6_5_2.lean` and pins the public signatures of the
combined Gabriel theorem together with its three standalone component endpoints. Its purpose
is to catch a regression in the source even when cached oleans would otherwise hide it from
the aggregate build: because this file `import`s the source and re-elaborates the endpoint
statements, it forces a fresh check of their public API.

See issue #7518 (restore fresh-buildable Gabriel theorem 6.5.2).
-/

-- The three standalone component endpoints (a) finiteness, (b) indecomposable ⇒ positive
-- root, (c) positive-root bijection.
#check @Etingof.Theorem_6_5_2a_finiteness
#check @Etingof.Theorem_6_5_2b_dimvec_is_positive_root
#check @Etingof.Theorem_6_5_2c_bijection

-- The combined theorem asserting all three clauses at once.
#check @Etingof.Theorem_6_5_2_Gabriels_theorem

-- Signature lock: the combined theorem delivers finiteness of positive roots, the
-- positive-root dimension vector of every finite-dimensional indecomposable, and the
-- existence/uniqueness bijection with positive roots.
example {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (k : Type) [Field k]
    {Q : @Quiver.{0, 0} (Fin n)}
    (hQ : Etingof.IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)] :
    (Set.Finite {d : Fin n → ℤ | Etingof.IsPositiveRoot n adj d}) ∧
    (∀ (ρ : @Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n) _ Q)
      [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)],
      ρ.IsIndecomposable →
      Etingof.IsPositiveRoot n adj (fun v => (Module.finrank k (ρ.obj v) : ℤ))) ∧
    (∀ (α : Fin n → ℤ), Etingof.IsPositiveRoot n adj α →
      (∃ (ρ : @Etingof.QuiverRepresentation.{0, 0, 0, _} k (Fin n) _ Q)
        (_ : ∀ v, Module.Free k (ρ.obj v)) (_ : ∀ v, Module.Finite k (ρ.obj v)),
        ρ.IsIndecomposable ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v))) ∧
      (∀ (ρ₁ ρ₂ : @Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n) _ Q)
        [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
        [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)],
        ρ₁.IsIndecomposable → ρ₂.IsIndecomposable →
        (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₁.obj v))) →
        (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₂.obj v))) →
        Nonempty (Etingof.QuiverRepresentation.Iso ρ₁ ρ₂))) :=
  Etingof.Theorem_6_5_2_Gabriels_theorem hDynkin k hQ
