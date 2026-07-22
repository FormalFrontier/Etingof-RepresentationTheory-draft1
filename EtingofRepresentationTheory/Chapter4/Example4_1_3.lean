import Mathlib

/-!
# Example 4.1.3: Representations of ℤ/pℤ in Characteristic p

If G = ℤ/pℤ and k has characteristic p, then every irreducible representation of G
over k is trivial (the generator acts as the identity).

The book's argument runs through the generator acting by a p-th root of unity, and over a
field of characteristic p one has `xᵖ - 1 = (x - 1)ᵖ`, so the only p-th root of unity is 1.
We formalize an equivalent route that takes representation-irreducibility as the genuine
hypothesis: writing `g` for the generator, `ρ g - 1` is nilpotent (since `(ρ g - 1)ᵖ = 0` by
the same freshman's-dream identity) and, because `ℤ/pℤ` is abelian, it is a self-intertwiner
of `ρ`. Schur's lemma then forces `ρ g - 1` to be injective or zero; nilpotency on a nonzero
space rules out injectivity, so `ρ g = id`.

This shows that the hypothesis in Maschke's theorem (char k ∤ |G|) is essential.

## Mathlib correspondence

Uses `ZMod p` for the cyclic group and `CharP k p` for characteristic p. Irreducibility is
`IsSimpleModule (MonoidAlgebra k (Multiplicative (ZMod p))) ρ.asModule`, i.e. Mathlib's
`Representation.IsIrreducible ρ`; Schur's lemma is
`Representation.IsIrreducible.injective_or_eq_zero`.
-/

open scoped MonoidAlgebra in
/-- In characteristic p, every irreducible representation of ℤ/pℤ is trivial.

The hypothesis `hirr` is genuine representation-irreducibility: `ρ.asModule` is simple as a
module over the group algebra `k[ℤ/pℤ]`, i.e. the representation has no proper nonzero
`ρ`-invariant subspace (Mathlib's `Representation.IsIrreducible`). This is the book's notion,
*not* `IsSimpleModule k V` (which would force `V` to be one-dimensional and assume away the
content). The conclusion `ρ g = id` says the representation is trivial.
(Etingof Example 4.1.3) -/
theorem Etingof.Example4_1_3
    (k : Type*) (p : ℕ) [Field k] [hp : Fact (Nat.Prime p)] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (Multiplicative (ZMod p)) V)
    (hirr : IsSimpleModule (MonoidAlgebra k (Multiplicative (ZMod p))) ρ.asModule) :
    -- Every irreducible rep is trivial: ρ(g) = id for all g
    ∀ g : Multiplicative (ZMod p), ρ g = LinearMap.id := by
  -- Repackage `hirr` as Mathlib's irreducibility predicate so Schur's lemma applies.
  haveI hirr' : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hirr
  haveI : Nontrivial ρ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra k (Multiplicative (ZMod p))) ρ.asModule
  haveI : Nontrivial V := (ρ.asModuleEquiv).toEquiv.symm.nontrivial
  intro g
  -- Step 1: g^p = 1 since |Multiplicative (ZMod p)| = p
  have hgp : g ^ p = 1 := by
    have h := pow_card_eq_one (x := g)
    rwa [Fintype.card_multiplicative, ZMod.card] at h
  -- Step 2: ρ(g)^p = id
  have hρp : (ρ g) ^ p = 1 := by
    rw [← map_pow, hgp, map_one]
  -- Step 3: (ρ(g) - 1)^p = 0 by freshman's dream in char p
  have hnil : (ρ g - 1) ^ p = 0 := by
    haveI : CharP (Module.End k V) p :=
      charP_of_injective_algebraMap' k p
    rw [sub_pow_char_of_commute p (Commute.one_right _)]
    rw [one_pow, hρp, sub_self]
  -- Step 4: `ρ g - 1` intertwines `ρ` with itself, because `ℤ/pℤ` is abelian, so `ρ h`
  -- commutes with `ρ g`.
  have key : ∀ (h : Multiplicative (ZMod p)) (v : V), ρ g (ρ h v) = ρ h (ρ g v) := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  let f : Representation.IntertwiningMap ρ ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (ρ g - 1) (by
      intro h v
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, key h v])
  -- Step 5: by Schur, the intertwiner `f = ρ g - 1` is injective or zero. It cannot be
  -- injective: it is nilpotent (`fᵖ = 0`) and `V` is nontrivial. Hence `f = 0`, i.e. `ρ g = id`.
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hinj | hf0
  · exfalso
    have hinj' : Function.Injective (⇑(ρ g - 1)) := hinj
    have hinj_iter : Function.Injective (⇑(ρ g - 1))^[p] := hinj'.iterate p
    rw [← Module.End.coe_pow, hnil] at hinj_iter
    obtain ⟨a, b, hab⟩ := exists_pair_ne V
    exact hab (hinj_iter (by simp))
  · have hzero : ρ g - 1 = 0 := by
      ext v
      have hv := DFunLike.congr_fun hf0 v
      simpa [f] using hv
    rwa [sub_eq_zero] at hzero

