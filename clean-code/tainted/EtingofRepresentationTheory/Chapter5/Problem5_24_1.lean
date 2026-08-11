import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible

/-!
# Problem 5.24.1(a): the two orderings of the Young symmetrizer give isomorphic modules

**Problem 5.24.1.** (a) Show that the `S_n`-representation `V'_λ := ℂ[S_n] b_λ a_λ` is
isomorphic to `V_λ`.

*Hint.* Define `S_n`-homomorphisms `f : V_λ → V'_λ` and `g : V'_λ → V_λ` by `f(x) = x a_λ`
and `g(y) = y b_λ`, and show that they are inverse to each other up to a nonzero scalar.

## Formalization

The book's `V_λ = ℂ[S_n] a_λ b_λ` (Young symmetrizer `c_λ = a_λ b_λ`), while the project's
`SpechtModule n la = ℂ[S_n] · (b_λ a_λ)` uses the opposite ordering `c_λ = b_λ a_λ` (see
`Etingof.YoungSymmetrizer`). Part (a) is precisely the statement that these two left ideals,
the two orderings of the row (`a_λ`) and column (`b_λ`) symmetrizers, are isomorphic as
`S_n`-representations.

We write `rowColIdeal la := ℂ[S_n] · (a_λ b_λ)` (the book's `V_λ`) and compare it with
`SpechtModule n la = ℂ[S_n] · (b_λ a_λ)` (the book's `V'_λ`). `S_n` acts on each left ideal by
left multiplication, which is exactly the `ℂ[S_n]`-module scalar action `of(g) • ·`. The claim
is a `ℂ`-linear isomorphism intertwining these actions.

The proof follows the book's hint: `f(x) = x · a_λ` maps `V_λ → V'_λ` and `g(y) = y · b_λ`
maps `V'_λ → V_λ`; both are right multiplications, hence left-`ℂ[S_n]`-linear (so they
intertwine the `of(g) • ·` action). The composites `g ∘ f` and `f ∘ g` are right
multiplication by `a_λ b_λ` and `b_λ a_λ`; the Young-symmetrizer scalar identity
`c_λ² = α · c_λ` (Lemma 5.13.3, with the mirror identity from `Lemma5_13_1_dual`, both
scalars equal via `c_λ³ = α² c_λ`) makes each composite `α · id` with `α ≠ 0`, so `f` is
bijective.
-/

namespace Etingof

/-- The left ideal `ℂ[S_n] · (a_λ b_λ)`, i.e. the book's `V_λ` (row symmetrizer `a_λ` times
column antisymmetrizer `b_λ`). -/
noncomputable def rowColIdeal (n : ℕ) (la : Nat.Partition n) :
    Submodule (SymGroupAlgebra n) (SymGroupAlgebra n) :=
  Submodule.span (SymGroupAlgebra n)
    {RowSymmetrizer n la * ColumnAntisymmetrizer n la}

/-- Problem 5.24.1(a). The two orderings of the Young symmetrizer generate isomorphic
`S_n`-representations: `ℂ[S_n]·(a_λ b_λ)` (the book's `V_λ`) is isomorphic to
`ℂ[S_n]·(b_λ a_λ) = V'_λ` (the project's `SpechtModule`), via a `ℂ`-linear equivalence
intertwining the left-multiplication (`of(g) • ·`) `S_n`-actions. -/
theorem rowColIdeal_iso_spechtModule (n : ℕ) (la : Nat.Partition n) :
    ∃ e : ↥(rowColIdeal n la) ≃ₗ[ℂ] ↥(SpechtModule n la),
      ∀ (g : Equiv.Perm (Fin n)) (x : ↥(rowColIdeal n la)),
        e ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • x)
          = (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • e x := by
  classical
  -- Scalar identities from the Young-symmetrizer machinery.
  obtain ⟨α, hα⟩ := Etingof.Lemma5_13_3 n la
  obtain ⟨ℓ, hℓ⟩ := Etingof.Lemma5_13_1_dual n la
  have hsq := young_symmetrizer_sq_ne_zero n la
  -- Abbreviate the row symmetrizer `a`, the column antisymmetrizer `b`.
  set a := RowSymmetrizer n la with ha_def
  set b := ColumnAntisymmetrizer n la with hb_def
  have hY : YoungSymmetrizer n la = b * a := rfl
  rw [hY] at hα hsq
  -- `c = b * a` satisfies `c² = α c` with `α ≠ 0`; `hℓ x : a * x * b = ℓ x • (a * b)`.
  have hα_ne : α ≠ 0 := fun h => hsq (by rw [hα, h, zero_smul])
  have hbne : b * a ≠ 0 := fun h => hsq (by rw [h, mul_zero])
  -- The mirror identity: `d² = ℓ(b*a) • d` for `d = a * b`.
  have hd2 : (a * b) * (a * b) = ℓ (b * a) • (a * b) := by
    have h := hℓ (b * a)
    calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = ℓ (b * a) • (a * b) := h
  -- The two scalars agree: `ℓ(b*a) = α` (both come from `c³ = α² c`).
  have hβα : ℓ (b * a) = α := by
    have cube1 : b * ((a * b) * (a * b)) * a = (α * α) • (b * a) := by
      have e : b * ((a * b) * (a * b)) * a = ((b * a) * (b * a)) * (b * a) := by
        simp only [mul_assoc]
      rw [e, hα, smul_mul_assoc, hα, smul_smul]
    have cube2 : b * ((a * b) * (a * b)) * a = (ℓ (b * a) * α) • (b * a) := by
      rw [hd2, mul_smul_comm, smul_mul_assoc]
      have e2 : b * (a * b) * a = (b * a) * (b * a) := by simp only [mul_assoc]
      rw [e2, hα, smul_smul]
    have hαβ : (α * α) • (b * a) = (ℓ (b * a) * α) • (b * a) := by rw [← cube1, cube2]
    have hzero : (α * α - ℓ (b * a) * α) • (b * a) = (0 : SymGroupAlgebra n) := by
      rw [sub_smul, hαβ, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact (mul_right_cancel₀ hα_ne (sub_eq_zero.mp h)).symm
    · exact absurd h hbne
  rw [hβα] at hd2
  -- Describe the two left ideals as span of a single generator.
  have hRC : rowColIdeal n la = Submodule.span (SymGroupAlgebra n) {a * b} := by
    simp only [rowColIdeal, ← ha_def, ← hb_def]
  have hSM : SpechtModule n la = Submodule.span (SymGroupAlgebra n) {b * a} := by
    simp only [SpechtModule, hY]
  -- Right multiplication by `a` (resp. `b`), as a left-`ℂ[Sₙ]`-linear endomorphism.
  let Fa : SymGroupAlgebra n →ₗ[SymGroupAlgebra n] SymGroupAlgebra n :=
    { toFun := fun x => x * a
      map_add' := fun x y => add_mul x y a
      map_smul' := fun s x => by simp only [RingHom.id_apply, smul_eq_mul, mul_assoc] }
  let Gb : SymGroupAlgebra n →ₗ[SymGroupAlgebra n] SymGroupAlgebra n :=
    { toFun := fun x => x * b
      map_add' := fun x y => add_mul x y b
      map_smul' := fun s x => by simp only [RingHom.id_apply, smul_eq_mul, mul_assoc] }
  have hFa_maps : ∀ x ∈ rowColIdeal n la, Fa x ∈ SpechtModule n la := by
    intro x hx
    rw [hRC, Submodule.mem_span_singleton] at hx
    obtain ⟨r, hr⟩ := hx
    rw [hSM, Submodule.mem_span_singleton]
    refine ⟨r * a, ?_⟩
    change (r * a) • (b * a) = x * a
    rw [← hr]; simp only [smul_eq_mul, mul_assoc]
  have hGb_maps : ∀ y ∈ SpechtModule n la, Gb y ∈ rowColIdeal n la := by
    intro y hy
    rw [hSM, Submodule.mem_span_singleton] at hy
    obtain ⟨s, hs⟩ := hy
    rw [hRC, Submodule.mem_span_singleton]
    refine ⟨s * b, ?_⟩
    change (s * b) • (a * b) = y * b
    rw [← hs]; simp only [smul_eq_mul, mul_assoc]
  let F : ↥(rowColIdeal n la) →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la) := Fa.restrict hFa_maps
  let G : ↥(SpechtModule n la) →ₗ[SymGroupAlgebra n] ↥(rowColIdeal n la) := Gb.restrict hGb_maps
  -- The composites are `α • id`.
  have hGF : ∀ x : ↥(rowColIdeal n la), G (F x) = α • x := by
    intro x
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    change (x.val * a) * b = α • x.val
    have hx : (x : SymGroupAlgebra n) ∈ Submodule.span (SymGroupAlgebra n) {a * b} := by
      rw [← hRC]; exact x.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hr]; simp only [smul_eq_mul]
    rw [show (r * (a * b)) * a * b = r * ((a * b) * (a * b)) by simp only [mul_assoc],
      hd2, mul_smul_comm]
  have hFG : ∀ y : ↥(SpechtModule n la), F (G y) = α • y := by
    intro y
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    change (y.val * b) * a = α • y.val
    have hy : (y : SymGroupAlgebra n) ∈ Submodule.span (SymGroupAlgebra n) {b * a} := by
      rw [← hSM]; exact y.property
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hy
    rw [← hs]; simp only [smul_eq_mul]
    rw [show (s * (b * a)) * b * a = s * ((b * a) * (b * a)) by simp only [mul_assoc],
      hα, mul_smul_comm]
  -- `F` restricted to a `ℂ`-linear map is bijective, giving the `ℂ`-linear equivalence.
  let Fℂ : ↥(rowColIdeal n la) →ₗ[ℂ] ↥(SpechtModule n la) := F.restrictScalars ℂ
  have hinj : Function.Injective Fℂ := by
    intro x y hxy
    have h1 : G (F x) = G (F y) := by rw [show F x = F y from hxy]
    rw [hGF, hGF] at h1
    have h2 : α⁻¹ • (α • x) = α⁻¹ • (α • y) := by rw [h1]
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ hα_ne, one_smul, one_smul] at h2
  have hsurj : Function.Surjective Fℂ := by
    intro y
    refine ⟨α⁻¹ • G y, ?_⟩
    have h1 : Fℂ (α⁻¹ • G y) = α⁻¹ • (α • y) := by
      rw [map_smul, show Fℂ (G y) = α • y from hFG y]
    rw [h1, smul_smul, inv_mul_cancel₀ hα_ne, one_smul]
  refine ⟨LinearEquiv.ofBijective Fℂ ⟨hinj, hsurj⟩, ?_⟩
  intro g x
  exact F.map_smul (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) x

end Etingof
