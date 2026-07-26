import Mathlib

/-!
# Finite direct sums of finite-dimensional representations

`FDRep k G` has binary biproducts, but Mathlib does not (yet) provide the `⨁`-indexed ones, and
several book statements decompose a representation as a direct sum indexed by an arbitrary finite
set (all `p²` characters of the Heisenberg group, `p` copies of `R_{zw}`, …). This file builds
that direct sum concretely, as the componentwise action on the product `∀ i, V i` (for a finite
index set, product and direct sum agree), and computes its character.

Main definitions and results:

* `Etingof.Representation.pi` — the componentwise action of `G` on `∀ i, M i`;
* `Etingof.FDRep.pi` — the corresponding object of `FDRep k G`;
* `Etingof.FDRep.piπ` / `Etingof.FDRep.piι` — the structural projections and inclusions, with
  `piι i ≫ piπ i = 𝟙` and `piι i ≫ piπ j = 0` for `i ≠ j`, exhibiting `FDRep.pi V` as the direct
  sum of the family `V`;
* `Etingof.FDRep.character_pi` — additivity of the character:
  `(FDRep.pi V).character g = ∑ i, (V i).character g`.

Combined with `Etingof.charEq_iso` ("equal characters imply isomorphism", `Chapter5/CharEqIso`)
this turns a character computation into an actual isomorphism of representations onto a direct
sum.
-/

open CategoryTheory Module

namespace Etingof

section PiEnd

variable {k : Type} [Field k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

/-- The diagonal endomorphism of `∀ i, M i` assembled from a family of endomorphisms `f i`. -/
def piEnd (f : ∀ i, M i →ₗ[k] M i) : (∀ i, M i) →ₗ[k] (∀ i, M i) :=
  LinearMap.pi fun i => (f i) ∘ₗ LinearMap.proj i

@[simp] theorem piEnd_apply (f : ∀ i, M i →ₗ[k] M i) (x : ∀ i, M i) (i : ι) :
    piEnd f x i = f i (x i) := rfl

theorem piEnd_id : piEnd (fun i => (LinearMap.id : M i →ₗ[k] M i)) = LinearMap.id := rfl

theorem piEnd_comp (f g : ∀ i, M i →ₗ[k] M i) :
    piEnd (fun i => (f i) ∘ₗ (g i)) = (piEnd f) ∘ₗ (piEnd g) := rfl

/-- The diagonal endomorphism, written out as `∑ i, single i ∘ f i ∘ proj i`. -/
theorem piEnd_eq_sum (f : ∀ i, M i →ₗ[k] M i) :
    piEnd f = ∑ i, (LinearMap.single k M i) ∘ₗ ((f i) ∘ₗ LinearMap.proj i) := by
  ext x j
  simp [Finset.sum_apply]

theorem proj_comp_single (i : ι) :
    (LinearMap.proj i : (∀ j, M j) →ₗ[k] M i) ∘ₗ LinearMap.single k M i = LinearMap.id := by
  ext x
  simp

variable [∀ i, FiniteDimensional k (M i)]

/-- **Trace additivity for a finite product.** The trace of the diagonal endomorphism `piEnd f`
of `∀ i, M i` is the sum of the traces of its components. -/
theorem trace_piEnd (f : ∀ i, M i →ₗ[k] M i) :
    LinearMap.trace k (∀ i, M i) (piEnd f) = ∑ i, LinearMap.trace k (M i) (f i) := by
  rw [piEnd_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm' ((f i) ∘ₗ LinearMap.proj i) (LinearMap.single k M i),
    LinearMap.comp_assoc, proj_comp_single, LinearMap.comp_id]

end PiEnd

namespace Representation

variable {k : Type} [Field k] {G : Type} [Monoid G]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

/-- The componentwise action of `G` on `∀ i, M i`: the direct sum of a finite family of
representations. -/
def pi (ρ : ∀ i, _root_.Representation k G (M i)) : _root_.Representation k G (∀ i, M i) where
  toFun g := piEnd fun i => ρ i g
  map_one' := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp [Module.End.mul_eq_comp]

@[simp] theorem pi_apply (ρ : ∀ i, _root_.Representation k G (M i)) (g : G) (x : ∀ i, M i)
    (i : ι) : pi ρ g x i = ρ i g (x i) := rfl

end Representation

namespace FDRep

variable {k : Type} [Field k] {G : Type} [Monoid G]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Build a morphism of `FDRep`s from an equivariant linear map. -/
def mkHom (V W : FDRep k G) (f : (V : Type) →ₗ[k] (W : Type))
    (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v)) : V ⟶ W where
  hom := FGModuleCat.ofHom f
  comm := by intro g; ext v; exact hf g v

@[simp] theorem mkHom_apply (V W : FDRep k G) (f : (V : Type) →ₗ[k] (W : Type))
    (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v)) (v : (V : Type)) :
    (mkHom V W f hf).hom.hom.hom v = f v := rfl

/-- **The direct sum of a finite family of finite-dimensional representations**, realized on the
product space `∀ i, V i` with the componentwise action. -/
noncomputable def pi (V : ι → FDRep k G) : FDRep k G :=
  FDRep.of (Representation.pi fun i => (V i).ρ)

@[simp] theorem pi_ρ_apply (V : ι → FDRep k G) (g : G) (x : (pi V : Type)) (i : ι) :
    (pi V).ρ g x i = (V i).ρ g (x i) := rfl

/-- The `i`-th structural projection of the direct sum. -/
noncomputable def piπ (V : ι → FDRep k G) (i : ι) : pi V ⟶ V i :=
  mkHom _ _ (LinearMap.proj i) fun _ _ => rfl

/-- The `i`-th structural inclusion into the direct sum. -/
noncomputable def piι (V : ι → FDRep k G) (i : ι) : V i ⟶ pi V :=
  mkHom _ _ (LinearMap.single k (fun j => ((V j : Type))) i) fun g v => by
    refine funext fun j => ?_
    change (Pi.single (M := fun j => ((V j : Type))) i ((V i).ρ g v)) j
        = (V j).ρ g ((Pi.single (M := fun j => ((V j : Type))) i v) j)
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h), map_zero]

@[simp] theorem piπ_apply (V : ι → FDRep k G) (i : ι) (x : (pi V : Type)) :
    (piπ V i).hom.hom.hom x = x i := rfl

@[simp] theorem piι_apply (V : ι → FDRep k G) (i : ι) (v : (V i : Type)) :
    (piι V i).hom.hom.hom v = Pi.single i v := rfl

/-- `piι i ≫ piπ i = 𝟙`: the inclusion followed by its own projection is the identity. -/
theorem piι_piπ_self (V : ι → FDRep k G) (i : ι) : piι V i ≫ piπ V i = 𝟙 (V i) := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  ext v
  simp

/-- `piι i ≫ piπ j = 0` for `i ≠ j`: distinct summands are orthogonal. -/
theorem piι_piπ_of_ne (V : ι → FDRep k G) {i j : ι} (h : i ≠ j) :
    piι V i ≫ piπ V j = 0 := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  ext v
  exact Pi.single_eq_of_ne (M := fun j => ((V j : Type))) (Ne.symm h) v

/-- **Character additivity over a finite direct sum**: the character of `FDRep.pi V` is the sum
of the characters of the summands. -/
theorem character_pi (V : ι → FDRep k G) (g : G) :
    (pi V).character g = ∑ i, (V i).character g :=
  trace_piEnd _

end FDRep

end Etingof
