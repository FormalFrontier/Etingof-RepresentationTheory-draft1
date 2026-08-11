import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1

/-!
# Problem 5.8.4: transitivity of induction (induction in stages)

**Problem 5.8.4.** Check that if `K ⊂ H ⊂ G` are groups and if `V` is a representation of
`K`, then `Ind_H^G Ind_K^H V` is isomorphic to `Ind_K^G V`.

## Formalization

We take subgroups `K H : Subgroup G` with `K ≤ H`.  This unrestricted induction-in-stages
statement concerns the tensor/coinvariant left adjoint, exposed as `Etingof.inducedTensorModel`
(Mathlib's `Representation.ind`).  Under finite index it transports to the book's function-space
model through `Etingof.Definition5_8_1_iso_functionSpace`.

For the inner induction `Ind_K^H` we need `K` viewed as a subgroup of `H`, namely
`K.subgroupOf H`, and the representation `V` of `K` transported to `K.subgroupOf H` along the
canonical isomorphism `K.subgroupOf H ≃* K` (`Subgroup.subgroupOfEquivOfLe`). Write
`ρ' : Representation ℂ (K.subgroupOf H) V` for this transport.

The claim is a `G`-equivariant linear isomorphism between the carrier of
`Ind_H^G (Ind_K^H V)` and the carrier of `Ind_K^G V`.

The mathematical core is the abstract associativity `Ind_ψ (Ind_φ τ) ≅ Ind_{ψ∘φ} τ`
(`ind_stages_exists`): in Mathlib's tensor/coinvariants model of `Representation.ind` the forward
map sends `⟦a_G ⊗ ⟦a_H ⊗ v⟧⟧ ↦ ⟦ψ_*(a_H)·a_G ⊗ v⟧`. The subgroup statement `ind_ind_iso_ind`
reduces to this via the change-of-source-group relabelling `indStages_ker_eq`.
-/

open CategoryTheory

namespace Etingof

section Problem584

variable {G : Type*} [Group G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The representation `V` of `K`, transported to a representation of `K.subgroupOf H`
(the copy of `K` sitting inside `H`) along `Subgroup.subgroupOfEquivOfLe`. -/
noncomputable def indStagesInnerRep
    (H K : Subgroup G) (hKH : K ≤ H) (ρ : Representation ℂ K V) :
    Representation ℂ (K.subgroupOf H) V :=
  ρ.comp (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom

/-- **Change of source group along an isomorphism.** For an isomorphism `σ : S ≃* K` and a
map `f : K →* G`, inducing `ρ` along `f` and inducing the pulled-back representation `ρ ∘ σ`
along `f ∘ σ` give the *same* underlying module `(ℂ[G] ⊗ V)` and the same `G`-action; only the
subgroup by which one takes coinvariants is reindexed by the bijection `σ`. Hence the two
coinvariant kernels coincide as submodules. -/
theorem indStages_ker_eq {K S : Type*} [Group K] [Group S]
    (fφ : S →* G) (τ' : Representation ℂ S V) (f : K →* G) (σ : S →* K)
    (τ : Representation ℂ K V) (hfφ : fφ = f.comp σ) (hτ : τ' = τ.comp σ)
    (hσ : Function.Bijective σ) :
    Representation.Coinvariants.ker
        (Representation.tprod ((Representation.leftRegular ℂ G).comp fφ) τ') =
      Representation.Coinvariants.ker
        (Representation.tprod ((Representation.leftRegular ℂ G).comp f) τ) := by
  subst hfφ hτ
  have hpt : ∀ (s : S), (Representation.tprod
        ((Representation.leftRegular ℂ G).comp (f.comp σ)) (τ.comp σ)) s
      = (Representation.tprod ((Representation.leftRegular ℂ G).comp f) τ) (σ s) := fun s => rfl
  unfold Representation.Coinvariants.ker
  congr 1
  ext y
  constructor
  · rintro ⟨⟨s, m⟩, rfl⟩
    exact ⟨(σ s, m), by simp only [hpt]⟩
  · rintro ⟨⟨k, m⟩, rfl⟩
    obtain ⟨s, rfl⟩ := hσ.surjective k
    exact ⟨(s, m), by simp only [hpt]⟩

namespace IndStages

open Representation TensorProduct

variable {S H : Type*} [Group S] [Group H]
  (φ : S →* H) (ψ : H →* G) (τ : Representation ℂ S V)

/-- The target representation of the direct induction `Ind_{ψ∘φ} τ`. -/
private noncomputable abbrev ρT : Representation ℂ S (TensorProduct ℂ (MonoidAlgebra ℂ G) V) :=
  Representation.tprod ((Representation.leftRegular ℂ G).comp (ψ.comp φ)) τ

/-- Group-algebra multiplication, kept `Finsupp`-typed so it can sit in tensor factors.
Defined through `LinearMap.mul` to force the `MonoidAlgebra` convolution product (not the
pointwise `Finsupp` product available under `import Mathlib`). -/
private noncomputable def gmul {K : Type*} [Group K]
    (x y : MonoidAlgebra ℂ K) : MonoidAlgebra ℂ K :=
  LinearMap.mul ℂ (MonoidAlgebra ℂ K) x y

/-- The convolution product as a genuine `Finsupp`-typed bilinear map. Ascribing the honest
`MonoidAlgebra ℂ K` domains lets `map_add`/`map_smul` fire without crossing the
`MonoidAlgebra`/`Finsupp` transparency boundary. -/
private noncomputable def gmulBilin {K : Type*} [Group K] :
    (MonoidAlgebra ℂ K) →ₗ[ℂ] (MonoidAlgebra ℂ K) →ₗ[ℂ] (MonoidAlgebra ℂ K) :=
  LinearMap.mul ℂ (MonoidAlgebra ℂ K)

private theorem gmul_eq_bilin {K : Type*} [Group K] (x y : MonoidAlgebra ℂ K) :
    gmul x y = gmulBilin x y := rfl

private theorem gmul_single {K : Type*} [Group K] (a b : K) (r s : ℂ) :
    gmul (MonoidAlgebra.single a r) (MonoidAlgebra.single b s) =
      MonoidAlgebra.single (a * b) (r * s) := by
  simp only [gmul, LinearMap.mul_apply']
  exact MonoidAlgebra.single_mul_single a b r s

private theorem gmul_assoc {K : Type*} [Group K] (x y z : MonoidAlgebra ℂ K) :
    gmul (gmul x y) z = gmul x (gmul y z) := by
  simp only [gmul, LinearMap.mul_apply']; rw [mul_assoc]

private theorem gmul_one_left {K : Type*} [Group K] (x : MonoidAlgebra ℂ K) :
    gmul (MonoidAlgebra.single (1 : K) 1) x = x :=
  @one_mul (MonoidAlgebra ℂ K) _ x

private theorem gmul_add_left {K : Type*} [Group K] (x y z : MonoidAlgebra ℂ K) :
    gmul (x + y) z = gmul x z + gmul y z := by
  simp only [gmul_eq_bilin, map_add, LinearMap.add_apply]

private theorem gmul_add_right {K : Type*} [Group K] (x y z : MonoidAlgebra ℂ K) :
    gmul x (y + z) = gmul x y + gmul x z := by
  simp only [gmul_eq_bilin, map_add]

private theorem gmul_smul_left {K : Type*} [Group K] (c : ℂ) (x y : MonoidAlgebra ℂ K) :
    gmul (c • x) y = c • gmul x y := by
  simp only [gmul_eq_bilin, map_smul, LinearMap.smul_apply]

/-- Left multiplication by `x`, as a linear map (`Finsupp`-typed). -/
private noncomputable def gmulLeftMap {K : Type*} [Group K] (x : MonoidAlgebra ℂ K) :
    (MonoidAlgebra ℂ K) →ₗ[ℂ] (MonoidAlgebra ℂ K) :=
  LinearMap.mul ℂ (MonoidAlgebra ℂ K) x

private theorem gmulLeftMap_apply {K : Type*} [Group K] (x y : MonoidAlgebra ℂ K) :
    gmulLeftMap x y = gmul x y := rfl

/-- `ψ_* : ℂ[H] →ₗ ℂ[G]`, the pushforward of coefficients along `ψ` (`Finsupp`-typed). -/
private noncomputable def psiL : (MonoidAlgebra ℂ H) →ₗ[ℂ] (MonoidAlgebra ℂ G) :=
  MonoidAlgebra.mapDomainLinearMap ℂ ℂ ψ

private theorem psiL_eq_mapDomainAlgHom (a : MonoidAlgebra ℂ H) :
    psiL ψ a = MonoidAlgebra.mapDomainAlgHom ℂ ℂ ψ a := by
  rfl

/-- `ψ_*` sends `single h r` to `single (ψ h) r`. -/
private theorem psiStar_single (h : H) (r : ℂ) :
    psiL ψ (MonoidAlgebra.single h r) = MonoidAlgebra.single (ψ h) r := by
  rw [psiL, MonoidAlgebra.mapDomainLinearMap_single]

/-- `ψ_*` is multiplicative. -/
private theorem psiStar_gmul (x y : MonoidAlgebra ℂ H) :
    psiL ψ (gmul x y) = gmul (psiL ψ x) (psiL ψ y) := by
  rw [psiL_eq_mapDomainAlgHom, psiL_eq_mapDomainAlgHom, psiL_eq_mapDomainAlgHom]
  simp only [gmul, LinearMap.mul_apply']; rw [map_mul]

/-- `leftRegular` acts by left multiplication in the group algebra. -/
private theorem leftRegular_gmul {K : Type*} [Group K] (g : K) (b : MonoidAlgebra ℂ K) :
    Representation.leftRegular ℂ K g b = gmul (MonoidAlgebra.single g 1) b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp [gmul_eq_bilin]
  | add x y hx hy => rw [map_add, hx, hy, gmul_add_right]
  | single x r =>
    rw [Representation.ofMulAction_single, gmul_single, one_mul, smul_eq_mul]

/-- `lmapDomain (· * g)` is right multiplication by `single g 1`. -/
private theorem lmapDomain_gmul {K : Type*} [Group K] (g : K) (a : MonoidAlgebra ℂ K) :
    MonoidAlgebra.mapDomainLinearMap ℂ ℂ (· * g) a =
      gmul a (MonoidAlgebra.single g 1) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [gmul_eq_bilin]
  | add x y hx hy => rw [map_add, hx, hy, gmul_add_left]
  | single x r =>
    rw [MonoidAlgebra.mapDomainLinearMap_single, gmul_single, mul_one]

/-- `ind` on a coinvariants generator: right multiply the group-algebra factor. -/
private theorem ind_mk_tmul {K L : Type*} [Group K] [Group L] (χ : K →* L)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (υ : Representation ℂ K W)
    (l : L) (a : MonoidAlgebra ℂ L) (w : W) :
    Representation.ind χ υ l (Coinvariants.mk _ (a ⊗ₜ[ℂ] w))
      = Coinvariants.mk _ (gmul a (MonoidAlgebra.single l⁻¹ 1) ⊗ₜ[ℂ] w) := by
  rw [Representation.ind_apply, Coinvariants.map_mk]
  congr 1
  rw [Representation.IntertwiningMap.coe_mk, LinearMap.rTensor_tmul, lmapDomain_gmul]

/-- The elementary building block of the forward map: for `aH, v`, the linear map
`aG ↦ ⟦(ψ_*(aH) * aG) ⊗ v⟧`. -/
private noncomputable def elt (aH : MonoidAlgebra ℂ H) (v : V) :
    (MonoidAlgebra ℂ G) →ₗ[ℂ] Representation.IndV (ψ.comp φ) τ :=
  Coinvariants.mk _ ∘ₗ (TensorProduct.mk ℂ (MonoidAlgebra ℂ G) V).flip v ∘ₗ
    gmulLeftMap (psiL ψ aH)

private theorem elt_apply (aH : MonoidAlgebra ℂ H) (v : V) (aG : MonoidAlgebra ℂ G) :
    elt φ ψ τ aH v aG
      = Coinvariants.mk (ρT φ ψ τ)
          (gmul (psiL ψ aH) aG ⊗ₜ[ℂ] v) := by
  simp only [elt, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    gmulLeftMap_apply]

/-- The bilinear map `(aH, v) ↦ elt aH v`. -/
private noncomputable def Cbil : (MonoidAlgebra ℂ H) →ₗ[ℂ] V →ₗ[ℂ] ((MonoidAlgebra ℂ G) →ₗ[ℂ]
    Representation.IndV (ψ.comp φ) τ) :=
  LinearMap.mk₂ ℂ (fun aH v => elt φ ψ τ aH v)
    (fun aH aH' v => by
      refine LinearMap.ext fun aG => ?_
      simp only [elt_apply, LinearMap.add_apply, map_add, gmul_add_left,
        TensorProduct.add_tmul, map_add])
    (fun c aH v => by
      refine LinearMap.ext fun aG => ?_
      simp only [elt_apply, LinearMap.smul_apply, map_smul, gmul_smul_left]
      rw [← TensorProduct.smul_tmul', map_smul])
    (fun aH v v' => by
      refine LinearMap.ext fun aG => ?_
      simp only [elt_apply, LinearMap.add_apply, TensorProduct.tmul_add, map_add])
    (fun c aH v => by
      refine LinearMap.ext fun aG => ?_
      simp only [elt_apply, LinearMap.smul_apply, TensorProduct.tmul_smul, map_smul])

private theorem Cbil_apply (aH : MonoidAlgebra ℂ H) (v : V) :
    Cbil φ ψ τ aH v = elt φ ψ τ aH v := rfl

/-- The map `⟦aH ⊗ v⟧ ↦ (aG ↦ ⟦ψ_*(aH)·aG ⊗ v⟧)` before descending the outer
coinvariants. -/
private noncomputable def h0 :
    TensorProduct ℂ (MonoidAlgebra ℂ H) V →ₗ[ℂ]
      ((MonoidAlgebra ℂ G) →ₗ[ℂ] Representation.IndV (ψ.comp φ) τ) :=
  TensorProduct.lift (Cbil φ ψ τ)

private theorem h0_tmul (aH : MonoidAlgebra ℂ H) (v : V) :
    h0 φ ψ τ (aH ⊗ₜ[ℂ] v) = elt φ ψ τ aH v := by
  rw [h0, TensorProduct.lift.tmul, Cbil_apply]

/-- `S`-invariance of `h0` (descends the inner induction's coinvariants). -/
private theorem h0_invariant (s : S) :
    h0 φ ψ τ ∘ₗ (Representation.tprod ((Representation.leftRegular ℂ H).comp φ) τ) s
      = h0 φ ψ τ := by
  refine TensorProduct.ext' fun aH v => ?_
  refine LinearMap.ext fun aG => ?_
  simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    MonoidHom.coe_comp, Function.comp_apply, h0_tmul, elt_apply]
  rw [leftRegular_gmul, psiStar_gmul, psiStar_single, gmul_assoc]
  have hkey := Coinvariants.mk_self_apply (ρT φ ψ τ) s
    (gmul (psiL ψ aH) aG ⊗ₜ[ℂ] v)
  rw [ρT, Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.coe_comp,
    Function.comp_apply, leftRegular_gmul] at hkey
  exact hkey

/-- The forward map descended over the inner coinvariants, as a map into
`Hom(MonoidAlgebra ℂ G, ·)`. -/
private noncomputable def bflip :
    Representation.IndV φ τ →ₗ[ℂ] ((MonoidAlgebra ℂ G) →ₗ[ℂ] Representation.IndV (ψ.comp φ) τ) :=
  Coinvariants.lift _ (h0 φ ψ τ) (h0_invariant φ ψ τ)

private theorem bflip_mk (aH : MonoidAlgebra ℂ H) (v : V) :
    bflip φ ψ τ (Coinvariants.mk _ (aH ⊗ₜ[ℂ] v)) = elt φ ψ τ aH v := by
  rw [bflip, Coinvariants.lift_mk, h0_tmul]

/-- The forward map before descending the outer coinvariants. -/
private noncomputable def f0 :
    TensorProduct ℂ (MonoidAlgebra ℂ G) (Representation.IndV φ τ) →ₗ[ℂ]
      Representation.IndV (ψ.comp φ) τ :=
  TensorProduct.lift (bflip φ ψ τ).flip

private theorem f0_tmul (aG : MonoidAlgebra ℂ G) (w : Representation.IndV φ τ) :
    f0 φ ψ τ (aG ⊗ₜ[ℂ] w) = bflip φ ψ τ w aG := by
  rw [f0, TensorProduct.lift.tmul, LinearMap.flip_apply]

/-- `H`-invariance of `f0` (descends the outer induction's coinvariants). -/
private theorem f0_invariant (h : H) :
    f0 φ ψ τ ∘ₗ
        (Representation.tprod ((Representation.leftRegular ℂ G).comp ψ)
          (Representation.ind φ τ)) h
      = f0 φ ψ τ := by
  refine TensorProduct.ext' fun aG w => ?_
  refine Coinvariants.induction_on w fun t => ?_
  refine t.induction_on ?_ (fun aH v => ?_) (fun t₁ t₂ h₁ h₂ => ?_)
  · simp
  · simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      MonoidHom.coe_comp, Function.comp_apply, ind_mk_tmul, f0_tmul, bflip_mk, elt_apply,
      leftRegular_gmul, psiStar_gmul, psiStar_single]
    rw [gmul_assoc, ← gmul_assoc (MonoidAlgebra.single (ψ h⁻¹) 1) (MonoidAlgebra.single (ψ h) 1) aG,
      gmul_single, show ψ h⁻¹ * ψ h = (1 : G) from by rw [← map_mul, inv_mul_cancel, map_one],
      mul_one, gmul_one_left]
  · simp only [map_add, TensorProduct.tmul_add]; rw [h₁, h₂]

/-- The forward linear map `Ind_ψ (Ind_φ τ) →ₗ Ind_{ψ∘φ} τ`. -/
private noncomputable def fwd :
    Representation.IndV ψ (Representation.ind φ τ) →ₗ[ℂ]
      Representation.IndV (ψ.comp φ) τ :=
  Coinvariants.lift _ (f0 φ ψ τ) (f0_invariant φ ψ τ)

private theorem fwd_mk (aG : MonoidAlgebra ℂ G) (aH : MonoidAlgebra ℂ H) (v : V) :
    fwd φ ψ τ (Coinvariants.mk _ (aG ⊗ₜ[ℂ] Coinvariants.mk _ (aH ⊗ₜ[ℂ] v)))
      = Coinvariants.mk _ (gmul (psiL ψ aH) aG ⊗ₜ[ℂ] v) := by
  rw [fwd, Coinvariants.lift_mk, f0_tmul, bflip_mk, elt_apply]

/-- The inverse building block: `⟦aG ⊗ v⟧ ↦ ⟦aG ⊗ ⟦single 1 1 ⊗ v⟧⟧`. -/
private noncomputable def g1 :
    TensorProduct ℂ (MonoidAlgebra ℂ G) V →ₗ[ℂ]
      Representation.IndV ψ (Representation.ind φ τ) :=
  Coinvariants.mk _ ∘ₗ TensorProduct.map LinearMap.id (Representation.IndV.mk φ τ 1)

private theorem g1_tmul (aG : MonoidAlgebra ℂ G) (v : V) :
    g1 φ ψ τ (aG ⊗ₜ[ℂ] v)
      = Coinvariants.mk _ (aG ⊗ₜ[ℂ]
          Coinvariants.mk _ (MonoidAlgebra.single (1 : H) (1 : ℂ) ⊗ₜ[ℂ] v)) := by
  rw [g1, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

/-- `S`-invariance of `g1` (descends the target coinvariants). -/
private theorem g1_invariant (s : S) :
    g1 φ ψ τ ∘ₗ (ρT φ ψ τ) s = g1 φ ψ τ := by
  refine TensorProduct.ext' fun aG v => ?_
  simp only [LinearMap.comp_apply, ρT, Representation.tprod_apply, TensorProduct.map_tmul,
    MonoidHom.coe_comp, Function.comp_apply, g1_tmul, leftRegular_gmul]
  -- inner S-relation: ⟦single 1 1 ⊗ τ s v⟧ = ⟦single (φ s)⁻¹ 1 ⊗ v⟧
  have hinner : Coinvariants.mk (Representation.tprod ((Representation.leftRegular ℂ H).comp φ) τ)
        (MonoidAlgebra.single (1 : H) (1 : ℂ) ⊗ₜ[ℂ] τ s v)
      = Coinvariants.mk _ (MonoidAlgebra.single (φ s)⁻¹ (1 : ℂ) ⊗ₜ[ℂ] v) := by
    have hh := Coinvariants.mk_self_apply
      (Representation.tprod ((Representation.leftRegular ℂ H).comp φ) τ) s
      (MonoidAlgebra.single (φ s)⁻¹ (1 : ℂ) ⊗ₜ[ℂ] v)
    rw [Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.coe_comp,
      Function.comp_apply, leftRegular_gmul, gmul_single, mul_inv_cancel, mul_one] at hh
    exact hh
  -- outer H-relation at h = φ s
  have houter := Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular ℂ G).comp ψ) (Representation.ind φ τ))
    (φ s)
    (aG ⊗ₜ[ℂ] Coinvariants.mk _ (MonoidAlgebra.single (1 : H) (1 : ℂ) ⊗ₜ[ℂ] v))
  rw [Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.coe_comp,
    Function.comp_apply, leftRegular_gmul, ind_mk_tmul, gmul_one_left] at houter
  rw [hinner]
  exact houter

/-- The inverse linear map `Ind_{ψ∘φ} τ →ₗ Ind_ψ (Ind_φ τ)`. -/
private noncomputable def inv :
    Representation.IndV (ψ.comp φ) τ →ₗ[ℂ]
      Representation.IndV ψ (Representation.ind φ τ) :=
  Coinvariants.lift _ (g1 φ ψ τ) (g1_invariant φ ψ τ)

private theorem inv_mk (aG : MonoidAlgebra ℂ G) (v : V) :
    inv φ ψ τ (Coinvariants.mk _ (aG ⊗ₜ[ℂ] v))
      = Coinvariants.mk _ (aG ⊗ₜ[ℂ]
          Coinvariants.mk _ (MonoidAlgebra.single (1 : H) (1 : ℂ) ⊗ₜ[ℂ] v)) := by
  rw [inv, Coinvariants.lift_mk, g1_tmul]

/-- `fwd ∘ inv = id`. -/
private theorem fwd_comp_inv : (fwd φ ψ τ).comp (inv φ ψ τ) = LinearMap.id := by
  refine Representation.IndV.hom_ext (ψ.comp φ) τ fun g => ?_
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply, Representation.IndV.mk,
    TensorProduct.mk_apply]
  rw [inv_mk, fwd_mk, psiStar_single, map_one, gmul_one_left]

/-- `inv ∘ fwd = id`. -/
private theorem inv_comp_fwd : (inv φ ψ τ).comp (fwd φ ψ τ) = LinearMap.id := by
  refine Representation.IndV.hom_ext ψ (Representation.ind φ τ) fun g => ?_
  refine Representation.IndV.hom_ext φ τ fun h => ?_
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply, Representation.IndV.mk,
    TensorProduct.mk_apply]
  rw [fwd_mk, inv_mk, psiStar_single, gmul_single, one_mul]
  have hkey := Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular ℂ G).comp ψ) (Representation.ind φ τ)) h
    (MonoidAlgebra.single g 1 ⊗ₜ[ℂ] Coinvariants.mk _ (MonoidAlgebra.single h 1 ⊗ₜ[ℂ] v))
  rw [Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.coe_comp,
    Function.comp_apply, leftRegular_gmul, gmul_single, ind_mk_tmul, gmul_single,
    mul_inv_cancel] at hkey
  simp only [mul_one] at hkey
  exact hkey

/-- `fwd` intertwines the `G`-actions of the two inductions. -/
private theorem fwd_equivariant (g : G) :
    (fwd φ ψ τ).comp (Representation.ind ψ (Representation.ind φ τ) g)
      = (Representation.ind (ψ.comp φ) τ g).comp (fwd φ ψ τ) := by
  refine Representation.IndV.hom_ext ψ (Representation.ind φ τ) fun g' => ?_
  refine Representation.IndV.hom_ext φ τ fun h => ?_
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, Representation.IndV.mk, TensorProduct.mk_apply]
  rw [ind_mk_tmul, fwd_mk, fwd_mk, ind_mk_tmul, gmul_assoc]

end IndStages

/-- **Induction in stages, abstract form.** For group homomorphisms `φ : S →* H` and `ψ : H →* G`
and a representation `τ` of `S`, the two-step induction `Ind_ψ (Ind_φ τ)` is `G`-equivariantly
isomorphic to the direct induction `Ind_{ψ∘φ} τ`. In the tensor/coinvariants model of `ind` this is
the associativity identity `⟦g ⊗ ⟦h ⊗ v⟧⟧ ↦ ⟦g · ψ(h) ⊗ v⟧`. -/
theorem ind_stages_exists {S H : Type*} [Group S] [Group H]
    (φ : S →* H) (ψ : H →* G) (τ : Representation ℂ S V) :
    ∃ e : Representation.IndV ψ (Representation.ind φ τ)
            ≃ₗ[ℂ] Representation.IndV (ψ.comp φ) τ,
      ∀ (g : G) x,
        e (Representation.ind ψ (Representation.ind φ τ) g x)
          = Representation.ind (ψ.comp φ) τ g (e x) := by
  refine ⟨LinearEquiv.ofLinear (IndStages.fwd φ ψ τ) (IndStages.inv φ ψ τ)
    (IndStages.fwd_comp_inv φ ψ τ) (IndStages.inv_comp_fwd φ ψ τ), ?_⟩
  intro g x
  simp only [LinearEquiv.ofLinear_apply]
  exact LinearMap.congr_fun (IndStages.fwd_equivariant φ ψ τ g) x

/-- Problem 5.8.4. For `K ≤ H ≤ G` and a representation `ρ` of `K`, the two-step induction
`Ind_H^G (Ind_K^H V)` is `G`-equivariantly isomorphic to the direct induction `Ind_K^G V`. -/
theorem ind_ind_iso_ind
    (H K : Subgroup G) (hKH : K ≤ H) (ρ : Representation ℂ K V) :
    ∃ e : Representation.IndV H.subtype
            (Etingof.inducedTensorModel (K.subgroupOf H) (indStagesInnerRep H K hKH ρ))
          ≃ₗ[ℂ] Representation.IndV K.subtype ρ,
      ∀ (g : G) x,
        e (Etingof.inducedTensorModel H
              (Etingof.inducedTensorModel (K.subgroupOf H)
                (indStagesInnerRep H K hKH ρ)) g x)
          = Etingof.inducedTensorModel K ρ g (e x) := by
  classical
  have hσbij : Function.Bijective (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom :=
    (Subgroup.subgroupOfEquivOfLe hKH).bijective
  -- STAGES: `Ind_H^G (Ind_{K.subgroupOf H} ρ') ≅ Ind_{ψ∘φ} ρ'` (abstract induction in stages).
  obtain ⟨e1, he1⟩ := ind_stages_exists (K.subgroupOf H).subtype H.subtype
    (indStagesInnerRep H K hKH ρ)
  -- RELABEL: `Ind_{ψ∘φ} (ρ∘σ) ≅ Ind_K^G ρ`, the two quotients share the module `ℂ[G]⊗V`, the same
  -- `G`-action, and (by `indStages_ker_eq`) equal coinvariant kernels.
  have hker := indStages_ker_eq (V := V)
    (H.subtype.comp (K.subgroupOf H).subtype) (indStagesInnerRep H K hKH ρ)
    K.subtype (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom ρ rfl rfl hσbij
  let relabelLE : Representation.IndV (H.subtype.comp (K.subgroupOf H).subtype)
        (indStagesInnerRep H K hKH ρ) ≃ₗ[ℂ] Representation.IndV K.subtype ρ :=
    Submodule.quotEquivOfEq _ _ hker
  -- the relabelling intertwines the two `ind` actions (both descend the same base map on `ℂ[G]⊗V`)
  have stepB : ∀ (g : G) (y : Representation.IndV (H.subtype.comp (K.subgroupOf H).subtype)
        (indStagesInnerRep H K hKH ρ)),
      relabelLE (Representation.ind (H.subtype.comp (K.subgroupOf H).subtype)
          (indStagesInnerRep H K hKH ρ) g y)
        = Representation.ind K.subtype ρ g (relabelLE y) := by
    have hrel : ∀ w : TensorProduct ℂ (MonoidAlgebra ℂ G) V,
        relabelLE (Representation.Coinvariants.mk _ w)
          = Representation.Coinvariants.mk _ w := by
      intro w
      exact Submodule.quotEquivOfEq_mk _ _ hker w
    intro g y
    refine Representation.Coinvariants.induction_on y (fun m => ?_)
    rw [Representation.ind_apply, Representation.ind_apply,
      Representation.Coinvariants.map_mk, hrel, hrel,
      Representation.Coinvariants.map_mk]
    rfl
  refine ⟨e1.trans relabelLE, ?_⟩
  intro g x
  -- Unfold the `inducedTensorModel` wrappers to `Representation.ind` (definitionally
  -- equal) so that `he1` and `stepB` apply syntactically; unfolding via `simp` leaves an ill-typed
  -- instance argument, so restate the goal with `change` instead.
  change relabelLE (e1 (Representation.ind H.subtype
        (Representation.ind (K.subgroupOf H).subtype (indStagesInnerRep H K hKH ρ)) g x))
      = Representation.ind K.subtype ρ g (relabelLE (e1 x))
  rw [he1, stepB]

end Problem584

end Etingof
