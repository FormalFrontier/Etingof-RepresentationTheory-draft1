import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Problem 3.3.3: An alternative proof of Theorem 3.3.1

The problem gives an alternative route to Theorem 3.3.1 through the structure of a direct
sum of algebras.

Let `A = A₁ ⊕ ⋯ ⊕ Aₙ` (modeled as the finite product algebra `∀ i, 𝒜 i`), with unit
idempotents `1ᵢ = Pi.single i 1`.

* **(a)** A representation `V` of `A` is irreducible iff `1ᵢ V` is an irreducible
  representation of `Aᵢ` for exactly one `i`, while `1ⱼ V = 0` for all other `j`. Here
  `1ᵢ V` is the `A`-submodule `LinearMap.range (idemProj i)`, the image of the (central,
  hence `A`-linear) projection `v ↦ 1ᵢ • v`. Since the factors `Aⱼ` with `j ≠ i` act as
  `0` on `1ᵢ V`, the `A`-submodules of `1ᵢ V` are exactly its `Aᵢ`-submodules, so
  "irreducible representation of `Aᵢ`" is faithfully rendered as
  `IsSimpleModule A (1ᵢ V)`.

* **(b)** The only irreducible representation of `Matₙ(k) = Mat_d(k)` is `k^d`, and every
  finite dimensional representation of `Mat_d(k)` is a direct sum of copies of `k^d`
  (i.e. isomorphic to `(k^d)^n = Fin n → (Fin d → k)` for some `n`).

* **(c)** Theorem 3.3.1 follows; the full statement is already recorded as
  `Etingof.irreducible_reps_of_matrix_algebra` in `Theorem3_3_1`.

Parts (a) and (b) are proved in full. Part (b) follows the book's elementary matrix-unit
argument rather than the Wedderburn–Artin route taken in `Theorem3_3_1`.
-/

namespace Etingof.Problem3_3_3

/-! ## Part (a): irreducibles of a direct sum of algebras

Part (a) is pure ring/module theory: it needs no base field, only the product ring
`A = ∀ i, 𝒜 i` and an `A`-module `V`. -/

section PartA

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]
  (V : Type*) [AddCommGroup V] [Module (∀ i, 𝒜 i) V]

/-- The unit idempotent `1ᵢ = Pi.single i 1` of the product algebra is central. -/
theorem single_one_central (i : Fin r) (a : ∀ i, 𝒜 i) :
    (Pi.single i 1 : ∀ i, 𝒜 i) * a = a * Pi.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- The `A`-linear projection `v ↦ 1ᵢ • v`. It is `A`-linear because `1ᵢ` is central. Its
range is the subrepresentation `1ᵢ V`. -/
def idemProj (i : Fin r) : V →ₗ[∀ i, 𝒜 i] V where
  toFun v := (Pi.single i 1 : ∀ i, 𝒜 i) • v
  map_add' v w := smul_add _ _ _
  map_smul' a v := by
    simp only [RingHom.id_apply, smul_smul]
    rw [single_one_central 𝒜 i a]

/-- The unit idempotents are orthogonal: `1ᵢ · 1ⱼ = δᵢⱼ 1ᵢ`. -/
theorem single_mul_single_eq (i j : Fin r) :
    (Pi.single i 1 : ∀ i, 𝒜 i) * Pi.single j 1 = if i = j then Pi.single i 1 else 0 := by
  by_cases h : i = j
  · rw [if_pos h]; subst h; ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  · rw [if_neg h]; ext k
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hk : k = i
    · subst hk; simp [Ne.symm h]
    · simp [hk]

/-- The unit idempotents sum to `1`. -/
theorem sum_single_one : (∑ i, (Pi.single i 1 : ∀ i, 𝒜 i)) = 1 := by
  simpa using Finset.univ_sum_single (1 : ∀ i, 𝒜 i)

/-- Applying two idempotent projections in succession: `1ᵢ · (1ⱼ · v) = δᵢⱼ (1ᵢ · v)`. -/
theorem single_smul_single_smul (i j : Fin r) (v : V) :
    (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single j 1 : ∀ i, 𝒜 i) • v)
      = if i = j then (Pi.single i 1 : ∀ i, 𝒜 i) • v else 0 := by
  rw [← mul_smul, single_mul_single_eq]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_smul]

/-- The projections `1ᵢ · (-)` sum to the identity: `∑ᵢ 1ᵢ · v = v`. -/
theorem sum_single_smul (v : V) : (∑ i, (Pi.single i 1 : ∀ i, 𝒜 i) • v) = v := by
  rw [← Finset.sum_smul, sum_single_one, one_smul]

/-- Membership in the range of `1ᵢ · (-)` is exactly idempotence: `v ∈ 1ᵢ V ↔ 1ᵢ · v = v`. -/
theorem mem_range_idemProj (i : Fin r) (v : V) :
    v ∈ LinearMap.range (idemProj 𝒜 V i) ↔ (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single i 1 : ∀ i, 𝒜 i) • w)
        = (Pi.single i 1 : ∀ i, 𝒜 i) • w
    rw [single_smul_single_smul, if_pos rfl]
  · intro h
    exact ⟨v, h⟩

/-- The summand `1ᵢ V` is everything iff `1ᵢ` acts as the identity. -/
theorem range_eq_top_iff (i : Fin r) :
    LinearMap.range (idemProj 𝒜 V i) = ⊤ ↔ ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
  rw [Submodule.eq_top_iff']
  exact ⟨fun h v => (mem_range_idemProj 𝒜 V i v).1 (h v),
         fun h v => (mem_range_idemProj 𝒜 V i v).2 (h v)⟩

/-- The summand `1ᵢ V` vanishes iff `1ᵢ` acts as zero. -/
theorem range_eq_bot_iff (i : Fin r) :
    LinearMap.range (idemProj 𝒜 V i) = ⊥ ↔ ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = 0 := by
  rw [LinearMap.range_eq_bot, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply]
  rfl

/-- **Problem 3.3.3(a).** A representation `V` of `A = ⊕ᵢ Aᵢ` is irreducible if and only if
`1ᵢ V` is an irreducible representation of `Aᵢ` for exactly one `i`, while `1ⱼ V = 0` for
all other `j`. -/
theorem simpleModule_prod_iff :
    IsSimpleModule (∀ i, 𝒜 i) V ↔
      ∃ i, IsSimpleModule (∀ i, 𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) ∧
        ∀ j, j ≠ i → LinearMap.range (idemProj 𝒜 V j) = ⊥ := by
  constructor
  · -- (⇒) `V` simple. Each summand `1ₖ V` is `⊥` or `⊤`; not all are `⊥` (they sum to `V`),
    -- and at most one is `⊤` (orthogonality). The unique `⊤` summand is the required `i`.
    intro hV
    haveI := hV
    haveI : Nontrivial V := IsSimpleModule.nontrivial (∀ i, 𝒜 i) V
    have hclass : ∀ k, LinearMap.range (idemProj 𝒜 V k) = ⊥ ∨
        LinearMap.range (idemProj 𝒜 V k) = ⊤ := fun k => eq_bot_or_eq_top _
    have hexists : ∃ i, LinearMap.range (idemProj 𝒜 V i) = ⊤ := by
      by_contra h
      simp only [not_exists] at h
      have hbot : ∀ k, LinearMap.range (idemProj 𝒜 V k) = ⊥ :=
        fun k => (hclass k).resolve_right (h k)
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine hv ?_
      rw [← sum_single_smul 𝒜 V v]
      exact Finset.sum_eq_zero fun k _ => (range_eq_bot_iff 𝒜 V k).1 (hbot k) v
    obtain ⟨i, hi_top⟩ := hexists
    have hi_id : ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := (range_eq_top_iff 𝒜 V i).1 hi_top
    refine ⟨i, ?_, fun j hj => ?_⟩
    · rw [hi_top]
      exact (LinearEquiv.isSimpleModule_iff Submodule.topEquiv).2 hV
    · rcases hclass j with hb | ht
      · exact hb
      · exfalso
        have hj_id : ∀ v : V, (Pi.single j 1 : ∀ i, 𝒜 i) • v = v := (range_eq_top_iff 𝒜 V j).1 ht
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine hv ?_
        have h1 : (Pi.single i 1 : ∀ i, 𝒜 i) • ((Pi.single j 1 : ∀ i, 𝒜 i) • v) = 0 := by
          rw [single_smul_single_smul, if_neg (fun h : i = j => hj h.symm)]
        rw [hj_id v, hi_id v] at h1
        exact h1
  · -- (⇐) exactly one `i` with `1ᵢ V` simple and all other `1ⱼ V = ⊥`. Then `1ᵢ` acts as the
    -- identity, so `V ≅ 1ᵢ V` is simple.
    rintro ⟨i, hi_simple, hj_bot⟩
    have hzero : ∀ j, j ≠ i → ∀ v : V, (Pi.single j 1 : ∀ i, 𝒜 i) • v = 0 :=
      fun j hj => (range_eq_bot_iff 𝒜 V j).1 (hj_bot j hj)
    have hi_id : ∀ v : V, (Pi.single i 1 : ∀ i, 𝒜 i) • v = v := by
      intro v
      have key : (∑ k, (Pi.single k 1 : ∀ i, 𝒜 i) • v) = (Pi.single i 1 : ∀ i, 𝒜 i) • v :=
        Finset.sum_eq_single i (fun k _ hk => hzero k hk v) (fun h => absurd (Finset.mem_univ i) h)
      rw [sum_single_smul] at key
      exact key.symm
    have hi_top : LinearMap.range (idemProj 𝒜 V i) = ⊤ := (range_eq_top_iff 𝒜 V i).2 hi_id
    rw [hi_top] at hi_simple
    exact (LinearEquiv.isSimpleModule_iff Submodule.topEquiv).1 hi_simple

end PartA

/-! ## Part (a), classification in terms of the factor algebras

Part (a) of the problem asks to *classify* the irreducibles of `A = ⊕ᵢ Aᵢ` **in terms of the
irreducibles of the factors `Aᵢ`**. `simpleModule_prod_iff` above pins down the summand
`1ᵢ V` but keeps it a module over the full product `∀ j, 𝒜 j`. Here we supply the missing
factor-algebra content: the *inflation* of a factor representation to the product, its
simplicity/isomorphism correspondence, the genuine `𝒜 i`-module structure on the summand
`1ᵢ V`, and the resulting classification of the product's irreducibles as inflations of the
factors' irreducibles from a unique index. -/

section Inflation

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]

set_option linter.unusedVariables false in
/-- **Inflation.** The type `W`, to be regarded as a representation of the product algebra
`∀ j, 𝒜 j` through its `i`-th coordinate: `c` acts as `c i`. Concretely this is restriction
of scalars along the surjective coordinate evaluation `Pi.evalRingHom 𝒜 i`. -/
@[nolint unusedArguments]
def Inflate {r : ℕ} (𝒜 : Fin r → Type*) (i : Fin r) (W : Type*) : Type _ := W

namespace Inflate

variable {𝒜} {i : Fin r} {W W₁ W₂ : Type*}

instance [AddCommGroup W] : AddCommGroup (Inflate 𝒜 i W) := inferInstanceAs (AddCommGroup W)

/-- An inflation remains nontrivial when its underlying factor module is nontrivial. -/
instance [AddCommGroup W] [Nontrivial W] : Nontrivial (Inflate 𝒜 i W) :=
  inferInstanceAs (Nontrivial W)

instance [AddCommGroup W] [Module (𝒜 i) W] : Module (𝒜 i) (Inflate 𝒜 i W) :=
  inferInstanceAs (Module (𝒜 i) W)

/-- The product algebra `∀ j, 𝒜 j` acts on an inflation through its `i`-th coordinate. -/
instance instProdModule [AddCommGroup W] [Module (𝒜 i) W] :
    Module (∀ j, 𝒜 j) (Inflate 𝒜 i W) :=
  Module.compHom (Inflate 𝒜 i W) (Pi.evalRingHom 𝒜 i)

/-- On an inflation, the product algebra acts through the `i`-th coordinate. -/
theorem prod_smul_def [AddCommGroup W] [Module (𝒜 i) W]
    (c : ∀ j, 𝒜 j) (w : Inflate 𝒜 i W) : c • w = c i • w := by
  change (Pi.evalRingHom 𝒜 i c) • w = c i • w
  rw [Pi.evalRingHom_apply]

/-- The coordinate idempotent `1ᵢ(a) = Pi.single i a` acts through the factor action. -/
theorem single_smul [AddCommGroup W] [Module (𝒜 i) W] (a : 𝒜 i) (w : Inflate 𝒜 i W) :
    (Pi.single i a : ∀ j, 𝒜 j) • w = a • w := by
  rw [prod_smul_def, Pi.single_eq_same]

/-- The identity map, as a bijection semilinear along the coordinate evaluation, from the
inflation of `W` onto the factor module `W`. -/
def toFactor [AddCommGroup W] [Module (𝒜 i) W] :
    Inflate 𝒜 i W →ₛₗ[Pi.evalRingHom 𝒜 i] W where
  toFun w := w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity semilinear map from an inflation to its underlying factor module is bijective. -/
theorem toFactor_bijective [AddCommGroup W] [Module (𝒜 i) W] :
    Function.Bijective (toFactor (𝒜 := 𝒜) (i := i) (W := W)) :=
  ⟨fun _ _ h => h, fun w => ⟨w, rfl⟩⟩

/-- **Simplicity correspondence.** A factor module `W` is simple over `𝒜 i` iff its inflation
is simple over the product algebra. In particular the submodule lattices correspond. -/
theorem isSimpleModule_iff [AddCommGroup W] [Module (𝒜 i) W] :
    IsSimpleModule (∀ j, 𝒜 j) (Inflate 𝒜 i W) ↔ IsSimpleModule (𝒜 i) W :=
  LinearMap.isSimpleModule_iff_of_bijective _ toFactor_bijective

/-- **Functoriality of inflation.** An `𝒜 i`-linear equivalence of factor modules inflates to
an equivalence of product-algebra representations. -/
def congr [AddCommGroup W₁] [Module (𝒜 i) W₁] [AddCommGroup W₂] [Module (𝒜 i) W₂]
    (e : W₁ ≃ₗ[𝒜 i] W₂) : Inflate 𝒜 i W₁ ≃ₗ[∀ j, 𝒜 j] Inflate 𝒜 i W₂ where
  toFun w := e w
  invFun w := e.symm w
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' _ _ := e.map_add _ _
  map_smul' c w := by
    simp only [prod_smul_def, RingHom.id_apply]
    exact map_smul e (c i) (w : W₁)

/-- Conversely, an equivalence of inflations restricts to an `𝒜 i`-linear equivalence of the
factor modules. -/
def ofCongr [AddCommGroup W₁] [Module (𝒜 i) W₁] [AddCommGroup W₂] [Module (𝒜 i) W₂]
    (e : Inflate 𝒜 i W₁ ≃ₗ[∀ j, 𝒜 j] Inflate 𝒜 i W₂) : W₁ ≃ₗ[𝒜 i] W₂ where
  toFun w := e w
  invFun w := e.symm w
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' _ _ := e.map_add _ _
  map_smul' a w := by
    rw [RingHom.id_apply, ← single_smul, map_smul, single_smul]

/-- **The factor index is an isomorphism invariant.** Inflations of nontrivial modules from
different factors are never isomorphic as product-algebra representations. -/
theorem index_eq_of_equiv {i₁ i₂ : Fin r} {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module (𝒜 i₁) W₁] [Nontrivial W₁]
    [AddCommGroup W₂] [Module (𝒜 i₂) W₂]
    (e : Inflate 𝒜 i₁ W₁ ≃ₗ[∀ j, 𝒜 j] Inflate 𝒜 i₂ W₂) : i₁ = i₂ := by
  by_contra h
  obtain ⟨w, hw⟩ := exists_ne (0 : Inflate 𝒜 i₁ W₁)
  apply hw
  have key : e (Pi.single i₁ 1 • w) = Pi.single i₁ 1 • e w := map_smul e _ _
  rw [prod_smul_def, prod_smul_def, Pi.single_eq_same, one_smul,
      Pi.single_eq_of_ne (Ne.symm h), zero_smul] at key
  exact e.map_eq_zero_iff.mp key

end Inflate

end Inflation

section FactorClassification

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]
  (V : Type*) [AddCommGroup V] [Module (∀ i, 𝒜 i) V]

/-- The unit idempotents multiply coordinatewise: `1ᵢ(a) · 1ᵢ(b) = 1ᵢ(a b)`. -/
theorem single_mul_single (i : Fin r) (a b : 𝒜 i) :
    (Pi.single i a : ∀ i, 𝒜 i) * Pi.single i b = Pi.single i (a * b) := by
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- **The summand `1ᵢ V` is a genuine representation of the factor algebra `𝒜 i`**, with `a`
acting through `1ᵢ(a) = Pi.single i a`. This is well defined because `1ᵢ` acts as the
identity on its own range. -/
instance factorSummandModule (i : Fin r) :
    Module (𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) where
  smul a x := ⟨(Pi.single i a : ∀ j, 𝒜 j) • (x : V), by
    rw [mem_range_idemProj, ← mul_smul, single_mul_single, one_mul]⟩
  one_smul x := Subtype.ext (by
    change (Pi.single i (1 : 𝒜 i) : ∀ j, 𝒜 j) • (x : V) = (x : V)
    exact (mem_range_idemProj 𝒜 V i _).1 x.2)
  mul_smul a b x := Subtype.ext (by
    change (Pi.single i (a * b) : ∀ j, 𝒜 j) • (x : V)
      = (Pi.single i a : ∀ j, 𝒜 j) • ((Pi.single i b : ∀ j, 𝒜 j) • (x : V))
    rw [← mul_smul, single_mul_single])
  smul_zero a := Subtype.ext (by
    change (Pi.single i a : ∀ j, 𝒜 j) • (0 : V) = 0
    rw [smul_zero])
  smul_add a x y := Subtype.ext (by
    change (Pi.single i a : ∀ j, 𝒜 j) • ((x : V) + (y : V))
      = (Pi.single i a : ∀ j, 𝒜 j) • (x : V) + (Pi.single i a : ∀ j, 𝒜 j) • (y : V)
    rw [smul_add])
  add_smul a b x := Subtype.ext (by
    change (Pi.single i (a + b) : ∀ j, 𝒜 j) • (x : V)
      = (Pi.single i a : ∀ j, 𝒜 j) • (x : V) + (Pi.single i b : ∀ j, 𝒜 j) • (x : V)
    rw [Pi.single_add, add_smul])
  zero_smul x := Subtype.ext (by
    change (Pi.single i (0 : 𝒜 i) : ∀ j, 𝒜 j) • (x : V) = 0
    rw [Pi.single_zero, zero_smul])

/-- Coercion to the ambient product module preserves the factor-summand action. -/
@[simp] theorem factorSummandModule_smul_coe (i : Fin r) (a : 𝒜 i)
    (x : LinearMap.range (idemProj 𝒜 V i)) :
    ((a • x : LinearMap.range (idemProj 𝒜 V i)) : V) = (Pi.single i a : ∀ j, 𝒜 j) • (x : V) :=
  rfl

/-- On the summand `1ᵢ V` the product-algebra action agrees with the inflation of the factor
`𝒜 i`-action: `c • x = 1ᵢ(c i) • x`, because every element of `1ᵢ V` is fixed by `1ᵢ`. -/
theorem prod_smul_summand_eq (i : Fin r) (c : ∀ j, 𝒜 j)
    (x : LinearMap.range (idemProj 𝒜 V i)) :
    (c • x : LinearMap.range (idemProj 𝒜 V i))
      = (c i • x : LinearMap.range (idemProj 𝒜 V i)) := by
  apply Subtype.ext
  rw [factorSummandModule_smul_coe]
  have hx : (Pi.single i 1 : ∀ j, 𝒜 j) • (x : V) = (x : V) := (mem_range_idemProj 𝒜 V i _).1 x.2
  change (c : ∀ j, 𝒜 j) • (x : V) = (Pi.single i (c i) : ∀ j, 𝒜 j) • (x : V)
  conv_lhs => rw [← hx, ← mul_smul]
  congr 1
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- The identity as a bijection semilinear along the coordinate evaluation, from `1ᵢ V` over
the product algebra to `1ᵢ V` over the factor `𝒜 i`. -/
def summandToFactor (i : Fin r) :
    LinearMap.range (idemProj 𝒜 V i) →ₛₗ[Pi.evalRingHom 𝒜 i]
      LinearMap.range (idemProj 𝒜 V i) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by rw [Pi.evalRingHom_apply]; exact prod_smul_summand_eq 𝒜 V i c x

/-- **Problem 3.3.3(a), simplicity in factor terms.** The summand `1ᵢ V` is simple over the
product algebra iff it is simple over the factor algebra `𝒜 i`. -/
theorem isSimpleModule_summand_iff (i : Fin r) :
    IsSimpleModule (∀ j, 𝒜 j) (LinearMap.range (idemProj 𝒜 V i)) ↔
      IsSimpleModule (𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) :=
  LinearMap.isSimpleModule_iff_of_bijective (summandToFactor 𝒜 V i)
    ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩

/-- **Problem 3.3.3(a), classification.** A representation `V` of `A = ⊕ᵢ Aᵢ` is irreducible
if and only if, for exactly one `i`, the summand `1ᵢ V` is an irreducible representation of
the factor algebra `𝒜 i` while `1ⱼ V = 0` for all other `j`. This is the book's
classification of the irreducibles of `A` in terms of those of the factors. -/
theorem simpleModule_prod_iff_factor :
    IsSimpleModule (∀ i, 𝒜 i) V ↔
      ∃ i, IsSimpleModule (𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) ∧
        ∀ j, j ≠ i → LinearMap.range (idemProj 𝒜 V j) = ⊥ := by
  rw [simpleModule_prod_iff]
  refine exists_congr fun i => ?_
  rw [isSimpleModule_summand_iff]

/-- The summand `1ᵢ V`, as a product-algebra representation, is the inflation of the factor
`𝒜 i`-representation `1ᵢ V`. -/
def summandEquivInflate (i : Fin r) :
    LinearMap.range (idemProj 𝒜 V i) ≃ₗ[∀ j, 𝒜 j]
      Inflate 𝒜 i (LinearMap.range (idemProj 𝒜 V i)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    rw [Inflate.prod_smul_def]
    exact prod_smul_summand_eq 𝒜 V i c x

/-- **Every irreducible representation of `A = ⊕ᵢ Aᵢ` is (isomorphic to) an irreducible
representation of a factor `𝒜 i`, for a unique `i`**, exhibited by the summand `1ᵢ V ≅ V`. -/
theorem exists_isSimpleFactor [IsSimpleModule (∀ i, 𝒜 i) V] :
    ∃ i, IsSimpleModule (𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) ∧
      Nonempty (V ≃ₗ[∀ i, 𝒜 i] LinearMap.range (idemProj 𝒜 V i)) := by
  obtain ⟨i, hi, hbot⟩ := (simpleModule_prod_iff_factor 𝒜 V).1 ‹_›
  refine ⟨i, hi, ⟨(LinearEquiv.ofTop _ ?_).symm⟩⟩
  rw [eq_top_iff]
  intro v _
  have hfix : (Pi.single i 1 : ∀ j, 𝒜 j) • v = v := by
    have hsum : (∑ j, (Pi.single j 1 : ∀ j, 𝒜 j) • v) = v := sum_single_smul 𝒜 V v
    rw [Finset.sum_eq_single i (fun j _ hj => (range_eq_bot_iff 𝒜 V j).1 (hbot j hj) v)
        (fun h => absurd (Finset.mem_univ i) h)] at hsum
    exact hsum
  rw [mem_range_idemProj]; exact hfix

/-- **Every irreducible representation of `A = ⊕ᵢ Aᵢ` is the inflation of an irreducible
representation of a unique factor `𝒜 i`.** Combined with `Inflate.index_eq_of_equiv` and
`Inflate.congr`/`Inflate.ofCongr`, this classifies the irreducibles of `A` up to isomorphism
by pairs `(i, irreducible 𝒜 i-representation)`. -/
theorem exists_inflate_of_isSimple [IsSimpleModule (∀ i, 𝒜 i) V] :
    ∃ i, IsSimpleModule (𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) ∧
      Nonempty (V ≃ₗ[∀ j, 𝒜 j] Inflate 𝒜 i (LinearMap.range (idemProj 𝒜 V i))) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := exists_isSimpleFactor 𝒜 V
  exact ⟨i, hi, ⟨e.trans (summandEquivInflate 𝒜 V i)⟩⟩

end FactorClassification

/-! ## Part (b): representations of a single matrix algebra `Mat_d(k)`

We follow the book's elementary matrix-unit argument (Etingof, hint to Problem 3.3.3(b)),
deliberately avoiding the Wedderburn–Artin machinery used in `Theorem3_3_1`. The key device
is, for a fixed nonzero `v` fixed by the idempotent `E₀₀`, the `Mat_d(k)`-linear map
`ψ_v : k^d → V`, `w ↦ ∑ₐ wₐ • (E_{a0} • v)`, whose image is the subrepresentation `S(v)`.
-/

open scoped Matrix.Module

section MatrixAux

variable {k : Type*} [Field k] {d : ℕ} [NeZero d]
  {V : Type*} [AddCommGroup V] [Module k V]
  [Module (Matrix (Fin d) (Fin d) k) V]
  [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]

omit [NeZero d] in
/-- Scalars from the base field commute past the matrix action: `A • (c • x) = c • (A • x)`.
This follows from `IsScalarTower k (Matrix …) V` because `c` acts as the central scalar
matrix `c • 1`. -/
private theorem smul_comm_k (A : Matrix (Fin d) (Fin d) k) (c : k) (x : V) :
    A • (c • x) = c • (A • x) := by
  conv_lhs => rw [show c • x = (c • (1 : Matrix (Fin d) (Fin d) k)) • x by
    rw [smul_assoc, one_smul]]
  rw [← mul_smul, mul_smul_comm, mul_one, smul_assoc]

omit [NeZero d] [Module k V] [IsScalarTower k (Matrix (Fin d) (Fin d) k) V] in
/-- The matrix units act as `E_{ij} • (E_{lm} • v) = δ_{jl} E_{im} • v`. -/
private theorem E_smul_E (i j l m : Fin d) (v : V) :
    (Matrix.single i j 1 : Matrix (Fin d) (Fin d) k) •
        ((Matrix.single l m 1 : Matrix (Fin d) (Fin d) k) • v)
      = if j = l then (Matrix.single i m 1 : Matrix (Fin d) (Fin d) k) • v else 0 := by
  rw [← mul_smul]
  by_cases h : j = l
  · subst h; simp
  · simp [h]

omit [NeZero d] in
/-- The diagonal matrix units sum to the identity matrix. -/
private theorem sum_single_diag_eq_one :
    (∑ i, (Matrix.single i i 1 : Matrix (Fin d) (Fin d) k)) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp [and_self, Finset.sum_ite_eq']
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hab (h.1.symm.trans h.2)

omit [NeZero d] [Module k V] [IsScalarTower k (Matrix (Fin d) (Fin d) k) V] in
/-- The diagonal matrix units act as `∑ᵢ E_{ii} • v = v`. -/
private theorem sum_E_diag_smul (v : V) :
    (∑ i, (Matrix.single i i 1 : Matrix (Fin d) (Fin d) k) • v) = v := by
  rw [← Finset.sum_smul, sum_single_diag_eq_one, one_smul]

/-- Pulling a matrix `A` through a matrix-unit column action:
`A • (E_{a0} • v) = ∑ᵢ Aᵢₐ • (E_{i0} • v)`. -/
private theorem A_smul_col (A : Matrix (Fin d) (Fin d) k) (a : Fin d) (v : V) :
    A • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v)
      = ∑ i, A i a • ((Matrix.single i 0 1 : Matrix (Fin d) (Fin d) k) • v) := by
  rw [← mul_smul]
  rw [show A * (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k)
        = ∑ i, A i a • Matrix.single i 0 1 from ?_]
  · rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_assoc]
  · ext p q
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply]
    rw [Finset.sum_eq_single a (fun l _ hl => by simp [Ne.symm hl]) (by simp),
        Finset.sum_eq_single p (fun i _ hi => by simp [hi]) (by simp)]
    simp

/-- The `Mat_d(k)`-linear map `ψ_v : k^d → V`, `w ↦ ∑ₐ wₐ • (E_{a0} • v)`. Its image is the
subrepresentation `S(v) = ⟨E_{00}v, E_{10}v, …⟩`. -/
private def psi (v : V) : (Fin d → k) →ₗ[Matrix (Fin d) (Fin d) k] V where
  toFun w := ∑ a, w a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v)
  map_add' w w' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' A w := by
    change (∑ a, (A • w) a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v))
        = A • ∑ a, w a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v)
    rw [Finset.smul_sum]
    simp_rw [smul_comm_k, A_smul_col, Finset.smul_sum, smul_smul,
      Matrix.Module.smul_apply, Finset.sum_smul, smul_eq_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm]

@[simp]
private theorem psi_apply (v : V) (w : Fin d → k) :
    psi v w = ∑ a, w a • ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v) := rfl

end MatrixAux

section PartB

variable (k : Type*) [Field k] (d : ℕ) [NeZero d]

/-- **Problem 3.3.3(b), existence.** The standard representation `k^d` is an irreducible
representation of `Mat_d(k)`. Any nonzero vector generates the whole module: if `vᵢ ≠ 0`
then `E_{ji} (vᵢ)⁻¹ • v = e_j`, so every standard basis vector lies in a nonzero
submodule. -/
theorem std_isSimpleModule :
    IsSimpleModule (Matrix (Fin d) (Fin d) k) (Fin d → k) where
  eq_bot_or_eq_top s := by
    rcases eq_or_ne s ⊥ with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hc; push Not at hc; exact hne (funext fun j => by simp [hc j])
      have basis_mem : ∀ j, (Pi.single j (1 : k) : Fin d → k) ∈ s := fun j => by
        have hmem := s.smul_mem (Matrix.single j i (v i)⁻¹) hv
        rwa [Matrix.Module.single_smul, smul_eq_mul, inv_mul_cancel₀ hi] at hmem
      rw [eq_top_iff]
      intro w _
      have hw : w = ∑ j, Pi.single j (w j) := by
        funext l
        rw [Finset.sum_apply]
        simp only [Pi.single_apply]
        rw [Finset.sum_ite_eq]
        simp
      rw [hw]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hsingle : (Pi.single j (w j) : Fin d → k)
          = (Matrix.single j j (w j) : Matrix (Fin d) (Fin d) k) •
            (Pi.single j (1 : k) : Fin d → k) := by
        rw [Matrix.Module.single_smul]; simp
      rw [hsingle]
      exact Submodule.smul_mem _ _ (basis_mem j)

/-- **Problem 3.3.3(b), uniqueness.** Every finite dimensional irreducible representation of
`Mat_d(k)` is isomorphic to the standard representation `k^d`. We choose a nonzero `v` fixed
by the idempotent `E₀₀`; then `ψ_v : k^d → V` is injective and its image is a nonzero
subrepresentation, hence all of `V` by simplicity. -/
theorem simpleModule_iso_std (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (Matrix (Fin d) (Fin d) k) V
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  -- Some diagonal idempotent does not kill `w₀`.
  obtain ⟨a, ha⟩ : ∃ a, (Matrix.single a a 1 : Matrix (Fin d) (Fin d) k) • w₀ ≠ 0 := by
    by_contra hc; push Not at hc
    refine hw₀ ?_
    rw [← sum_E_diag_smul (k := k) (d := d) w₀]
    exact Finset.sum_eq_zero fun a _ => hc a
  -- `v := E_{0a} • w₀` lies in `E₀₀ V` and is nonzero.
  set v : V := (Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • w₀ with hv_def
  have hEv : (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • v = v := by
    rw [hv_def, E_smul_E]; simp
  have hv_ne : v ≠ 0 := fun h => ha (by
    have h2 : (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • v
        = (Matrix.single a a 1 : Matrix (Fin d) (Fin d) k) • w₀ := by
      rw [hv_def, E_smul_E]; simp
    rw [h, smul_zero] at h2; exact h2.symm)
  -- `ψ_v` is injective.
  have hpsi_inj : Function.Injective (psi (k := k) (d := d) (V := V) v) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, psi_apply] at hw
    ext b
    have key : w b • v = 0 := by
      have h0 : (Matrix.single 0 b 1 : Matrix (Fin d) (Fin d) k) •
          (∑ c, w c • ((Matrix.single c 0 1 : Matrix (Fin d) (Fin d) k) • v)) = 0 := by
        rw [hw, smul_zero]
      rw [Finset.smul_sum] at h0
      simp_rw [smul_comm_k, E_smul_E] at h0
      simp_rw [smul_ite, smul_zero] at h0
      rw [Finset.sum_ite_eq] at h0
      simpa [hEv] using h0
    rcases smul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hv_ne
  -- The image of `ψ_v` contains `v ≠ 0`, so by simplicity it is all of `V`.
  have hrange : LinearMap.range (psi (k := k) (d := d) (V := V) v) = ⊤ := by
    rcases eq_bot_or_eq_top (LinearMap.range (psi (k := k) (d := d) (V := V) v)) with hb | ht
    · exfalso; apply hv_ne
      have hvmem : v ∈ LinearMap.range (psi (k := k) (d := d) (V := V) v) :=
        ⟨Pi.single 0 1, by rw [psi_apply]; simp [Pi.single_apply, hEv]⟩
      rw [hb, Submodule.mem_bot] at hvmem; exact hvmem
    · exact ht
  exact ⟨(LinearEquiv.ofBijective (psi (k := k) (d := d) (V := V) v)
    ⟨hpsi_inj, LinearMap.range_eq_top.mp hrange⟩).symm⟩

/-- **Problem 3.3.3(b), decomposition.** Every finite dimensional representation of
`Mat_d(k)` is a direct sum of copies of the standard representation `k^d`: it is isomorphic
to `(k^d)^n = Fin n → (Fin d → k)` for some `n`. Take a basis `v₁,…,vₙ` of `E₀₀ V`; the map
`Ψ(f) = ∑ᵢ ψ_{vᵢ}(fᵢ)` is a `Mat_d(k)`-linear isomorphism. -/
theorem finite_iso_std_pow (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] :
    ∃ n : ℕ, Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin n → (Fin d → k))) := by
  classical
  -- `W = E₀₀ V`, the range of the `k`-linear idempotent `x ↦ E₀₀ • x`.
  let P0 : V →ₗ[k] V :=
    { toFun := fun x => (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • x
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun c x => by simp only [RingHom.id_apply]; rw [smul_comm_k] }
  set W := LinearMap.range P0 with hW_def
  set n := Module.finrank k W with hn_def
  let b := Module.finBasis k W
  -- Each basis vector is fixed by `E₀₀`.
  have hfix : ∀ i, (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • (b i : V) = (b i : V) := by
    intro i
    obtain ⟨x, hx⟩ := (b i).2
    have hx' : (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) • x = (b i : V) := hx
    rw [← hx', E_smul_E]; simp
  -- The linear map `Ψ : (Fin n → k^d) → V`.
  let Ψ : (Fin n → (Fin d → k)) →ₗ[Matrix (Fin d) (Fin d) k] V :=
    ∑ i, (psi (k := k) (d := d) (V := V) (b i : V)) ∘ₗ (LinearMap.proj i)
  have hΨ : ∀ f, Ψ f = ∑ i, psi (k := k) (d := d) (V := V) (b i : V) (f i) := fun f => by
    change (∑ i, (psi (k := k) (d := d) (V := V) (b i : V)) ∘ₗ (LinearMap.proj i)) f = _
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  -- Linear independence of the basis vectors seen inside `V`.
  have hli : LinearIndependent k (fun i => (b i : V)) :=
    (b.linearIndependent).map' W.subtype (Submodule.ker_subtype W)
  -- `Ψ` is injective: applying `E_{0b}` extracts the `b`-th column coefficients.
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker, hΨ] at hf
    ext i j
    have key : (∑ i, (f i j) • (b i : V)) = 0 := by
      have h0 : (Matrix.single 0 j 1 : Matrix (Fin d) (Fin d) k) •
          (∑ i, psi (k := k) (d := d) (V := V) (b i : V) (f i)) = 0 := by rw [hf, smul_zero]
      simp_rw [psi_apply, Finset.smul_sum, smul_comm_k, E_smul_E,
        smul_ite, smul_zero] at h0
      simp_rw [Finset.sum_ite_eq] at h0
      simpa [hfix] using h0
    exact (Fintype.linearIndependent_iff.mp hli (fun i => f i j) key) i
  -- `Ψ` is surjective: reconstruct `x` from the columns `E_{0a} • x ∈ W`.
  have hsurj : Function.Surjective Ψ := by
    intro x
    have hg_mem : ∀ a, (Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x ∈ W := by
      intro a
      refine ⟨(Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x, ?_⟩
      change (Matrix.single 0 0 1 : Matrix (Fin d) (Fin d) k) •
          ((Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x) = _
      rw [E_smul_E]; simp
    refine ⟨fun i a => b.repr ⟨_, hg_mem a⟩ i, ?_⟩
    rw [hΨ]
    have hrepr : ∀ a, (∑ i, (b.repr ⟨_, hg_mem a⟩ i) • (b i : V))
        = (Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x := by
      intro a
      have hsum := congrArg (Submodule.subtype W) (b.sum_repr ⟨_, hg_mem a⟩)
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using hsum
    calc ∑ i, psi (k := k) (d := d) (V := V) (b i : V) (fun a => b.repr ⟨_, hg_mem a⟩ i)
        = ∑ i, ∑ a, (b.repr ⟨_, hg_mem a⟩ i) •
            ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • (b i : V)) := by
          simp_rw [psi_apply]
      _ = ∑ a, ∑ i, (b.repr ⟨_, hg_mem a⟩ i) •
            ((Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) • (b i : V)) := Finset.sum_comm
      _ = ∑ a, (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) •
            (∑ i, (b.repr ⟨_, hg_mem a⟩ i) • (b i : V)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => (smul_comm_k _ _ _).symm
      _ = ∑ a, (Matrix.single a 0 1 : Matrix (Fin d) (Fin d) k) •
            ((Matrix.single 0 a 1 : Matrix (Fin d) (Fin d) k) • x) := by
          simp_rw [hrepr]
      _ = ∑ a, (Matrix.single a a 1 : Matrix (Fin d) (Fin d) k) • x := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [E_smul_E]; simp
      _ = x := sum_E_diag_smul (k := k) (d := d) x
  exact ⟨n, ⟨(LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm⟩⟩

end PartB

/-! ## Part (c): deducing Theorem 3.3.1

Part (c) asks to deduce Theorem 3.3.1 from (a) and (b). The full statement (for
`A = ⊕ᵢ Mat_{dᵢ}(k)`, the irreducibles are the `k^{dᵢ}` and every finite dimensional
representation is a direct sum of copies of them) is recorded and proved as
`Etingof.irreducible_reps_of_matrix_algebra` in `Theorem3_3_1`. -/

end Etingof.Problem3_3_3

-- The enclosing namespace follows the book's numbered `Problem3_3_3` convention. These
-- lowerCamelCase names themselves follow Mathlib naming style; only that stable namespace causes
-- `defsWithUnderscore` to fire.
attribute [nolint defsWithUnderscore]
  Etingof.Problem3_3_3.idemProj
  Etingof.Problem3_3_3.Inflate
  Etingof.Problem3_3_3.Inflate.instAddCommGroup
  Etingof.Problem3_3_3.Inflate.instModule
  Etingof.Problem3_3_3.Inflate.instProdModule
  Etingof.Problem3_3_3.Inflate.toFactor
  Etingof.Problem3_3_3.Inflate.congr
  Etingof.Problem3_3_3.Inflate.ofCongr
  Etingof.Problem3_3_3.factorSummandModule
  Etingof.Problem3_3_3.summandToFactor
  Etingof.Problem3_3_3.summandEquivInflate

-- The first two parameters record the product factor through which the unchanged carrier `W`
-- is inflated; they are used by its instances rather than by the carrier synonym itself.
attribute [nolint defsWithUnderscore unusedArguments] Etingof.Problem3_3_3.Inflate
