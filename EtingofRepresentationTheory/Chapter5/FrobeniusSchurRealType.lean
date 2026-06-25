import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1
import EtingofRepresentationTheory.Chapter5.Definition5_1_4

/-!
# Frobenius-Schur indicator bridge: `FS(ρ) = 1 ⟹ IsRealType ρ`

This file connects the *numerical* Frobenius-Schur indicator
(`Etingof.frobeniusSchurIndicator`, Definition 5.1.4) to the *structural* type
predicate `Etingof.IsRealType` (Definition 5.1.1): a simple complex
representation `ρ` with `frobeniusSchurIndicator ρ = 1` admits a nondegenerate
symmetric `G`-invariant bilinear form, so it is of real type.

This bridge is the shared dependency of the S₃, S₄ and A₅ cases of Example 5.1.3.

## Proof strategy (Etingof, around Theorem 5.1.5)

Work in `Bil := V →ₗ[ℂ] V →ₗ[ℂ] ℂ`, the space of bilinear forms, which carries
the `G`-action `(g · B)(v, w) = B (ρ g⁻¹ v) (ρ g⁻¹ w)` — this is
`Representation.linHom ρ ρ.dual`. The swap `τ B := fun v w => B w v` is
`G`-equivariant with `τ² = 1`; its `+1`/`-1` eigenspaces are the symmetric /
skew-symmetric forms.

1. The invariant forms `Bil^G ≅ Hom_G(V, V*) = IntertwiningMap ρ ρ.dual`; for
   simple `V` this is `0`- or `1`-dimensional (Schur, via
   `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`).
2. The crux trace identity:
   `dim (sym ∩ Bil^G) − dim (skew ∩ Bil^G) = trace(τ ∘ P)
   = (|G|)⁻¹ ∑_g trace(τ ∘ (g·)) = (|G|)⁻¹ ∑_g χ_V(g²) = FS(ρ)`,
   where `P` is the averaging projector onto `Bil^G`. The middle trace
   `trace(τ ∘ (g·))` on `V* ⊗ V*` evaluates to `χ_V(g²) = tr(ρ g)²`, the
   `χ(g²) = χ_{S²} − χ_{Λ²}` identity of Theorem 5.1.5 phrased via the swap.
3. `FS = 1` with `dim(sym∩Bil^G) + dim(skew∩Bil^G) ∈ {0,1}` forces
   `dim(sym∩Bil^G) = 1`: a nonzero invariant **symmetric** form exists.
4. Nondegeneracy: the radical `{v | ∀ w, B v w = 0} = ker B` is a `ρ`-invariant
   submodule, proper (since `B ≠ 0`), hence `⊥` by simplicity. So `B` is
   nondegenerate.

Step 4 (the nondegeneracy bridge) is fully proved below as
`Etingof.nondegenerate_of_invariant_of_simple`. Steps 1–3 — the existence of a
nonzero invariant symmetric form, packaged as
`Etingof.exists_nonzero_invariant_symmetric_of_FS_eq_one` — are the trace-identity
heart and are currently isolated as a `sorry`.
-/

open scoped MonoidAlgebra

namespace Etingof

variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A nonzero `G`-invariant bilinear form on a *simple* representation is
automatically nondegenerate: its left radical `ker B = {v | ∀ w, B v w = 0}` is
a `ρ`-invariant submodule, proper (as `B ≠ 0`), hence `⊥` by simplicity.

No symmetry or finite-dimensionality hypothesis is needed. -/
theorem nondegenerate_of_invariant_of_simple
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hBne : B ≠ 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    ∀ v, (∀ w, B v w = 0) → v = 0 := by
  -- The radical `ker B` is `ρ`-invariant.
  have hRinv : LinearMap.ker B ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext w
    simp only [LinearMap.zero_apply]
    have hgg : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h1 : B (ρ g x) w = B (ρ g x) (ρ g (ρ g⁻¹ w)) := by rw [hgg]
    rw [h1, hinv g x (ρ g⁻¹ w)]
    rw [hx]
    simp
  -- Simplicity transports to the lattice of `ρ`-invariant submodules.
  haveI := hρ
  haveI hSO : IsSimpleOrder ρ.invtSubmodule :=
    (Representation.mapSubmodule ρ).isSimpleOrder_iff.mpr hρ.toIsSimpleOrder
  -- The radical is `⊥` or `⊤`; `B ≠ 0` rules out `⊤`.
  have hker : LinearMap.ker B = ⊥ := by
    rcases hSO.eq_bot_or_eq_top ⟨LinearMap.ker B, hRinv⟩ with h | h
    · simpa using congrArg Subtype.val h
    · exact absurd (LinearMap.ker_eq_top.mp (by simpa using congrArg Subtype.val h)) hBne
  -- `ker B = ⊥` is exactly nondegeneracy.
  intro v hv
  have hv' : v ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker]; ext w; exact hv w
  rw [hker, Submodule.mem_bot] at hv'
  exact hv'

variable [Fintype G] [DecidableEq G] [Module.Finite ℂ V]

/-- **Existence of a nonzero invariant symmetric form when `FS = 1`** (steps 1–3
of the strategy above). For a simple complex representation `ρ` with
`frobeniusSchurIndicator ρ = 1`, there is a nonzero `G`-invariant *symmetric*
bilinear form on `V`.

The proof is the trace-identity argument
`dim(sym ∩ Bil^G) − dim(skew ∩ Bil^G) = FS(ρ)` together with the Schur bound
`dim Bil^G ≤ 1`. Isolated as a `sorry` pending that computation. -/
theorem exists_nonzero_invariant_symmetric_of_FS_eq_one
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hFS : Etingof.frobeniusSchurIndicator ρ = 1) :
    ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ v w, B v w = B w v) ∧ B ≠ 0 ∧ (∀ g v w, B (ρ g v) (ρ g w) = B v w) := by
  sorry

/-- **The FS-indicator bridge.** A simple complex representation whose
Frobenius-Schur indicator equals `1` is of real type (Etingof, around
Theorem 5.1.5; the per-representation companion of Definition 5.1.4). -/
theorem isRealType_of_frobeniusSchurIndicator_eq_one
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hFS : Etingof.frobeniusSchurIndicator ρ = 1) :
    Etingof.IsRealType ρ := by
  obtain ⟨B, hsym, hBne, hinv⟩ :=
    exists_nonzero_invariant_symmetric_of_FS_eq_one ρ hρ hFS
  exact ⟨B, hsym, nondegenerate_of_invariant_of_simple ρ hρ B hBne hinv, hinv⟩

/-!
## L1 — real / rational form ⟹ real type (the linchpin)

The companion construction that does *not* route through the (still isolated)
Frobenius-Schur trace identity: if a simple complex representation is realised by
**real matrices** in some basis (every matrix entry of every `ρ g` is real — a
genuine ℝ-scalar-extension structure, the "real form"), then averaging the
standard coordinate symmetric form over `G` produces a nonzero `G`-invariant
*symmetric* `ℂ`-bilinear form, which is nondegenerate by simplicity. So `ρ` is of
real type. This is the workhorse for the rational matrix reps of `S₃`, `S₄`,
`A₅`: realisation by rational matrices is a special case of a real form.

The averaged form is `B(v, w) = ∑_{g ∈ G} ∑_i ⟨ρ g v, e_i⟩ ⟨ρ g w, e_i⟩` where
`⟨·, e_i⟩ = b.coord i` are the coordinate functionals. Non-vanishing comes from
positivity: each `B(e_{i₀}, e_{i₀}) = ∑_g ∑_i (matrix entry)²` has real entries,
so its real part is `≥` the `g = 1` term `= 1`.
-/

section RealForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard coordinate symmetric bilinear form in the basis `b`, averaged over
`G`: `B(v, w) = ∑_{g} ∑_i (b.coord i (ρ g v)) * (b.coord i (ρ g w))`. -/
private noncomputable def avgCoordForm
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V) : V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  ∑ g : G, (∑ i : ι,
    (LinearMap.mul ℂ ℂ).compl₁₂ (b.coord i) (b.coord i)).compl₁₂ (ρ g) (ρ g)

private theorem avgCoordForm_apply
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V) (v w : V) :
    avgCoordForm ρ b v w
      = ∑ g : G, ∑ i : ι, (b.coord i (ρ g v)) * (b.coord i (ρ g w)) := by
  simp only [avgCoordForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply']

/-- **L1 (the linchpin).** A simple complex representation realised by **real
matrices** in a basis `b` (a real form) is of real type. (Etingof, around
Theorem 5.1.5.) -/
theorem isRealType_of_real_form
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (b : Module.Basis ι ℂ V)
    (hreal : ∀ (g : G) (i j : ι), (LinearMap.toMatrix b b (ρ g) i j).im = 0) :
    Etingof.IsRealType ρ := by
  haveI := hρ
  haveI hNT : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨i₀⟩ := b.index_nonempty
  -- Symmetry: each summand is symmetric because multiplication on `ℂ` is.
  have hsym : ∀ v w, avgCoordForm ρ b v w = avgCoordForm ρ b w v := by
    intro v w
    rw [avgCoordForm_apply, avgCoordForm_apply]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- `G`-invariance: reindex the average by `h ↦ h * g`.
  have hmul : ∀ (g h : G) (x : V), ρ h (ρ g x) = ρ (h * g) x := by
    intro g h x; rw [map_mul]; rfl
  have hinv : ∀ g v w, avgCoordForm ρ b (ρ g v) (ρ g w) = avgCoordForm ρ b v w := by
    intro g v w
    rw [avgCoordForm_apply, avgCoordForm_apply,
      ← Equiv.sum_comp (Equiv.mulRight g)
        (fun h => ∑ i : ι, (b.coord i (ρ h v)) * (b.coord i (ρ h w)))]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hmul g h v, hmul g h w]
  -- Reading a coordinate of `ρ g` as a matrix entry — hence real.
  have hcoord : ∀ (g : G) (i : ι),
      b.coord i (ρ g (b i₀)) = LinearMap.toMatrix b b (ρ g) i i₀ := by
    intro g i; rw [LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  -- Non-vanishing: the real part of `B (b i₀) (b i₀)` is `≥ 1`.
  have hre : (avgCoordForm ρ b (b i₀) (b i₀)).re
      = ∑ g : G, ∑ i : ι, ((b.coord i (ρ g (b i₀))).re) ^ 2 := by
    rw [avgCoordForm_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have him : (b.coord i (ρ g (b i₀))).im = 0 := by rw [hcoord]; exact hreal g i i₀
    rw [Complex.mul_re, him, sq]; ring
  have hnonneg : ∀ g : G, (0 : ℝ) ≤ ∑ i : ι, ((b.coord i (ρ g (b i₀))).re) ^ 2 :=
    fun g => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hone : (∑ i : ι, ((b.coord i (ρ (1 : G) (b i₀))).re) ^ 2) = 1 := by
    have : ∀ i : ι, b.coord i (ρ (1 : G) (b i₀)) = (if i = i₀ then (1 : ℂ) else 0) := by
      intro i
      rw [map_one, Module.End.one_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      simp [eq_comm]
    simp only [this]
    rw [Finset.sum_congr rfl (fun i _ => by split <;> simp : ∀ i ∈ Finset.univ,
      ((if i = i₀ then (1 : ℂ) else 0).re) ^ 2 = (if i = i₀ then (1 : ℝ) else 0))]
    simp
  have hge : (1 : ℝ) ≤ (avgCoordForm ρ b (b i₀) (b i₀)).re := by
    rw [hre, ← hone]
    exact Finset.single_le_sum (fun g _ => hnonneg g) (Finset.mem_univ (1 : G))
  have hval_ne : avgCoordForm ρ b (b i₀) (b i₀) ≠ 0 := by
    intro h0
    rw [h0] at hge
    simp only [Complex.zero_re] at hge
    linarith
  have hBne : avgCoordForm ρ b ≠ 0 := by
    intro h0
    exact hval_ne (by rw [h0]; simp)
  exact ⟨avgCoordForm ρ b, hsym,
    nondegenerate_of_invariant_of_simple ρ hρ _ hBne hinv, hinv⟩

/-- **L1 corollary — rational form ⟹ real type.** A simple complex representation
realised by **rational matrices** in a basis is of real type (`ℚ ⊂ ℝ`): this is
the direct workhorse for the rational reps of `S₃`, `S₄`, `A₅`. -/
theorem isRealType_of_rational_form
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (b : Module.Basis ι ℂ V)
    (hrat : ∀ (g : G) (i j : ι), ∃ q : ℚ, LinearMap.toMatrix b b (ρ g) i j = (q : ℂ)) :
    Etingof.IsRealType ρ :=
  isRealType_of_real_form ρ hρ b fun g i j => by
    obtain ⟨q, hq⟩ := hrat g i j; rw [hq]; simp

end RealForm

/-!
## L2 — ambivalent ⟹ real character

If every `g ∈ G` is conjugate to its inverse (`G` is *ambivalent*), then every
character value `χ(g) = tr(ρ g)` is real: `χ(g) = χ(g⁻¹)` by conjugacy-invariance
of the character, and `χ(g⁻¹) = conj(χ(g))` always (the eigenvalues of `ρ g` are
roots of unity). Hence `χ(g) = conj(χ(g))`, i.e. `χ(g).im = 0`.
-/

open Polynomial in
/-- `reverse` is multiplicative over a `Multiset` of polynomials in a domain. -/
private lemma reverse_multiset_prod {R : Type*} [CommRing R] [NoZeroDivisors R]
    (s : Multiset R[X]) : s.prod.reverse = (s.map Polynomial.reverse).prod := by
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.prod_zero, Multiset.map_zero]
    rw [show (1 : R[X]) = C 1 from (map_one C).symm, Polynomial.reverse_C]
  | cons a s ih =>
    rw [Multiset.prod_cons, Polynomial.reverse_mul_of_domain, ih, Multiset.map_cons,
      Multiset.prod_cons]

open Polynomial in
/-- The reverse of the linear factor `X - a` (for `a ≠ 0`) has the single root `a⁻¹`. -/
private lemma roots_reverse_X_sub_C {a : ℂ} (ha : a ≠ 0) :
    ((X - C a).reverse).roots = {a⁻¹} := by
  have hu : (-a) ≠ 0 := neg_ne_zero.mpr ha
  have hrev : (X - C a).reverse = C ((Units.mk0 (-a) hu : ℂˣ) : ℂ) * X + C 1 := by
    rw [Polynomial.reverse, natDegree_X_sub_C, sub_eq_add_neg, ← C_neg, reflect_add,
      reflect_one_X, reflect_C, pow_one, Units.val_mk0, C_1]
    ring
  rw [hrev, roots_C_mul_X_add_C_of_IsUnit, Multiset.singleton_inj, mul_one,
    Units.val_inv_eq_inv_val, Units.val_mk0, inv_neg, neg_neg]

open Polynomial in
/-- For a monic polynomial that splits over `ℂ` and has no zero root, the roots of its
`reverse` are exactly the inverses of its roots. -/
private lemma roots_reverse_eq_map_inv {p : ℂ[X]} (hsp : p.Splits)
    (hm : p.Monic) (h0 : (0 : ℂ) ∉ p.roots) :
    p.reverse.roots = p.roots.map (·⁻¹) := by
  set R := p.roots with hR
  have key : ∀ a ∈ R, ((X - C a).reverse).roots = ({a⁻¹} : Multiset ℂ) :=
    fun a ha => roots_reverse_X_sub_C (fun h => h0 (h ▸ ha))
  have hfact : p = (R.map (fun a => X - C a)).prod := hsp.eq_prod_roots_of_monic hm
  rw [hfact, reverse_multiset_prod, Multiset.map_map, roots_multiset_prod,
    Multiset.bind_map]
  · simp only [Function.comp_apply]
    rw [Multiset.bind_congr (g := fun a => ({a⁻¹} : Multiset ℂ)) (fun a ha => key a ha),
      Multiset.bind_singleton]
  · simp only [Multiset.mem_map, Function.comp_apply, not_exists, not_and]
    exact fun a _ hcontra => X_sub_C_ne_zero a (Polynomial.reverse_eq_zero.mp hcontra)

open Polynomial Matrix in
/-- For a complex matrix `A` of finite multiplicative order, `tr(A⁻¹) = conj(tr A)`:
the eigenvalues are roots of unity, so `tr(A⁻¹) = ∑ λᵢ⁻¹ = ∑ conj λᵢ = conj(∑ λᵢ)`. -/
private lemma matrix_trace_inv_eq_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {n : ℕ} (hn : 0 < n) (hpow : A ^ n = 1) :
    A⁻¹.trace = starRingEnd ℂ A.trace := by
  -- `A` is invertible since `A * A^(n-1) = 1` and `A^(n-1) * A = 1`.
  have hr : A * A ^ (n - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hn]; exact hpow
  have hl : A ^ (n - 1) * A = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn]; exact hpow
  have hunit : IsUnit A := ⟨⟨A, A ^ (n - 1), hr, hl⟩, rfl⟩
  -- `A.charpoly` is monic and splits over `ℂ`.
  have hmon : A.charpoly.Monic := A.charpoly_monic
  have hsplit : A.charpoly.Splits := IsAlgClosed.splits _
  -- No zero root: the product of the roots is `det A ≠ 0`.
  have hdet : A.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  have h0 : (0 : ℂ) ∉ A.charpoly.roots := by
    intro hmem
    have hprod : A.charpoly.roots.prod = 0 := Multiset.prod_eq_zero hmem
    rw [← Matrix.det_eq_prod_roots_charpoly A] at hprod
    exact hdet hprod
  -- Each root `λ` of the characteristic polynomial is a root of unity.
  have hroot : ∀ μ ∈ A.charpoly.roots, μ ^ n = 1 := by
    intro μ hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact (Polynomial.mem_roots'.mp hμ).2
    obtain ⟨v, hv_mem, hv0⟩ := hev.exists_hasEigenvector
    have hveq : Matrix.toLin' A v = μ • v := Module.End.mem_eigenspace_iff.mp hv_mem
    have key : ∀ k, (Matrix.toLin' A ^ k) v = μ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, Module.End.mul_apply, hveq, map_smul, ih, smul_smul, ← pow_succ']
    have hkey := key n
    rw [← Matrix.toLin'_pow, hpow, Matrix.toLin'_one, LinearMap.id_apply] at hkey
    have hsmul : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← hkey, sub_self]
    rcases smul_eq_zero.mp hsmul with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  -- Star of a root of unity is its inverse.
  have hstar : ∀ μ ∈ A.charpoly.roots, starRingEnd ℂ μ = μ⁻¹ := by
    intro μ hμ
    have hnorm : ‖μ‖ = 1 := by
      have h1 : ‖μ‖ ^ n = 1 := by rw [← norm_pow, hroot μ hμ, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1
    exact (Complex.inv_eq_conj hnorm).symm
  -- `tr(A⁻¹) = ∑ (roots A).map inv`.
  have hinvtr : A⁻¹.trace = (A.charpoly.roots.map (·⁻¹)).sum := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    have hcp : A⁻¹.charpoly =
        C ((-1) ^ Fintype.card ι * Ring.inverse A.det) * A.charpoly.reverse := by
      rw [Matrix.charpoly_inv A hunit, ← Matrix.reverse_charpoly,
        show ((-1 : ℂ[X]) ^ Fintype.card ι) = C ((-1 : ℂ) ^ Fintype.card ι) by
          rw [map_pow, map_neg, map_one], ← C_mul]
    have hc : (-1 : ℂ) ^ Fintype.card ι * Ring.inverse A.det ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero _ (by norm_num))
      rw [Ring.inverse_eq_inv]
      exact inv_ne_zero hdet
    rw [hcp, roots_C_mul _ hc, roots_reverse_eq_map_inv hsplit hmon h0]
  -- `conj(tr A) = ∑ conj(roots A) = ∑ (roots A).map inv`.
  rw [hinvtr, Matrix.trace_eq_sum_roots_charpoly, map_multiset_sum]
  exact congrArg Multiset.sum (Multiset.map_congr rfl (fun μ hμ => (hstar μ hμ).symm))

/-- For a finite-group complex representation, `χ(g⁻¹) = conj(χ(g))`: the
eigenvalues of `ρ g` are roots of unity (since `g` has finite order), so
`χ(g⁻¹) = ∑ λᵢ⁻¹ = ∑ conj λᵢ = conj(∑ λᵢ) = conj(χ(g))`. -/
private theorem character_inv_eq_conj (ρ : Representation ℂ G V) (g : G) :
    Representation.character ρ g⁻¹ = starRingEnd ℂ (Representation.character ρ g) := by
  classical
  -- Pass to a matrix `A := [ρ g]` in a basis; then `[ρ g⁻¹] = A⁻¹` and `A` has finite order.
  let b := Module.finBasis ℂ V
  let E := LinearMap.toMatrixAlgEquiv b
  have hcg : Representation.character ρ g = (E (ρ g)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ b (ρ g)
  have hcgi : Representation.character ρ g⁻¹ = (E (ρ g⁻¹)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ b (ρ g⁻¹)
  have hpow : (E (ρ g)) ^ orderOf g = 1 := by
    rw [← map_pow, ← map_pow ρ, pow_orderOf_eq_one, map_one, map_one]
  have hinv : (E (ρ g))⁻¹ = E (ρ g⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, ← map_mul ρ, inv_mul_cancel, map_one, map_one]
  rw [hcg, hcgi, ← hinv]
  exact matrix_trace_inv_eq_conj (E (ρ g)) (orderOf_pos g) hpow

/-- **L2 — ambivalent ⟹ real character.** If every element of `G` is conjugate to
its own inverse, then every character value of every complex representation is
real (its imaginary part vanishes). Consequently `frobeniusSchurIndicator ρ` is
real, hence `∈ {-1, 0, 1}` for simple `ρ`. (Etingof, around Theorem 5.1.5.) -/
theorem character_im_eq_zero_of_ambivalent
    (h : ∀ g : G, IsConj g g⁻¹) (ρ : Representation ℂ G V) (g : G) :
    (Representation.character ρ g).im = 0 := by
  -- Ambivalence: `χ(g⁻¹) = χ(g)` via conjugacy-invariance of the character.
  obtain ⟨c, hc⟩ := isConj_iff.mp (h g)
  have hconj : Representation.character ρ g⁻¹ = Representation.character ρ g := by
    rw [← hc]; exact Representation.char_conj ρ g c
  -- Combined with `χ(g⁻¹) = conj(χ(g))`: `χ(g)` is fixed by conjugation.
  rw [character_inv_eq_conj] at hconj
  exact Complex.conj_eq_iff_im.mp hconj

/-!
## L3 — quaternionic ⟹ even-dimensional

A representation of quaternionic type carries a nondegenerate invariant
*alternating* form, and a nondegenerate alternating form on a finite-dimensional
space forces even dimension (symplectic basis). (Etingof, discussion after
Definition 5.1.1: "every quaternionic representation is even-dimensional".)
-/

/-- A nondegenerate alternating bilinear form on a finite-dimensional space forces
the dimension to be even.

The slick determinant argument (no symplectic basis needed): an alternating form
is skew-symmetric, so its Gram matrix `M` in any basis satisfies `Mᵀ = -M`. Hence
`det M = det Mᵀ = det (-M) = (-1)ⁿ det M`. If `n = finrank` were odd this gives
`det M = -det M`, so `det M = 0` (characteristic `0`), contradicting the
nondegeneracy `det M ≠ 0`. -/
private theorem even_finrank_of_nondegenerate_alternating
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (halt : ∀ v, B v v = 0)
    (hnondeg : ∀ v, (∀ w, B v w = 0) → v = 0) :
    Even (Module.finrank ℂ V) := by
  -- Alternating ⟹ skew-symmetric: expand `B (v + w) (v + w) = 0`.
  have hskew : ∀ v w, B v w = - B w v := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt] at h
    linear_combination h
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  -- Work with the Gram matrix `M` of `B` in the canonical finite basis.
  set b := Module.finBasis ℂ V with hb
  set M := LinearMap.BilinForm.toMatrix b B with hM
  -- Nondegeneracy is literally the hypothesis, so `det M ≠ 0`.
  have hnd : LinearMap.BilinForm.Nondegenerate B := by
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    exact hnondeg m (fun w => by rw [hm]; simp)
  have hdet_ne : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  -- Skew-symmetry of `B` makes `M` skew-symmetric.
  have htrans : M.transpose = -M := by
    ext i j
    simp only [hM, Matrix.transpose_apply, Matrix.neg_apply, LinearMap.BilinForm.toMatrix_apply]
    exact hskew (b j) (b i)
  -- `det M = (-1)ⁿ det M`, and `n` odd forces `det M = 0`.
  have h1 : M.det = (-1) ^ Module.finrank ℂ V * M.det := by
    conv_lhs => rw [← Matrix.det_transpose M, htrans, Matrix.det_neg]
    simp [Fintype.card_fin]
  rw [hne.neg_one_pow] at h1
  exact hdet_ne (by linear_combination (1 / 2 : ℂ) * h1)

/-- **L3 — quaternionic ⟹ even-dimensional.** A representation of quaternionic
type is even-dimensional. So an **odd-dimensional** representation cannot be of
quaternionic type: together with L2 (`odd dim + real character ⇒ FS ≠ 0`) this is
the "odd dim + real character ⇒ real type" half of the classification. -/
theorem even_finrank_of_isQuaternionicType
    (ρ : Representation ℂ G V) (h : Etingof.IsQuaternionicType ρ) :
    Even (Module.finrank ℂ V) := by
  obtain ⟨B, hskew, hnondeg, _⟩ := h
  refine even_finrank_of_nondegenerate_alternating B (fun v => ?_) hnondeg
  -- `B v v = -(B v v)` in characteristic `0` forces `B v v = 0`.
  have e : B v v = -(B v v) := hskew v v
  have h2 : (2 : ℂ) * B v v = 0 := by linear_combination e
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

end Etingof
