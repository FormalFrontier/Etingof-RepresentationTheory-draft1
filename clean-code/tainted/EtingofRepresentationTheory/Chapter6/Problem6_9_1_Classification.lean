import EtingofRepresentationTheory.Chapter6.Problem6_9_1

/-!
# Problem 6.9.1: isomorphism-level exhaustiveness

This file completes the step deliberately separated from the dimension-vector
argument in `Problem6_9_1.lean`: it constructs compatible Jordan-chain bases and
uses them to produce isomorphisms with the four stated normal forms.
-/

/-- A single Jordan chain for the off-diagonal operator, with a homogeneous
generator.  Homogeneity is precisely what makes the chain split into bases at
the two vertices. -/
structure Q₂Rep.PureChainBasis (ρ : Q₂Rep ℂ) where
  length : ℕ
  length_pos : 0 < length
  head : ρ.V × ρ.W
  head_pure : head.1 = 0 ∨ head.2 = 0
  killed : (ρ.chainOperator ^ length) head = 0
  basis : Module.Basis (Fin length) ℂ (ρ.V × ρ.W)
  basis_apply : ∀ i, basis i = (ρ.chainOperator ^ (i : ℕ)) head

/-- A Jordan-chain basis whose chain generators are homogeneous for
`V ⊕ W`.  This is the literal compatible-basis object requested in Problem
6.9.1(c), including representations with more than one chain. -/
structure Q₂Rep.CompatibleChainBasis (ρ : Q₂Rep ℂ) where
  ι : Type
  [instFintype : Fintype ι]
  length : ι → ℕ
  length_pos : ∀ i, 0 < length i
  head : ι → ρ.V × ρ.W
  head_pure : ∀ i, (head i).1 = 0 ∨ (head i).2 = 0
  killed : ∀ i, (ρ.chainOperator ^ length i) (head i) = 0
  basis : Module.Basis (Σ i, Fin (length i)) ℂ (ρ.V × ρ.W)
  basis_apply : ∀ i,
    basis i = (ρ.chainOperator ^ (i.2 : ℕ)) (head i.1)

/-- Regard a one-chain basis as a compatible chain decomposition. -/
noncomputable def Q₂Rep.PureChainBasis.toCompatible {ρ : Q₂Rep ℂ}
    (c : ρ.PureChainBasis) : ρ.CompatibleChainBasis where
  ι := PUnit
  length := fun _ => c.length
  length_pos := fun _ => c.length_pos
  head := fun _ => c.head
  head_pure := fun _ => c.head_pure
  killed := fun _ => c.killed
  basis := c.basis.reindex
    (Equiv.uniqueSigma (fun _ : PUnit => Fin c.length)).symm
  basis_apply := by
    rintro ⟨i, j⟩
    rw [Module.Basis.reindex_apply, c.basis_apply]
    rfl

attribute [instance] Q₂Rep.CompatibleChainBasis.instFintype

/-- The zero representation has the empty compatible family of chains. -/
noncomputable def Q₂Rep.CompatibleChainBasis.empty (ρ : Q₂Rep ℂ)
    [Subsingleton ρ.V] [Subsingleton ρ.W] : ρ.CompatibleChainBasis where
  ι := PEmpty
  length := PEmpty.elim
  length_pos := fun i => i.elim
  head := PEmpty.elim
  head_pure := fun i => i.elim
  killed := fun i => i.elim
  basis := Module.Basis.empty (ρ.V × ρ.W)
  basis_apply := by rintro ⟨i, _⟩; exact i.elim

/-- Restrict a quiver representation to a pair of arrow-stable subspaces. -/
noncomputable abbrev Q₂Rep.restrict (ρ : Q₂Rep ℂ) (V' : Submodule ℂ ρ.V)
    (W' : Submodule ℂ ρ.W)
    (hA : ∀ v ∈ V', ρ.A v ∈ W') (hB : ∀ w ∈ W', ρ.B w ∈ V') :
    Q₂Rep ℂ where
  V := V'
  W := W'
  A := (ρ.A.domRestrict V').codRestrict W' (fun v => hA v v.2)
  B := (ρ.B.domRestrict W').codRestrict V' (fun w => hB w w.2)

lemma Q₂Rep.restrict_A_coe (ρ : Q₂Rep ℂ)
    (V' : Submodule ℂ ρ.V) (W' : Submodule ℂ ρ.W)
    (hA : ∀ v ∈ V', ρ.A v ∈ W') (hB : ∀ w ∈ W', ρ.B w ∈ V')
    (v : V') :
    ((ρ.restrict V' W' hA hB).A v : ρ.W) = ρ.A v := rfl

lemma Q₂Rep.restrict_B_coe (ρ : Q₂Rep ℂ)
    (V' : Submodule ℂ ρ.V) (W' : Submodule ℂ ρ.W)
    (hA : ∀ v ∈ V', ρ.A v ∈ W') (hB : ∀ w ∈ W', ρ.B w ∈ V')
    (w : W') :
    ((ρ.restrict V' W' hA hB).B w : ρ.V) = ρ.B w := rfl

/-- Inclusion of a stable restricted representation intertwines the chain
operator and all of its powers. -/
lemma Q₂Rep.restrict_chainOperator_coe (ρ : Q₂Rep ℂ)
    (V' : Submodule ℂ ρ.V) (W' : Submodule ℂ ρ.W)
    (hA : ∀ v ∈ V', ρ.A v ∈ W') (hB : ∀ w ∈ W', ρ.B w ∈ V')
    (x : V' × W') :
    ((ρ.restrict V' W' hA hB).chainOperator x).map V'.subtype W'.subtype =
      ρ.chainOperator (x.map V'.subtype W'.subtype) := by
  rcases x with ⟨v, w⟩
  rw [(ρ.restrict V' W' hA hB).chainOperator_apply, ρ.chainOperator_apply]
  rfl

lemma Q₂Rep.restrict_chainOperator_pow_coe (ρ : Q₂Rep ℂ)
    (V' : Submodule ℂ ρ.V) (W' : Submodule ℂ ρ.W)
    (hA : ∀ v ∈ V', ρ.A v ∈ W') (hB : ∀ w ∈ W', ρ.B w ∈ V')
    (j : ℕ) (x : V' × W') :
    (((ρ.restrict V' W' hA hB).chainOperator ^ j) x).map
        ((V'.subtype : V' →ₗ[ℂ] ρ.V)) ((W'.subtype : W' →ₗ[ℂ] ρ.W)) =
      (ρ.chainOperator ^ j) (x.map V'.subtype W'.subtype) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      rw [ρ.restrict_chainOperator_coe V' W' hA hB]
      exact congrArg ρ.chainOperator ih

/-- Inclusion of a stable restricted representation intertwines `AB` and all
of its powers. -/
lemma Q₂Rep.restrict_AB_pow_coe (ρ : Q₂Rep ℂ)
    (V' : Submodule ℂ ρ.V) (W' : Submodule ℂ ρ.W)
    (hA : ∀ v ∈ V', ρ.A v ∈ W') (hB : ∀ w ∈ W', ρ.B w ∈ V')
    (j : ℕ) (w : W') :
    ((((ρ.restrict V' W' hA hB).A.comp
        (ρ.restrict V' W' hA hB).B) ^ j) w : W') =
      ((ρ.A.comp ρ.B) ^ j) (w : ρ.W) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.comp_apply, LinearMap.comp_apply]
      change ρ.A (ρ.B (↑((((ρ.restrict V' W' hA hB).A.comp
        (ρ.restrict V' W' hA hB).B) ^ j) w : W'))) = _
      rw [ih]

/-- Nilpotence of `AB` descends to every stable restricted representation. -/
lemma Q₂Rep.restrict_AB_isNilpotent (ρ : Q₂Rep ℂ)
    (V' : Submodule ℂ ρ.V) (W' : Submodule ℂ ρ.W)
    (hA : ∀ v ∈ V', ρ.A v ∈ W') (hB : ∀ w ∈ W', ρ.B w ∈ V')
    (hAB : IsNilpotent (ρ.A.comp ρ.B)) :
    IsNilpotent ((ρ.restrict V' W' hA hB).A.comp
      (ρ.restrict V' W' hA hB).B) := by
  obtain ⟨n, hn⟩ := hAB
  refine ⟨n, LinearMap.ext fun w => Subtype.ext ?_⟩
  rw [ρ.restrict_AB_pow_coe V' W' hA hB, LinearMap.congr_fun hn]
  rfl

/-- An explicit split embedding of quiver representations.  The retractions
commute with both arrows, so its image is a direct summand as a representation,
not merely as a pair of vector spaces. -/
structure Q₂Rep.SplitEmbedding (τ ρ : Q₂Rep ℂ) where
  iV : τ.V →ₗ[ℂ] ρ.V
  pV : ρ.V →ₗ[ℂ] τ.V
  iW : τ.W →ₗ[ℂ] ρ.W
  pW : ρ.W →ₗ[ℂ] τ.W
  retract_V : ∀ v, pV (iV v) = v
  retract_W : ∀ w, pW (iW w) = w
  map_A_i : ∀ v, iW (τ.A v) = ρ.A (iV v)
  map_B_i : ∀ w, iV (τ.B w) = ρ.B (iW w)
  map_A_p : ∀ v, pW (ρ.A v) = τ.A (pV v)
  map_B_p : ∀ w, pV (ρ.B w) = τ.B (pW w)

/-- The identity split embedding. -/
def Q₂Rep.SplitEmbedding.refl (ρ : Q₂Rep ℂ) : ρ.SplitEmbedding ρ where
  iV := LinearMap.id
  pV := LinearMap.id
  iW := LinearMap.id
  pW := LinearMap.id
  retract_V := fun _ => rfl
  retract_W := fun _ => rfl
  map_A_i := fun _ => rfl
  map_B_i := fun _ => rfl
  map_A_p := fun _ => rfl
  map_B_p := fun _ => rfl

/-- Split embeddings compose, expressing transitivity of being a direct
summand. -/
def Q₂Rep.SplitEmbedding.trans {τ σ ρ : Q₂Rep ℂ}
    (e : τ.SplitEmbedding σ) (f : σ.SplitEmbedding ρ) :
    τ.SplitEmbedding ρ where
  iV := f.iV.comp e.iV
  pV := e.pV.comp f.pV
  iW := f.iW.comp e.iW
  pW := e.pW.comp f.pW
  retract_V := fun v => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.retract_V, e.retract_V]
  retract_W := fun w => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.retract_W, e.retract_W]
  map_A_i := fun v => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    e.map_A_i, f.map_A_i]
  map_B_i := fun w => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    e.map_B_i, f.map_B_i]
  map_A_p := fun v => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.map_A_p, e.map_A_p]
  map_B_p := fun w => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.map_B_p, e.map_B_p]

/-- A compatible complementary pair makes either restricted representation an
explicit direct summand. -/
noncomputable def Q₂Rep.restrictSplitEmbedding (ρ : Q₂Rep ℂ)
    (pV qV : Submodule ℂ ρ.V) (pW qW : Submodule ℂ ρ.W)
    (hcV : IsCompl pV qV) (hcW : IsCompl pW qW)
    (hApV : ∀ v ∈ pV, ρ.A v ∈ pW) (hAqV : ∀ v ∈ qV, ρ.A v ∈ qW)
    (hBpW : ∀ w ∈ pW, ρ.B w ∈ pV) (hBqW : ∀ w ∈ qW, ρ.B w ∈ qV) :
    (ρ.restrict pV pW hApV hBpW).SplitEmbedding ρ where
  iV := pV.subtype
  pV := pV.projectionOnto qV hcV
  iW := pW.subtype
  pW := pW.projectionOnto qW hcW
  retract_V := Submodule.projectionOnto_apply_left hcV
  retract_W := Submodule.projectionOnto_apply_left hcW
  map_A_i := fun _ => rfl
  map_B_i := fun _ => rfl
  map_A_p := by
    intro v
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show v ∈ pV ⊔ qV by rw [hcV.sup_eq_top]; exact Submodule.mem_top)
    rw [← hab, map_add, map_add, map_add, map_add,
      Submodule.projectionOnto_apply_of_mem_left hcV ha,
      Submodule.projectionOnto_apply_of_mem_right hcV hb,
      Submodule.projectionOnto_apply_of_mem_left hcW (hApV a ha),
      Submodule.projectionOnto_apply_of_mem_right hcW (hAqV b hb),
      add_zero, map_zero]
    rw [add_zero]
    apply Subtype.ext
    rfl
  map_B_p := by
    intro w
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show w ∈ pW ⊔ qW by rw [hcW.sup_eq_top]; exact Submodule.mem_top)
    rw [← hab, map_add, map_add, map_add, map_add,
      Submodule.projectionOnto_apply_of_mem_left hcW ha,
      Submodule.projectionOnto_apply_of_mem_right hcW hb,
      Submodule.projectionOnto_apply_of_mem_left hcV (hBpW a ha),
      Submodule.projectionOnto_apply_of_mem_right hcV (hBqW b hb),
      add_zero, map_zero]
    rw [add_zero]
    apply Subtype.ext
    rfl

/-- If both complementary restricted `AB` operators are nilpotent, then so is
the original `AB`. -/
lemma Q₂Rep.AB_isNilpotent_of_isCompl (ρ : Q₂Rep ℂ)
    (pV qV : Submodule ℂ ρ.V) (pW qW : Submodule ℂ ρ.W)
    (hcW : IsCompl pW qW)
    (hApV : ∀ v ∈ pV, ρ.A v ∈ pW) (hAqV : ∀ v ∈ qV, ρ.A v ∈ qW)
    (hBpW : ∀ w ∈ pW, ρ.B w ∈ pV) (hBqW : ∀ w ∈ qW, ρ.B w ∈ qV)
    (hp : IsNilpotent ((ρ.restrict pV pW hApV hBpW).A.comp
      (ρ.restrict pV pW hApV hBpW).B))
    (hq : IsNilpotent ((ρ.restrict qV qW hAqV hBqW).A.comp
      (ρ.restrict qV qW hAqV hBqW).B)) :
    IsNilpotent (ρ.A.comp ρ.B) := by
  obtain ⟨m, hm⟩ := hp
  obtain ⟨n, hn⟩ := hq
  refine ⟨m + n, LinearMap.ext fun w => ?_⟩
  let z := (Submodule.prodEquivOfIsCompl pW qW hcW).symm w
  have hw : (z.1 : ρ.W) + (z.2 : ρ.W) = w := by
    simpa [z] using (Submodule.prodEquivOfIsCompl pW qW hcW).apply_symm_apply w
  rw [← hw, map_add]
  have hp0 : ((ρ.A.comp ρ.B) ^ (m + n)) (z.1 : ρ.W) = 0 := by
    rw [← ρ.restrict_AB_pow_coe pV pW hApV hBpW]
    rw [pow_add, hm]
    rfl
  have hq0 : ((ρ.A.comp ρ.B) ^ (m + n)) (z.2 : ρ.W) = 0 := by
    rw [Nat.add_comm, ← ρ.restrict_AB_pow_coe qV qW hAqV hBqW]
    rw [pow_add, hn]
    rfl
  rw [hp0, hq0]
  simp

/-- Combine compatible chain bases on two complementary subrepresentations. -/
noncomputable def Q₂Rep.CompatibleChainBasis.ofIsCompl
    {ρ : Q₂Rep ℂ} {pV qV : Submodule ℂ ρ.V} {pW qW : Submodule ℂ ρ.W}
    (hcV : IsCompl pV qV) (hcW : IsCompl pW qW)
    (hApV : ∀ v ∈ pV, ρ.A v ∈ pW) (hAqV : ∀ v ∈ qV, ρ.A v ∈ qW)
    (hBpW : ∀ w ∈ pW, ρ.B w ∈ pV) (hBqW : ∀ w ∈ qW, ρ.B w ∈ qV)
    (cp : (ρ.restrict pV pW hApV hBpW).CompatibleChainBasis)
    (cq : (ρ.restrict qV qW hAqV hBqW).CompatibleChainBasis) :
    ρ.CompatibleChainBasis := by
  classical
  letI : Fintype cp.ι := cp.instFintype
  letI : Fintype cq.ι := cq.instFintype
  let length : cp.ι ⊕ cq.ι → ℕ := Sum.elim cp.length cq.length
  let head : cp.ι ⊕ cq.ι → ρ.V × ρ.W := fun i => match i with
    | Sum.inl i => (cp.head i).map pV.subtype pW.subtype
    | Sum.inr i => (cq.head i).map qV.subtype qW.subtype
  let shuffle : ((pV × pW) × (qV × qW)) ≃ₗ[ℂ]
      ((pV × qV) × (pW × qW)) :=
    { toFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
      invFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let total : ((pV × pW) × (qV × qW)) ≃ₗ[ℂ] (ρ.V × ρ.W) :=
    shuffle.trans ((Submodule.prodEquivOfIsCompl pV qV hcV).prodCongr
      (Submodule.prodEquivOfIsCompl pW qW hcW))
  let indexEquiv :
      ((Σ i, Fin (cp.length i)) ⊕ (Σ i, Fin (cq.length i))) ≃
        (Σ i, Fin (length i)) :=
    { toFun := Sum.elim (fun x => ⟨Sum.inl x.1, x.2⟩)
        (fun x => ⟨Sum.inr x.1, x.2⟩)
      invFun := fun x => match x with
        | ⟨Sum.inl i, j⟩ => Sum.inl ⟨i, j⟩
        | ⟨Sum.inr i, j⟩ => Sum.inr ⟨i, j⟩
      left_inv := by rintro (⟨i, j⟩ | ⟨i, j⟩) <;> rfl
      right_inv := by rintro ⟨i | i, j⟩ <;> rfl }
  let b : Module.Basis (Σ i, Fin (length i)) ℂ (ρ.V × ρ.W) :=
    ((cp.basis.prod cq.basis).map total).reindex indexEquiv
  refine {
    ι := cp.ι ⊕ cq.ι
    length := length
    length_pos := ?_
    head := head
    head_pure := ?_
    killed := ?_
    basis := b
    basis_apply := ?_ }
  · rintro (i | i)
    · exact cp.length_pos i
    · exact cq.length_pos i
  · rintro (i | i)
    · simpa [head] using cp.head_pure i
    · simpa [head] using cq.head_pure i
  · rintro (i | i)
    · change (ρ.chainOperator ^ cp.length i)
        ((cp.head i).map pV.subtype pW.subtype) = 0
      calc
        _ = (((ρ.restrict pV pW hApV hBpW).chainOperator ^ cp.length i)
              (cp.head i)).map pV.subtype pW.subtype :=
          (ρ.restrict_chainOperator_pow_coe pV pW hApV hBpW _ _).symm
        _ = 0 := by rw [cp.killed]; rfl
    · change (ρ.chainOperator ^ cq.length i)
        ((cq.head i).map qV.subtype qW.subtype) = 0
      calc
        _ = (((ρ.restrict qV qW hAqV hBqW).chainOperator ^ cq.length i)
              (cq.head i)).map qV.subtype qW.subtype :=
          (ρ.restrict_chainOperator_pow_coe qV qW hAqV hBqW _ _).symm
        _ = 0 := by rw [cq.killed]; rfl
  · rintro ⟨i | i, j⟩
    · rw [show b ⟨Sum.inl i, j⟩ = total (cp.basis ⟨i, j⟩, 0) by
        simp [b, indexEquiv, Module.Basis.prod_apply]]
      rw [cp.basis_apply]
      rw [show total
          (((ρ.restrict pV pW hApV hBpW).chainOperator ^ (j : ℕ)) (cp.head i), 0) =
          (((ρ.restrict pV pW hApV hBpW).chainOperator ^ (j : ℕ))
            (cp.head i)).map pV.subtype pW.subtype by
        change
          (Submodule.prodEquivOfIsCompl pV qV hcV
              ((((ρ.restrict pV pW hApV hBpW).chainOperator ^ (j : ℕ))
                (cp.head i)).1, (0 : qV)),
            Submodule.prodEquivOfIsCompl pW qW hcW
              ((((ρ.restrict pV pW hApV hBpW).chainOperator ^ (j : ℕ))
                (cp.head i)).2, (0 : qW))) = _
        simp only [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero, Prod.map]
        rfl]
      change _ = (ρ.chainOperator ^ (j : ℕ))
        ((cp.head i).map pV.subtype pW.subtype)
      exact ρ.restrict_chainOperator_pow_coe pV pW hApV hBpW (j : ℕ) (cp.head i)
    · rw [show b ⟨Sum.inr i, j⟩ = total (0, cq.basis ⟨i, j⟩) by
        simp [b, indexEquiv, Module.Basis.prod_apply]]
      rw [cq.basis_apply]
      rw [show total
          (0, ((ρ.restrict qV qW hAqV hBqW).chainOperator ^ (j : ℕ)) (cq.head i)) =
          (((ρ.restrict qV qW hAqV hBqW).chainOperator ^ (j : ℕ))
            (cq.head i)).map qV.subtype qW.subtype by
        change
          (Submodule.prodEquivOfIsCompl pV qV hcV
              ((0 : pV), (((ρ.restrict qV qW hAqV hBqW).chainOperator ^ (j : ℕ))
                (cq.head i)).1),
            Submodule.prodEquivOfIsCompl pW qW hcW
              ((0 : pW), (((ρ.restrict qV qW hAqV hBqW).chainOperator ^ (j : ℕ))
                (cq.head i)).2)) = _
        simp only [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, zero_add, Prod.map]
        rfl]
      change _ = (ρ.chainOperator ^ (j : ℕ))
        ((cq.head i).map qV.subtype qW.subtype)
      exact ρ.restrict_chainOperator_pow_coe qV qW hAqV hBqW (j : ℕ) (cq.head i)

/-- A polynomial-module equivalence intertwining two evaluated operators also
intertwines their underlying linear operators and all their powers. -/
private lemma aeval_equiv_pow_intertwines
    {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    (S : Module.End ℂ M) (T : Module.End ℂ N)
    (e : Module.AEval' S ≃ₗ[Polynomial ℂ] Module.AEval' T)
    (j : ℕ) (x : M) :
    (Module.AEval'.of T).symm
        (e (Module.AEval'.of S ((S ^ j) x))) =
      (T ^ j) ((Module.AEval'.of T).symm (e (Module.AEval'.of S x))) := by
  have hST (y : M) :
      (Module.AEval'.of T).symm (e (Module.AEval'.of S (S y))) =
        T ((Module.AEval'.of T).symm (e (Module.AEval'.of S y))) := by
    apply (Module.AEval'.of T).injective
    rw [(Module.AEval'.of T).apply_symm_apply]
    rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, e.map_smul]
    simp
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      rw [ih (x := S x), hST]

/-- A nilpotent chain operator with one-dimensional kernel is a single
compatible Jordan chain. -/
theorem Etingof.Problem6_9_1c_exists_pureChainBasis_of_ker_finrank_eq_one
    (ρ : Q₂Rep ℂ) (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hker : Module.finrank ℂ (LinearMap.ker ρ.chainOperator) = 1) :
    Nonempty ρ.PureChainBasis := by
  classical
  let T := ρ.chainOperator
  have hT : IsNilpotent T := Etingof.Problem6_9_1c ρ hAB
  have hindecomp : Etingof.IsIndecomposable (Polynomial ℂ) (Module.AEval' T) :=
    Etingof.nilpotent_aeval_indecomposable_of_ker_finrank_eq_one T hT hker
  obtain ⟨lam, n, hn, ⟨e⟩⟩ :=
    Etingof.Example_2_3_14.exists_equiv_jordanRep
      (k := ℂ) (M := Module.AEval' T) hindecomp
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let ofT := Module.AEval'.of (R := ℂ) T
  let J := Etingof.Example_2_3_14.jordanBlock lam n
  let ofJ := Module.AEval'.of (R := ℂ) J
  have hlam : lam = 0 := by
    obtain ⟨m, hm⟩ := hT
    let y := e.symm (ofJ (Etingof.Example_2_3_14.e0 n))
    have hy : (Polynomial.X ^ m : Polynomial ℂ) • y = 0 := by
      let z := ofT.symm y
      rw [show y = ofT z by simp [z]]
      change ofT (Polynomial.aeval T (Polynomial.X ^ m) z) = 0
      rw [map_pow, Polynomial.aeval_X, hm]
      simp
    have hy' := congrArg e hy
    rw [map_smul, e.apply_symm_apply, map_zero] at hy'
    change ofJ (Polynomial.aeval J (Polynomial.X ^ m)
      (Etingof.Example_2_3_14.e0 n)) = 0 at hy'
    rw [map_pow, Polynomial.aeval_X] at hy'
    have hJpow : (J ^ m) (Etingof.Example_2_3_14.e0 n) = 0 :=
      ofJ.injective (by simpa using hy')
    have heigen : ∀ r : ℕ, (J ^ r) (Etingof.Example_2_3_14.e0 n) =
        lam ^ r • (Etingof.Example_2_3_14.e0 n : Fin n → ℂ) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          rw [pow_succ', Module.End.mul_apply, ih, map_smul]
          rw [Etingof.Example_2_3_14.jordanBlock_e0, smul_smul, pow_succ']
          simp [mul_comm]
    rw [heigen] at hJpow
    by_contra hne
    exact (pow_ne_zero m hne)
      ((smul_eq_zero.mp hJpow).resolve_right
        (Etingof.Example_2_3_14.e0_ne_zero n))
  subst lam
  change Module.AEval' T ≃ₗ[Polynomial ℂ]
    Etingof.Example_2_3_14.jordanRep 0 n at e
  let F : (ρ.V × ρ.W) ≃ₗ[ℂ] (Fin n → ℂ) :=
    ofT.trans ((e.restrictScalars ℂ).trans ofJ.symm)
  have hJ : J = Etingof.Example_2_3_14.shift n := by
    simp [J, Etingof.Example_2_3_14.jordanBlock]
  have hFpow (j : ℕ) (x : ρ.V × ρ.W) :
      F ((T ^ j) x) = (Etingof.Example_2_3_14.shift n ^ j) (F x) := by
    change ofJ.symm (e (ofT ((T ^ j) x))) =
      (Etingof.Example_2_3_14.shift n ^ j) (ofJ.symm (e (ofT x)))
    have hh := aeval_equiv_pow_intertwines T J
      (show Module.AEval' T ≃ₗ[Polynomial ℂ] Module.AEval' J from e) j x
    calc
      ofJ.symm (e (ofT ((T ^ j) x))) = (J ^ j) (ofJ.symm (e (ofT x))) := hh
      _ = (Etingof.Example_2_3_14.shift n ^ j) (ofJ.symm (e (ofT x))) := by rw [hJ]
  have hdim : Module.finrank ℂ (ρ.V × ρ.W) = n := by
    calc
      Module.finrank ℂ (ρ.V × ρ.W) = Module.finrank ℂ (Fin n → ℂ) := F.finrank_eq
      _ = n := by simp
  let g := F.symm (Etingof.Example_2_3_14.eTop n)
  have hgmax : (T ^ (n - 1)) g ≠ 0 := by
    intro h
    have h' := congrArg F h
    rw [hFpow, map_zero, F.apply_symm_apply,
      Etingof.Example_2_3_14.shift_pow_eTop n (by omega)] at h'
    apply Etingof.Example_2_3_14.e0_ne_zero (k := ℂ) n
    have hindex : (⟨n - 1 - (n - 1), by omega⟩ : Fin n) = 0 := by
      apply Fin.ext
      simp
    rw [hindex] at h'
    exact h'
  rcases g with ⟨v, w⟩
  have hpure : (T ^ (n - 1)) (v, (0 : ρ.W)) ≠ 0 ∨
      (T ^ (n - 1)) ((0 : ρ.V), w) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨hv0, hw0⟩ := h
    apply hgmax
    rw [show (v, w) = (v, (0 : ρ.W)) + ((0 : ρ.V), w) by simp,
      map_add, hv0, hw0, add_zero]
  obtain ⟨p, hpmax, hppure⟩ : ∃ p : ρ.V × ρ.W,
      (T ^ (n - 1)) p ≠ 0 ∧ (p.1 = 0 ∨ p.2 = 0) := by
    rcases hpure with hv | hw
    · exact ⟨(v, 0), hv, Or.inr rfl⟩
    · exact ⟨(0, w), hw, Or.inl rfl⟩
  let q := F p
  have hqmax : (Etingof.Example_2_3_14.shift n ^ (n - 1)) q ≠ 0 := by
    simpa [q, hFpow] using F.injective.ne hpmax
  have hqlast : q ⟨n - 1, by omega⟩ ≠ 0 := by
    intro hlast
    apply hqmax
    funext i
    rw [Etingof.Example_2_3_14.shift_pow_apply]
    split_ifs with hi
    · have hval : (i : ℕ) + (n - 1) = n - 1 := by omega
      have hidx : (⟨(i : ℕ) + (n - 1), hi⟩ : Fin n) =
          ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        exact hval
      rw [hidx, hlast]
      rfl
    · rfl
  have hliQ : LinearIndependent ℂ (fun i : Fin n =>
      (Etingof.Example_2_3_14.shift n ^ (i : ℕ)) q) :=
    Etingof.shift_powers_linearIndependent_of_last_ne n hn q hqlast
  have hli : LinearIndependent ℂ (fun i : Fin n => (T ^ (i : ℕ)) p) := by
    apply LinearIndependent.of_comp F.toLinearMap
    convert hliQ using 1
    funext i
    exact hFpow (i : ℕ) p
  let b : Module.Basis (Fin n) ℂ (ρ.V × ρ.W) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])
  have hb (i : Fin n) : b i = (T ^ (i : ℕ)) p := by
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])) i
  have hkill : (T ^ n) p = 0 := by
    apply F.injective
    rw [hFpow, map_zero, Etingof.Example_2_3_14.shift_pow_self]
    rfl
  exact ⟨{
    length := n
    length_pos := hn
    head := p
    head_pure := hppure
    killed := hkill
    basis := b
    basis_apply := hb }⟩

/-- In the nondegenerate indecomposable nilpotent case, the compatible basis
has one chain. -/
theorem Etingof.Problem6_9_1c_exists_pureChainBasis (ρ : Q₂Rep ℂ)
    (hρ : ρ.Indecomposable) (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV : 0 < Module.finrank ℂ ρ.V) (hW : 0 < Module.finrank ℂ ρ.W) :
    Nonempty ρ.PureChainBasis :=
  Etingof.Problem6_9_1c_exists_pureChainBasis_of_ker_finrank_eq_one ρ hAB
    (Etingof.Problem6_9_1c_chainOperator_ker_finrank ρ hρ hAB hV hW)

/-- **Problem 6.9.1(c), literal compatible-chain statement.** Whenever `AB`
is nilpotent, `V ⊕ W` has a basis partitioned into nilpotent `X`-chains, and
the generator of every chain lies entirely in one vertex. -/
theorem Etingof.Problem6_9_1c_exists_compatibleChainBasis (ρ : Q₂Rep ℂ)
    (hAB : IsNilpotent (ρ.A.comp ρ.B)) :
    Nonempty ρ.CompatibleChainBasis := by
  classical
  suffices h : ∀ d : ℕ, ∀ σ : Q₂Rep ℂ,
      Module.finrank ℂ σ.V + Module.finrank ℂ σ.W = d →
      IsNilpotent (σ.A.comp σ.B) → Nonempty σ.CompatibleChainBasis by
    exact h _ ρ rfl hAB
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro σ hdim hABσ
      by_cases hd0 : d = 0
      · have hV0 : Module.finrank ℂ σ.V = 0 := by omega
        have hW0 : Module.finrank ℂ σ.W = 0 := by omega
        letI : Subsingleton σ.V := Module.finrank_zero_iff.mp hV0
        letI : Subsingleton σ.W := Module.finrank_zero_iff.mp hW0
        exact ⟨Q₂Rep.CompatibleChainBasis.empty σ⟩
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hprodpos : 0 < Module.finrank ℂ (σ.V × σ.W) := by
          rw [Module.finrank_prod, hdim]
          exact hdpos
        letI : Nontrivial (σ.V × σ.W) := Module.finrank_pos_iff.mp hprodpos
        have hX : IsNilpotent σ.chainOperator := Etingof.Problem6_9_1c σ hABσ
        obtain ⟨x, hxne, hx0⟩ :=
          Etingof.Example_2_3_14.exists_mem_ker_of_isNilpotent σ.chainOperator hX
        have hxmem : x ∈ LinearMap.ker σ.chainOperator := LinearMap.mem_ker.mpr hx0
        have hkerne : Module.finrank ℂ (LinearMap.ker σ.chainOperator) ≠ 0 := by
          intro hzero
          have hbot : LinearMap.ker σ.chainOperator = ⊥ :=
            Submodule.finrank_eq_zero.mp hzero
          apply hxne
          exact (Submodule.mem_bot ℂ).mp (hbot ▸ hxmem)
        have hkerpos : 0 < Module.finrank ℂ (LinearMap.ker σ.chainOperator) :=
          Nat.pos_of_ne_zero hkerne
        by_cases hker1 : Module.finrank ℂ (LinearMap.ker σ.chainOperator) = 1
        · obtain ⟨c⟩ :=
            Etingof.Problem6_9_1c_exists_pureChainBasis_of_ker_finrank_eq_one
              σ hABσ hker1
          exact ⟨c.toCompatible⟩
        · have hker2 : 2 ≤ Module.finrank ℂ (LinearMap.ker σ.chainOperator) := by
            omega
          have hkerSum : 2 ≤ Module.finrank ℂ (LinearMap.ker σ.A) +
              Module.finrank ℂ (LinearMap.ker σ.B) := by
            rw [← σ.chainOperator_ker_finrank]
            exact hker2
          obtain ⟨pV, qV, pW, qW, hcV, hcW, hApV, hAqV, hBpW, hBqW,
              hpne, hqne⟩ :=
            off_diagonal_nilpotent_product_decomp σ.A σ.B hABσ hkerSum
          have hdimV : Module.finrank ℂ pV + Module.finrank ℂ qV =
              Module.finrank ℂ σ.V := by
            simpa [Module.finrank_prod] using
              (Submodule.prodEquivOfIsCompl pV qV hcV).finrank_eq
          have hdimW : Module.finrank ℂ pW + Module.finrank ℂ qW =
              Module.finrank ℂ σ.W := by
            simpa [Module.finrank_prod] using
              (Submodule.prodEquivOfIsCompl pW qW hcW).finrank_eq
          have hpdim : 0 < Module.finrank ℂ pV + Module.finrank ℂ pW := by
            by_contra hzero
            apply hpne
            constructor
            · apply Submodule.finrank_eq_zero.mp
              omega
            · apply Submodule.finrank_eq_zero.mp
              omega
          have hqdim : 0 < Module.finrank ℂ qV + Module.finrank ℂ qW := by
            by_contra hzero
            apply hqne
            constructor
            · apply Submodule.finrank_eq_zero.mp
              omega
            · apply Submodule.finrank_eq_zero.mp
              omega
          have hp_lt : Module.finrank ℂ pV + Module.finrank ℂ pW < d := by
            omega
          have hq_lt : Module.finrank ℂ qV + Module.finrank ℂ qW < d := by
            omega
          let σp := σ.restrict pV pW hApV hBpW
          let σq := σ.restrict qV qW hAqV hBqW
          have hABp : IsNilpotent (σp.A.comp σp.B) :=
            σ.restrict_AB_isNilpotent pV pW hApV hBpW hABσ
          have hABq : IsNilpotent (σq.A.comp σq.B) :=
            σ.restrict_AB_isNilpotent qV qW hAqV hBqW hABσ
          obtain ⟨cp⟩ := ih _ hp_lt σp rfl hABp
          obtain ⟨cq⟩ := ih _ hq_lt σq rfl hABq
          exact ⟨Q₂Rep.CompatibleChainBasis.ofIsCompl hcV hcW hApV hAqV
            hBpW hBqW cp cq⟩

private lemma chain_pow_parity_of_snd_zero {ρ : Q₂Rep ℂ} (p : ρ.V × ρ.W)
    (hp : p.2 = 0) (i : ℕ) :
    ((ρ.chainOperator ^ (2 * i)) p).2 = 0 ∧
      ((ρ.chainOperator ^ (2 * i + 1)) p).1 = 0 := by
  induction i with
  | zero =>
      constructor
      · simpa using hp
      · simp [pow_succ', ρ.chainOperator_apply, hp]
  | succ i ih =>
      constructor
      · rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.chainOperator_apply]
        exact map_zero ρ.A ▸ congrArg ρ.A ih.2
      · rw [show 2 * (i + 1) + 1 = (2 * i + 2) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.chainOperator_apply]
        exact map_zero ρ.B ▸ congrArg ρ.B (by
          rw [show 2 * i + 2 = (2 * i + 1) + 1 by omega, pow_succ',
            Module.End.mul_apply, ρ.chainOperator_apply]
          exact map_zero ρ.A ▸ congrArg ρ.A ih.2)

private lemma chain_pow_parity_of_fst_zero {ρ : Q₂Rep ℂ} (p : ρ.V × ρ.W)
    (hp : p.1 = 0) (i : ℕ) :
    ((ρ.chainOperator ^ (2 * i)) p).1 = 0 ∧
      ((ρ.chainOperator ^ (2 * i + 1)) p).2 = 0 := by
  induction i with
  | zero =>
      constructor
      · simpa using hp
      · simp [pow_succ', ρ.chainOperator_apply, hp]
  | succ i ih =>
      constructor
      · rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.chainOperator_apply]
        exact map_zero ρ.B ▸ congrArg ρ.B ih.2
      · rw [show 2 * (i + 1) + 1 = (2 * i + 2) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.chainOperator_apply]
        exact map_zero ρ.A ▸ congrArg ρ.A (by
          rw [show 2 * i + 2 = (2 * i + 1) + 1 by omega, pow_succ',
            Module.End.mul_apply, ρ.chainOperator_apply]
          exact map_zero ρ.B ▸ congrArg ρ.B ih.2)

private lemma Q₂Rep_E_zero_A_basis (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (Etingof.Q₂Rep_E n hn 0).A ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j) =
      if h : j.val + 1 < n then
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis ⟨j.val + 1, h⟩ else 0 := by
  split_ifs with hj
  all_goals
    apply WithLp.ofLp_injective
    funext i
    simp only [Etingof.Q₂Rep_E, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    simp [Fin.ext_iff]
    all_goals omega

private lemma Q₂Rep_H_A_basis (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (Etingof.Q₂Rep_H n hn).A ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j) =
      if h : j.val < n - 1 then
        (EuclideanSpace.basisFun (Fin (n - 1)) ℂ).toBasis ⟨j.val, h⟩ else 0 := by
  split_ifs with hj
  all_goals
    apply WithLp.ofLp_injective
    funext i
    simp only [Etingof.Q₂Rep_H, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    simp [Fin.ext_iff]
    all_goals omega

private lemma Q₂Rep_H_B_basis (n : ℕ) (hn : 0 < n) (j : Fin (n - 1)) :
    (Etingof.Q₂Rep_H n hn).B
        ((EuclideanSpace.basisFun (Fin (n - 1)) ℂ).toBasis j) =
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis ⟨j.val + 1, by omega⟩ := by
  apply WithLp.ofLp_injective
  funext i
  simp only [Etingof.Q₂Rep_H, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp [Fin.ext_iff]

/-- An even-length chain starting at the `V` vertex is `E_{m,∞}`. -/
private theorem pureChain_even_snd_zero_iso {ρ : Q₂Rep ℂ}
    (c : ρ.PureChainBasis) (m : ℕ) (hm : 0 < m) (hlen : c.length = 2 * m)
    (hp : c.head.2 = 0) :
    Nonempty (ρ.Iso (Etingof.Q₂Rep_E_infinity m hm)) := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let vchain : Fin m → ρ.V := fun i =>
    ((ρ.chainOperator ^ (2 * (i : ℕ))) c.head).1
  let wchain : Fin m → ρ.W := fun i =>
    ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head).2
  let evenIndex : Fin m → Fin c.length := fun i => ⟨2 * (i : ℕ), by rw [hlen]; omega⟩
  let oddIndex : Fin m → Fin c.length := fun i => ⟨2 * (i : ℕ) + 1, by rw [hlen]; omega⟩
  have heven_inj : Function.Injective evenIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [evenIndex] at this
    omega
  have hodd_inj : Function.Injective oddIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [oddIndex] at this
    omega
  have hliV : LinearIndependent ℂ vchain := by
    apply LinearIndependent.of_comp (LinearMap.inl ℂ ρ.V ρ.W)
    have hsub := c.basis.linearIndependent.comp evenIndex heven_inj
    convert hsub using 1
    funext i
    change (vchain i, (0 : ρ.W)) = c.basis (evenIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · rfl
    · simpa [evenIndex] using (chain_pow_parity_of_snd_zero c.head hp (i : ℕ)).1.symm
  have hliW : LinearIndependent ℂ wchain := by
    apply LinearIndependent.of_comp (LinearMap.inr ℂ ρ.V ρ.W)
    have hsub := c.basis.linearIndependent.comp oddIndex hodd_inj
    convert hsub using 1
    funext i
    change ((0 : ρ.V), wchain i) = c.basis (oddIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · simpa [oddIndex] using (chain_pow_parity_of_snd_zero c.head hp (i : ℕ)).2.symm
    · rfl
  have hsum : Module.finrank ℂ ρ.V + Module.finrank ℂ ρ.W = 2 * m := by
    rw [← Module.finrank_prod]
    simpa [hlen] using Module.finrank_eq_card_basis c.basis
  have hdimV : Module.finrank ℂ ρ.V = m := by
    have hleV := hliV.fintype_card_le_finrank
    have hleW := hliW.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hleV hleW
    omega
  have hdimW : Module.finrank ℂ ρ.W = m := by omega
  let bV : Module.Basis (Fin m) ℂ ρ.V :=
    basisOfLinearIndependentOfCardEqFinrank hliV (by rw [Fintype.card_fin, hdimV])
  let bW : Module.Basis (Fin m) ℂ ρ.W :=
    basisOfLinearIndependentOfCardEqFinrank hliW (by rw [Fintype.card_fin, hdimW])
  have hbV (i : Fin m) : bV i = vchain i :=
    congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hliV (by rw [Fintype.card_fin, hdimV])) i
  have hbW (i : Fin m) : bW i = wchain i :=
    congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hliW (by rw [Fintype.card_fin, hdimW])) i
  let std := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
  let eV : ρ.V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) := bV.equiv std (Equiv.refl _)
  let eW : ρ.W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) := bW.equiv std (Equiv.refl _)
  have hAchain (i : Fin m) : ρ.A (vchain i) = wchain i := by
    change ρ.A ((ρ.chainOperator ^ (2 * (i : ℕ))) c.head).1 =
      ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head).2
    have hstep : (ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head =
        ρ.chainOperator ((ρ.chainOperator ^ (2 * (i : ℕ))) c.head) := by
      rw [pow_succ', Module.End.mul_apply]
    have hs := congrArg Prod.snd hstep
    rw [ρ.chainOperator_apply] at hs
    exact hs.symm
  have hBchain (i : Fin m) : ρ.B (wchain i) =
      if h : i.val + 1 < m then vchain ⟨i.val + 1, h⟩ else 0 := by
    split_ifs with hi
    · have hstep : (ρ.chainOperator ^ (2 * (i : ℕ) + 2)) c.head =
          ρ.chainOperator ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head) := by
        rw [show 2 * (i : ℕ) + 2 = (2 * (i : ℕ) + 1) + 1 by omega,
          pow_succ', Module.End.mul_apply]
      change ρ.B ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head).2 =
        ((ρ.chainOperator ^ (2 * ((⟨i.val + 1, hi⟩ : Fin m) : ℕ))) c.head).1
      have hs := congrArg Prod.fst hstep
      rw [ρ.chainOperator_apply] at hs
      rw [show 2 * ((⟨i.val + 1, hi⟩ : Fin m) : ℕ) =
        2 * (i : ℕ) + 2 by simp; omega]
      exact hs.symm
    · have hilast : (i : ℕ) = m - 1 := by omega
      have hkill : (ρ.chainOperator ^ (2 * (i : ℕ) + 2)) c.head = 0 := by
        rw [show 2 * (i : ℕ) + 2 = c.length by omega]
        exact c.killed
      have hstep : (ρ.chainOperator ^ (2 * (i : ℕ) + 2)) c.head =
          ρ.chainOperator ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head) := by
        rw [show 2 * (i : ℕ) + 2 = (2 * (i : ℕ) + 1) + 1 by omega,
          pow_succ', Module.End.mul_apply]
      have := congrArg Prod.fst (hstep.symm.trans hkill)
      simpa [ρ.chainOperator_apply] using this
  have hmapA : eW.toLinearMap.comp ρ.A = eV.toLinearMap := by
    apply bV.ext
    intro i
    simp only [LinearMap.comp_apply]
    rw [hbV, hAchain, ← hbW, ← hbV]
    simp [eV, eW, std]
  have hmapB_basis (i : Fin m) : eV (ρ.B (bW i)) =
      (Etingof.Q₂Rep_E m hm 0).A (eW (bW i)) := by
    rw [hbW, hBchain]
    split_ifs with hi
    · rw [← hbV, ← hbW]
      simp only [eV, eW, std, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_E_zero_A_basis m hm i).symm
    · rw [map_zero]
      rw [← hbW]
      simp only [eW, std, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_E_zero_A_basis m hm i).symm
  have hmapB (x : ρ.W) : eV (ρ.B x) =
      (Etingof.Q₂Rep_E m hm 0).A (eW x) := by
    rw [← bW.sum_repr x]
    simp only [map_sum, map_smul]
    simp_rw [hmapB_basis]
  exact ⟨{
    eV := eV
    eW := eW
    map_A := fun x => by
      simpa [Etingof.Q₂Rep_E_infinity, Q₂Rep.swap, Etingof.Q₂Rep_E] using
        LinearMap.congr_fun hmapA x
    map_B := fun x => by
      change eV (ρ.B x) = (Etingof.Q₂Rep_E m hm 0).A (eW x)
      exact hmapB x }⟩

/-- An odd-length chain starting at the `V` vertex is `H_{m+1}`. -/
private theorem pureChain_odd_snd_zero_iso {ρ : Q₂Rep ℂ}
    (c : ρ.PureChainBasis) (m : ℕ) (hlen : c.length = 2 * m + 1)
    (hp : c.head.2 = 0) :
    Nonempty (ρ.Iso (Etingof.Q₂Rep_H (m + 1) (by omega))) := by
  classical
  have hn : 0 < m + 1 := by omega
  let vchain : Fin (m + 1) → ρ.V := fun i =>
    ((ρ.chainOperator ^ (2 * (i : ℕ))) c.head).1
  let wchain : Fin m → ρ.W := fun i =>
    ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head).2
  let evenIndex : Fin (m + 1) → Fin c.length := fun i =>
    ⟨2 * (i : ℕ), by rw [hlen]; omega⟩
  let oddIndex : Fin m → Fin c.length := fun i =>
    ⟨2 * (i : ℕ) + 1, by rw [hlen]; omega⟩
  have heven_inj : Function.Injective evenIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [evenIndex] at this
    omega
  have hodd_inj : Function.Injective oddIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [oddIndex] at this
    omega
  have hliV : LinearIndependent ℂ vchain := by
    apply LinearIndependent.of_comp (LinearMap.inl ℂ ρ.V ρ.W)
    have hsub := c.basis.linearIndependent.comp evenIndex heven_inj
    convert hsub using 1
    funext i
    change (vchain i, (0 : ρ.W)) = c.basis (evenIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · rfl
    · simpa [evenIndex] using (chain_pow_parity_of_snd_zero c.head hp (i : ℕ)).1.symm
  have hliW : LinearIndependent ℂ wchain := by
    apply LinearIndependent.of_comp (LinearMap.inr ℂ ρ.V ρ.W)
    have hsub := c.basis.linearIndependent.comp oddIndex hodd_inj
    convert hsub using 1
    funext i
    change ((0 : ρ.V), wchain i) = c.basis (oddIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · simpa [oddIndex] using (chain_pow_parity_of_snd_zero c.head hp (i : ℕ)).2.symm
    · rfl
  have hsum : Module.finrank ℂ ρ.V + Module.finrank ℂ ρ.W = 2 * m + 1 := by
    rw [← Module.finrank_prod]
    simpa [hlen] using Module.finrank_eq_card_basis c.basis
  have hdimV : Module.finrank ℂ ρ.V = m + 1 := by
    have hleV := hliV.fintype_card_le_finrank
    have hleW := hliW.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hleV hleW
    omega
  have hdimW : Module.finrank ℂ ρ.W = m := by omega
  let bV : Module.Basis (Fin (m + 1)) ℂ ρ.V :=
    basisOfLinearIndependentOfCardEqFinrank' vchain hliV
      (by rw [Fintype.card_fin, hdimV])
  let bW : Module.Basis (Fin m) ℂ ρ.W :=
    basisOfLinearIndependentOfCardEqFinrank' wchain hliW
      (by rw [Fintype.card_fin, hdimW])
  have hbV (i : Fin (m + 1)) : bV i = vchain i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' vchain hliV
      (by rw [Fintype.card_fin, hdimV])) i
  have hbW (i : Fin m) : bW i = wchain i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' wchain hliW
      (by rw [Fintype.card_fin, hdimW])) i
  let stdV := (EuclideanSpace.basisFun (Fin (m + 1)) ℂ).toBasis
  let stdW := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
  let eV : ρ.V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)) := bV.equiv stdV (Equiv.refl _)
  let eW : ρ.W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) := bW.equiv stdW (Equiv.refl _)
  have hAchain (i : Fin (m + 1)) : ρ.A (vchain i) =
      if h : i.val < m then wchain ⟨i.val, h⟩ else 0 := by
    split_ifs with hi
    · change ρ.A ((ρ.chainOperator ^ (2 * (i : ℕ))) c.head).1 =
        ((ρ.chainOperator ^ (2 * ((⟨i.val, hi⟩ : Fin m) : ℕ) + 1)) c.head).2
      have hstep : (ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head =
          ρ.chainOperator ((ρ.chainOperator ^ (2 * (i : ℕ))) c.head) := by
        rw [pow_succ', Module.End.mul_apply]
      have hs := congrArg Prod.snd hstep
      rw [ρ.chainOperator_apply] at hs
      simpa using hs.symm
    · have hilast : (i : ℕ) = m := by omega
      have hkill : (ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head = 0 := by
        rw [show 2 * (i : ℕ) + 1 = c.length by omega]
        exact c.killed
      have hstep : (ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head =
          ρ.chainOperator ((ρ.chainOperator ^ (2 * (i : ℕ))) c.head) := by
        rw [pow_succ', Module.End.mul_apply]
      have hs := congrArg Prod.snd (hstep.symm.trans hkill)
      simpa [ρ.chainOperator_apply] using hs
  have hBchain (i : Fin m) : ρ.B (wchain i) =
      vchain ⟨i.val + 1, by omega⟩ := by
    change ρ.B ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head).2 =
      ((ρ.chainOperator ^ (2 * ((⟨i.val + 1, by omega⟩ : Fin (m + 1)) : ℕ))) c.head).1
    have hstep : (ρ.chainOperator ^ (2 * (i : ℕ) + 2)) c.head =
        ρ.chainOperator ((ρ.chainOperator ^ (2 * (i : ℕ) + 1)) c.head) := by
      rw [show 2 * (i : ℕ) + 2 = (2 * (i : ℕ) + 1) + 1 by omega,
        pow_succ', Module.End.mul_apply]
    have hs := congrArg Prod.fst hstep
    rw [ρ.chainOperator_apply] at hs
    rw [show 2 * ((⟨i.val + 1, by omega⟩ : Fin (m + 1)) : ℕ) =
      2 * (i : ℕ) + 2 by simp; omega]
    exact hs.symm
  have hmapA_basis (i : Fin (m + 1)) : eW (ρ.A (bV i)) =
      (Etingof.Q₂Rep_H (m + 1) hn).A (eV (bV i)) := by
    rw [hbV, hAchain]
    split_ifs with hi
    · rw [← hbW, ← hbV]
      simp only [eV, eW, stdV, stdW, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_H_A_basis (m + 1) hn i).symm
    · rw [map_zero, ← hbV]
      simp only [eV, stdV, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_H_A_basis (m + 1) hn i).symm
  have hmapB_basis (i : Fin m) : eV (ρ.B (bW i)) =
      (Etingof.Q₂Rep_H (m + 1) hn).B (eW (bW i)) := by
    rw [hbW, hBchain, ← hbV, ← hbW]
    simp only [eV, eW, stdV, stdW, Module.Basis.equiv_apply]
    simpa using (Q₂Rep_H_B_basis (m + 1) hn i).symm
  have hmapA (x : ρ.V) : eW (ρ.A x) =
      (Etingof.Q₂Rep_H (m + 1) hn).A (eV x) := by
    rw [← bV.sum_repr x]
    simp only [map_sum, map_smul]
    simp_rw [hmapA_basis]
  have hmapB (x : ρ.W) : eV (ρ.B x) =
      (Etingof.Q₂Rep_H (m + 1) hn).B (eW x) := by
    rw [← bW.sum_repr x]
    simp only [map_sum, map_smul]
    simp_rw [hmapB_basis]
  exact ⟨{
    eV := eV
    eW := eW
    map_A := hmapA
    map_B := hmapB }⟩

/-- Swap an isomorphism together with its two vertex maps. -/
def Q₂Rep.Iso.swap {k : Type*} [Field k] {ρ σ : Q₂Rep k}
    (e : ρ.Iso σ) : ρ.swap.Iso σ.swap where
  eV := e.eW
  eW := e.eV
  map_A := e.map_B
  map_B := e.map_A

private lemma chainOperator_swap_intertwines (ρ : Q₂Rep ℂ) (j : ℕ)
    (x : ρ.V × ρ.W) :
    ((ρ.swap.chainOperator ^ j) ((LinearEquiv.prodComm ℂ ρ.V ρ.W) x)) =
      (LinearEquiv.prodComm ℂ ρ.V ρ.W) ((ρ.chainOperator ^ j) x) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      rcases (ρ.chainOperator ^ j) x with ⟨v, w⟩
      simp only [LinearEquiv.prodComm_apply, Prod.swap_prod_mk]
      rw [ρ.chainOperator_apply, ρ.swap.chainOperator_apply]
      rfl

/-- Swapping the vertices of a pure chain swaps the homogeneous generator and
preserves its length and chain basis. -/
noncomputable def Q₂Rep.PureChainBasis.swap {ρ : Q₂Rep ℂ}
    (c : ρ.PureChainBasis) : ρ.swap.PureChainBasis where
  length := c.length
  length_pos := c.length_pos
  head := (LinearEquiv.prodComm ℂ ρ.V ρ.W) c.head
  head_pure := by simpa using c.head_pure.symm
  killed := by
    rw [chainOperator_swap_intertwines]
    rw [c.killed, map_zero]
  basis := c.basis.map (LinearEquiv.prodComm ℂ ρ.V ρ.W)
  basis_apply := by
    intro i
    rw [Module.Basis.map_apply, c.basis_apply]
    exact (chainOperator_swap_intertwines ρ (i : ℕ) c.head).symm

/-- Swapping twice is canonically the original representation. -/
def Q₂Rep.swapSwapIso {k : Type*} [Field k] (ρ : Q₂Rep k) :
    ρ.swap.swap.Iso ρ where
  eV := LinearEquiv.refl k ρ.V
  eW := LinearEquiv.refl k ρ.W
  map_A := fun _ => rfl
  map_B := fun _ => rfl

/-- An even-length chain starting at `W` is `E_{m,0}`. -/
private theorem pureChain_even_fst_zero_iso {ρ : Q₂Rep ℂ}
    (c : ρ.PureChainBasis) (m : ℕ) (hm : 0 < m) (hlen : c.length = 2 * m)
    (hp : c.head.1 = 0) :
    Nonempty (ρ.Iso (Etingof.Q₂Rep_E m hm 0)) := by
  obtain ⟨e⟩ := pureChain_even_snd_zero_iso c.swap m hm hlen hp
  let f := (Q₂Rep.swapSwapIso ρ).symm.trans e.swap
  exact ⟨by simpa [Etingof.Q₂Rep_E_infinity, Q₂Rep.swap] using f⟩

/-- An odd-length chain starting at `W` is `K_{m+1}`. -/
private theorem pureChain_odd_fst_zero_iso {ρ : Q₂Rep ℂ}
    (c : ρ.PureChainBasis) (m : ℕ) (hlen : c.length = 2 * m + 1)
    (hp : c.head.1 = 0) :
    Nonempty (ρ.Iso (Etingof.Q₂Rep_K (m + 1) (by omega))) := by
  obtain ⟨e⟩ := pureChain_odd_snd_zero_iso c.swap m hlen hp
  let f := (Q₂Rep.swapSwapIso ρ).symm.trans e.swap
  exact ⟨by simpa [Etingof.Q₂Rep_K] using f⟩

/-- A homogeneous single chain is isomorphic to exactly one of the four normal
forms, according to its parity and starting vertex. -/
theorem Etingof.Q₂Rep.PureChainBasis.isClassified {ρ : Q₂Rep ℂ}
    (c : ρ.PureChainBasis) : Etingof.Q₂Rep.IsClassified ρ := by
  obtain ⟨m, hlen | hlen⟩ := c.length.even_or_odd'
  · have hm : 0 < m := by
      have hpos := c.length_pos
      rw [hlen] at hpos
      omega
    rcases c.head_pure with hp | hp
    · refine ⟨Etingof.Q₂Family.finite ⟨m, hm⟩ 0, ?_⟩
      simpa [Etingof.Q₂Family.rep] using pureChain_even_fst_zero_iso c m hm hlen hp
    · refine ⟨Etingof.Q₂Family.infinity ⟨m, hm⟩, ?_⟩
      simpa [Etingof.Q₂Family.rep] using pureChain_even_snd_zero_iso c m hm hlen hp
  · rcases c.head_pure with hp | hp
    · refine ⟨Etingof.Q₂Family.preinjective ⟨m + 1, by omega⟩, ?_⟩
      simpa [Etingof.Q₂Family.rep] using pureChain_odd_fst_zero_iso c m hlen hp
    · refine ⟨Etingof.Q₂Family.preprojective ⟨m + 1, by omega⟩, ?_⟩
      simpa [Etingof.Q₂Family.rep] using pureChain_odd_snd_zero_iso c m hlen hp

/-- In the nonnilpotent Fitting summand of an indecomposable representation,
both arrows are bijective. -/
private lemma nonnilpotent_arrows_bijective (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : ¬IsNilpotent (ρ.A.comp ρ.B)) :
    Function.Bijective ρ.A ∧ Function.Bijective ρ.B := by
  set AB := ρ.A.comp ρ.B
  set BA := ρ.B.comp ρ.A
  set pW := ⨆ n, LinearMap.ker (AB ^ n)
  set qW := ⨅ n, LinearMap.range (AB ^ n)
  set pV := ⨆ n, LinearMap.ker (BA ^ n)
  set qV := ⨅ n, LinearMap.range (BA ^ n)
  have hcV := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow BA
  have hcW := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow AB
  have hApV : ∀ x ∈ pV, ρ.A x ∈ pW := fun x hx => ρ.fitting_A_ker_to_ker x hx
  have hAqV : ∀ x ∈ qV, ρ.A x ∈ qW := fun x hx => ρ.fitting_A_range_to_range x hx
  have hBpW : ∀ x ∈ pW, ρ.B x ∈ pV := fun x hx => ρ.fitting_B_ker_to_ker x hx
  have hBqW : ∀ x ∈ qW, ρ.B x ∈ qV := fun x hx => ρ.fitting_B_range_to_range x hx
  have hqW_ne : qW ≠ ⊥ := by
    intro hq
    apply hAB
    have hpW : pW = ⊤ := eq_top_of_isCompl_bot (hq ▸ hcW)
    have hsup : ⨆ n, LinearMap.ker (AB ^ n) = ⊤ := hpW
    obtain ⟨N, hN⟩ := Filter.Eventually.exists (LinearMap.eventually_iSup_ker_pow_eq AB)
    rw [hsup] at hN
    exact ⟨N, LinearMap.ker_eq_top.mp hN.symm⟩
  rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with hp | hq
  · have hqV : qV = ⊤ := eq_top_of_bot_isCompl (hp.1 ▸ hcV)
    have hqW : qW = ⊤ := eq_top_of_bot_isCompl (hp.2 ▸ hcW)
    have hAinj : Function.Injective ρ.A := by
      intro x y hxy
      apply ρ.fitting_A_injective_on_range
        (show x ∈ qV by rw [hqV]; exact Submodule.mem_top)
        (show y ∈ qV by rw [hqV]; exact Submodule.mem_top) hxy
    have hBinj : Function.Injective ρ.B := by
      intro x y hxy
      apply ρ.fitting_B_injective_on_range
        (show x ∈ qW by rw [hqW]; exact Submodule.mem_top)
        (show y ∈ qW by rw [hqW]; exact Submodule.mem_top) hxy
    have hdim : Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W := le_antisymm
      (LinearMap.finrank_le_finrank_of_injective hAinj)
      (LinearMap.finrank_le_finrank_of_injective hBinj)
    exact ⟨⟨hAinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hAinj⟩,
      ⟨hBinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mp hBinj⟩⟩
  · exact (hqW_ne hq.2).elim

/-- If `B` is invertible, indecomposability of the quiver representation is
equivalent to indecomposability of the single operator `AB` on `W`; this is the
reduction used in Problem 6.9.1(b). -/
private lemma aeval_AB_indecomposable_of_B_bijective (ρ : Q₂Rep ℂ)
    (hρ : ρ.Indecomposable) (hB : Function.Bijective ρ.B) :
    Etingof.IsIndecomposable (Polynomial ℂ) (Module.AEval' (ρ.A.comp ρ.B)) := by
  classical
  let AB := ρ.A.comp ρ.B
  let ofAB := Module.AEval'.of (R := ℂ) AB
  have hWpos : 0 < Module.finrank ℂ ρ.W := by
    rcases hρ.1 with hV | hW
    · have := LinearMap.finrank_le_finrank_of_surjective hB.2
      omega
    · exact hW
  letI : Nontrivial ρ.W := Module.finrank_pos_iff.mp hWpos
  letI : Nontrivial (Module.AEval' AB) := ofAB.symm.toEquiv.nontrivial
  refine ⟨inferInstance, ?_⟩
  intro P Q hPQ
  let eB : ρ.W ≃ₗ[ℂ] ρ.V := LinearEquiv.ofBijective ρ.B hB
  let oW := Submodule.orderIsoMapComap ofAB
  let oB := Submodule.orderIsoMapComap eB
  let pW : Submodule ℂ ρ.W := oW.symm (P.restrictScalars ℂ)
  let qW : Submodule ℂ ρ.W := oW.symm (Q.restrictScalars ℂ)
  let pV : Submodule ℂ ρ.V := oB pW
  let qV : Submodule ℂ ρ.V := oB qW
  have hcW0 : IsCompl (P.restrictScalars ℂ) (Q.restrictScalars ℂ) :=
    ⟨by simpa using hPQ.disjoint, by simpa using hPQ.codisjoint⟩
  have hcW : IsCompl pW qW := oW.symm.isCompl hcW0
  have hcV : IsCompl pV qV := oB.isCompl hcW
  have invariant (N : Submodule (Polynomial ℂ) (Module.AEval' AB))
      (w : ρ.W) (hw : ofAB w ∈ N) : AB w ∈ oW.symm (N.restrictScalars ℂ) := by
    change ofAB (AB w) ∈ N
    rw [← Module.AEval'.X_smul_of]
    exact N.smul_mem Polynomial.X hw
  have hApV : ∀ x ∈ pV, ρ.A x ∈ pW := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    change ρ.A (ρ.B w) ∈ pW
    exact invariant P w hw
  have hAqV : ∀ x ∈ qV, ρ.A x ∈ qW := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    change ρ.A (ρ.B w) ∈ qW
    exact invariant Q w hw
  have hBpW : ∀ x ∈ pW, ρ.B x ∈ pV := by
    intro x hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hBqW : ∀ x ∈ qW, ρ.B x ∈ qV := by
    intro x hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with hp | hq
  · left
    apply Submodule.restrictScalars_injective ℂ (Polynomial ℂ) (Module.AEval' AB)
    apply oW.symm.injective
    simpa [pW] using hp.2
  · right
    apply Submodule.restrictScalars_injective ℂ (Polynomial ℂ) (Module.AEval' AB)
    apply oW.symm.injective
    simpa [qW] using hq.2

/-- Reverse coordinates and then regard a function as a Euclidean vector. -/
private noncomputable def reverseEuclidean (n : ℕ) :
    (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin n => ℂ) Fin.revPerm).trans
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

@[simp] private lemma reverseEuclidean_apply (n : ℕ) (x : Fin n → ℂ) (i : Fin n) :
    WithLp.ofLp (reverseEuclidean n x) i = x i.rev := by
  rfl

/-- Coordinate reversal changes the down-shift Jordan convention used by the
polynomial-module theorem into the up-shift convention of `Q₂Rep_E`. -/
private lemma reverseEuclidean_intertwines (lam : ℂ) (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℂ) :
    reverseEuclidean n (Etingof.Example_2_3_14.jordanBlock lam n x) =
      (Etingof.Q₂Rep_E n hn lam).A (reverseEuclidean n x) := by
  apply WithLp.ofLp_injective
  funext i
  simp only [reverseEuclidean_apply, Etingof.Example_2_3_14.jordanBlock_apply,
    Etingof.Q₂Rep_E, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Matrix.of_apply]
  have hentry (j : Fin n) :
      (if i = j then lam else if i.val = j.val + 1 then 1 else 0) * x j.rev =
        (if i = j then lam * x j.rev else 0) +
          (if i.val = j.val + 1 then x j.rev else 0) := by
    split_ifs <;> simp_all
  simp_rw [hentry, Finset.sum_add_distrib]
  have hfirst : (∑ j : Fin n, if i = j then lam * x j.rev else 0) =
      lam * x i.rev := by simp
  rw [hfirst]
  by_cases hi : (i : ℕ) = 0
  · have hrev : (i.rev : ℕ) = n - 1 := by simp [Fin.rev, hi]
    rw [dif_neg (by omega)]
    apply congrArg (lam * x i.rev + ·)
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by omega)]
  · have hi_pos : 0 < (i : ℕ) := by omega
    let j : Fin n := ⟨(i : ℕ) - 1, by omega⟩
    have hj (a : Fin n) : ((i : ℕ) = (a : ℕ) + 1) ↔ a = j := by
      constructor
      · intro h
        apply Fin.ext
        dsimp [j]
        omega
      · rintro rfl
        dsimp [j]
        omega
    simp_rw [hj]
    rw [Finset.sum_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, ↓reduceIte]
    have hrevlt : (i.rev : ℕ) + 1 < n := by simp [Fin.rev]; omega
    rw [dif_pos hrevlt]
    congr 2
    apply Fin.ext
    simp [j, Fin.rev]
    omega

/-- **Problem 6.9.1(b), isomorphism-level form.** If `AB` is not nilpotent in
an indecomposable representation, both arrows are invertible and Jordan normal
form gives an actual isomorphism with `E_{n,λ}`, where `λ ≠ 0`. -/
theorem Etingof.Problem6_9_1b_iso (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : ¬IsNilpotent (ρ.A.comp ρ.B)) :
    ∃ (n : ℕ) (hn : 0 < n) (lam : ℂ), lam ≠ 0 ∧
      Nonempty (ρ.Iso (Etingof.Q₂Rep_E n hn lam)) := by
  classical
  obtain ⟨hA, hB⟩ := nonnilpotent_arrows_bijective ρ hρ hAB
  let AB := ρ.A.comp ρ.B
  have hindecomp : Etingof.IsIndecomposable (Polynomial ℂ) (Module.AEval' AB) :=
    aeval_AB_indecomposable_of_B_bijective ρ hρ hB
  obtain ⟨lam, n, hn, ⟨e⟩⟩ :=
    Etingof.Example_2_3_14.exists_equiv_jordanRep
      (k := ℂ) (M := Module.AEval' AB) hindecomp
  let ofAB := Module.AEval'.of (R := ℂ) AB
  let J := Etingof.Example_2_3_14.jordanBlock lam n
  let ofJ := Module.AEval'.of (R := ℂ) J
  let e0 : ρ.W ≃ₗ[ℂ] (Fin n → ℂ) :=
    ofAB.trans ((e.restrictScalars ℂ).trans ofJ.symm)
  have he0 (w : ρ.W) : e0 (AB w) = J (e0 w) := by
    change ofJ.symm (e (ofAB (AB w))) = J (ofJ.symm (e (ofAB w)))
    simpa [pow_one] using aeval_equiv_pow_intertwines AB J
      (show Module.AEval' AB ≃ₗ[Polynomial ℂ] Module.AEval' J from e) 1 w
  have hlam : lam ≠ 0 := by
    intro hlam
    subst lam
    apply hAB
    refine ⟨n, ?_⟩
    apply LinearMap.ext
    intro w
    apply e0.injective
    have he0pow : e0 ((AB ^ n) w) = (J ^ n) (e0 w) := by
      simpa [e0, ofAB, ofJ] using aeval_equiv_pow_intertwines AB J
        (show Module.AEval' AB ≃ₗ[Polynomial ℂ] Module.AEval' J from e) n w
    rw [he0pow]
    have hJ : J = Etingof.Example_2_3_14.shift n := by
      simp [J, Etingof.Example_2_3_14.jordanBlock]
    rw [hJ, Etingof.Example_2_3_14.shift_pow_self]
    simp
  let eW : ρ.W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := e0.trans (reverseEuclidean n)
  let eB : ρ.W ≃ₗ[ℂ] ρ.V := LinearEquiv.ofBijective ρ.B hB
  let eV : ρ.V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := eB.symm.trans eW
  have hABmap (w : ρ.W) : eW (AB w) =
      (Etingof.Q₂Rep_E n hn lam).A (eW w) := by
    change reverseEuclidean n (e0 (AB w)) =
      (Etingof.Q₂Rep_E n hn lam).A (reverseEuclidean n (e0 w))
    rw [he0]
    exact reverseEuclidean_intertwines lam n hn (e0 w)
  have hmapA (v : ρ.V) : eW (ρ.A v) =
      (Etingof.Q₂Rep_E n hn lam).A (eV v) := by
    let w := eB.symm v
    have hw : eB w = v := eB.apply_symm_apply v
    rw [← hw]
    change eW (ρ.A (ρ.B w)) =
      (Etingof.Q₂Rep_E n hn lam).A (eW (eB.symm (eB w)))
    rw [eB.symm_apply_apply]
    exact hABmap w
  have hmapB (w : ρ.W) : eV (ρ.B w) =
      (Etingof.Q₂Rep_E n hn lam).B (eW w) := by
    change eW (eB.symm (ρ.B w)) = eW w
    rw [show ρ.B w = eB w from rfl, eB.symm_apply_apply]
  exact ⟨n, hn, lam, hlam, ⟨{
    eV := eV
    eW := eW
    map_A := hmapA
    map_B := hmapB }⟩⟩

universe uV uW

/-- **Problem 6.9.1(b), literal direct-summand form.** If `AB` is not
nilpotent, the representation contains an explicitly split direct summand
isomorphic to `E_{n,λ}` for some positive `n` and nonzero `λ`.  The inclusion
and retraction in `SplitEmbedding` are quiver maps, so this is construction
data for the asserted decomposition `E = E' ⊕ E_{n,λ}`. -/
theorem Etingof.Problem6_9_1b_directSummand (ρ : Q₂Rep.{0, uV, uW} ℂ)
    (hAB : ¬IsNilpotent (ρ.A.comp ρ.B)) :
    ∃ (n : ℕ) (hn : 0 < n) (lam : ℂ), lam ≠ 0 ∧
      ∃ τ : Q₂Rep.{0, uV, uW} ℂ, Nonempty (τ.SplitEmbedding ρ) ∧
        Nonempty (τ.Iso (Etingof.Q₂Rep_E n hn lam)) := by
  classical
  suffices h : ∀ d : ℕ, ∀ σ : Q₂Rep.{0, uV, uW} ℂ,
      Module.finrank ℂ σ.V + Module.finrank ℂ σ.W = d →
      ¬IsNilpotent (σ.A.comp σ.B) →
      ∃ (n : ℕ) (hn : 0 < n) (lam : ℂ), lam ≠ 0 ∧
        ∃ τ : Q₂Rep.{0, uV, uW} ℂ, Nonempty (τ.SplitEmbedding σ) ∧
          Nonempty (τ.Iso (Etingof.Q₂Rep_E n hn lam)) by
    exact h _ ρ rfl hAB
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro σ hdim hABσ
      have hdpos : 0 < d := by
        by_contra hnot
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
        have hW0 : Module.finrank ℂ σ.W = 0 := by omega
        letI : Subsingleton σ.W := Module.finrank_zero_iff.mp hW0
        apply hABσ
        exact ⟨1, Subsingleton.elim _ _⟩
      have hnon : 0 < Module.finrank ℂ σ.V ∨ 0 < Module.finrank ℂ σ.W := by
        rcases Nat.eq_zero_or_pos (Module.finrank ℂ σ.V) with hV0 | hVpos
        · right; omega
        · exact Or.inl hVpos
      by_cases hσ : σ.Indecomposable
      · obtain ⟨n, hn, lam, hlam, he⟩ := Etingof.Problem6_9_1b_iso σ hσ hABσ
        exact ⟨n, hn, lam, hlam, σ, ⟨Q₂Rep.SplitEmbedding.refl σ⟩, he⟩
      · rw [Q₂Rep.Indecomposable] at hσ
        have hnotdecomp : ¬ ∀ (pV qV : Submodule ℂ σ.V)
            (pW qW : Submodule ℂ σ.W),
            IsCompl pV qV → IsCompl pW qW →
            (∀ x ∈ pV, σ.A x ∈ pW) → (∀ x ∈ qV, σ.A x ∈ qW) →
            (∀ x ∈ pW, σ.B x ∈ pV) → (∀ x ∈ qW, σ.B x ∈ qV) →
            (pV = ⊥ ∧ pW = ⊥) ∨ (qV = ⊥ ∧ qW = ⊥) := by
          intro hdecomp
          exact hσ ⟨hnon, hdecomp⟩
        push Not at hnotdecomp
        obtain ⟨pV, qV, pW, qW, hcV, hcW, hApV, hAqV, hBpW, hBqW,
            hpV, hqV⟩ := hnotdecomp
        have hpne : ¬(pV = ⊥ ∧ pW = ⊥) := fun hzero => hpV hzero.1 hzero.2
        have hqne : ¬(qV = ⊥ ∧ qW = ⊥) := fun hzero => hqV hzero.1 hzero.2
        have hdimV : Module.finrank ℂ pV + Module.finrank ℂ qV =
            Module.finrank ℂ σ.V := by
          simpa [Module.finrank_prod] using
            (Submodule.prodEquivOfIsCompl pV qV hcV).finrank_eq
        have hdimW : Module.finrank ℂ pW + Module.finrank ℂ qW =
            Module.finrank ℂ σ.W := by
          simpa [Module.finrank_prod] using
            (Submodule.prodEquivOfIsCompl pW qW hcW).finrank_eq
        have hpdim : 0 < Module.finrank ℂ pV + Module.finrank ℂ pW := by
          by_contra hzero
          apply hpne
          exact ⟨Submodule.finrank_eq_zero.mp (by omega),
            Submodule.finrank_eq_zero.mp (by omega)⟩
        have hqdim : 0 < Module.finrank ℂ qV + Module.finrank ℂ qW := by
          by_contra hzero
          apply hqne
          exact ⟨Submodule.finrank_eq_zero.mp (by omega),
            Submodule.finrank_eq_zero.mp (by omega)⟩
        have hp_lt : Module.finrank ℂ pV + Module.finrank ℂ pW < d := by omega
        have hq_lt : Module.finrank ℂ qV + Module.finrank ℂ qW < d := by omega
        let σp := σ.restrict pV pW hApV hBpW
        let σq := σ.restrict qV qW hAqV hBqW
        by_cases hp : IsNilpotent (σp.A.comp σp.B)
        · have hq : ¬IsNilpotent (σq.A.comp σq.B) := by
            intro hqnil
            exact hABσ (σ.AB_isNilpotent_of_isCompl pV qV pW qW hcW
              hApV hAqV hBpW hBqW hp hqnil)
          obtain ⟨n, hn, lam, hlam, τ, ⟨e⟩, heiso⟩ := ih _ hq_lt σq rfl hq
          refine ⟨n, hn, lam, hlam, τ, ⟨e.trans ?_⟩, heiso⟩
          exact σ.restrictSplitEmbedding qV pV qW pW hcV.symm hcW.symm
            hAqV hApV hBqW hBpW
        · obtain ⟨n, hn, lam, hlam, τ, ⟨e⟩, heiso⟩ := ih _ hp_lt σp rfl hp
          refine ⟨n, hn, lam, hlam, τ, ⟨e.trans ?_⟩, heiso⟩
          exact σ.restrictSplitEmbedding pV qV pW qW hcV hcW
            hApV hAqV hBpW hBqW

private theorem classified_of_finrank_V_zero (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hV0 : Module.finrank ℂ ρ.V = 0) : Etingof.Q₂Rep.IsClassified ρ := by
  have hWpos : 0 < Module.finrank ℂ ρ.W := by
    rcases hρ.1 with hV | hW
    · omega
    · exact hW
  have hdim := Etingof.Problem6_9_1_dimension_vectors ρ hρ
  have hW1 : Module.finrank ℂ ρ.W = 1 := by
    rcases hdim with h | h | h <;> omega
  obtain ⟨eV⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.V = Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) by
      simp [hV0])
  obtain ⟨eW⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.W = Module.finrank ℂ (EuclideanSpace ℂ (Fin 1)) by
      simp [hW1])
  letI : Subsingleton ρ.V := Module.finrank_zero_iff.mp hV0
  let target := Etingof.Q₂Rep_K 1 (by omega)
  have hmapA (v : ρ.V) : eW (ρ.A v) = target.A (eV v) := by
    rw [Subsingleton.elim v 0, map_zero, map_zero, map_zero]
    exact target.A.map_zero.symm
  have hmapB (w : ρ.W) : eV (ρ.B w) = target.B (eW w) := by
    apply Subsingleton.elim
  refine ⟨Etingof.Q₂Family.preinjective ⟨1, by omega⟩, ⟨?_⟩⟩
  simpa [Etingof.Q₂Family.rep, target] using (show ρ.Iso target from {
    eV := eV
    eW := eW
    map_A := hmapA
    map_B := hmapB })

private theorem classified_of_finrank_W_zero (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hW0 : Module.finrank ℂ ρ.W = 0) : Etingof.Q₂Rep.IsClassified ρ := by
  have hVpos : 0 < Module.finrank ℂ ρ.V := by
    rcases hρ.1 with hV | hW
    · exact hV
    · omega
  have hdim := Etingof.Problem6_9_1_dimension_vectors ρ hρ
  have hV1 : Module.finrank ℂ ρ.V = 1 := by
    rcases hdim with h | h | h <;> omega
  obtain ⟨eV⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.V = Module.finrank ℂ (EuclideanSpace ℂ (Fin 1)) by
      simp [hV1])
  obtain ⟨eW⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.W = Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) by
      simp [hW0])
  letI : Subsingleton ρ.W := Module.finrank_zero_iff.mp hW0
  let target := Etingof.Q₂Rep_H 1 (by omega)
  have hmapA (v : ρ.V) : eW (ρ.A v) = target.A (eV v) := by
    apply Subsingleton.elim
  have hmapB (w : ρ.W) : eV (ρ.B w) = target.B (eW w) := by
    rw [Subsingleton.elim w 0, map_zero, map_zero, map_zero]
    exact target.B.map_zero.symm
  refine ⟨Etingof.Q₂Family.preprojective ⟨1, by omega⟩, ⟨?_⟩⟩
  simpa [Etingof.Q₂Family.rep, target] using (show ρ.Iso target from {
    eV := eV
    eW := eW
    map_A := hmapA
    map_B := hmapB })

/-- **Problem 6.9.1(a), exhaustiveness.** Every finite-dimensional
indecomposable representation of the cyclic two-vertex quiver is isomorphic to
one of the four concrete normal forms.  This statement carries representation
isomorphisms, not only the corresponding dimension-vector trichotomy. -/
theorem Etingof.Problem6_9_1 (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable) :
    Etingof.Q₂Rep.IsClassified ρ := by
  by_cases hAB : IsNilpotent (ρ.A.comp ρ.B)
  · by_cases hV0 : Module.finrank ℂ ρ.V = 0
    · exact classified_of_finrank_V_zero ρ hρ hV0
    by_cases hW0 : Module.finrank ℂ ρ.W = 0
    · exact classified_of_finrank_W_zero ρ hρ hW0
    obtain ⟨c⟩ := Etingof.Problem6_9_1c_exists_pureChainBasis ρ hρ hAB
      (Nat.pos_of_ne_zero hV0) (Nat.pos_of_ne_zero hW0)
    exact Etingof.Q₂Rep.PureChainBasis.isClassified c
  · obtain ⟨n, hn, lam, hlam, ⟨e⟩⟩ := Etingof.Problem6_9_1b_iso ρ hρ hAB
    exact ⟨Etingof.Q₂Family.finite ⟨n, hn⟩ lam, by
      simpa [Etingof.Q₂Family.rep] using (show Nonempty
        (ρ.Iso (Etingof.Q₂Rep_E n hn lam)) from ⟨e⟩)⟩

/-- The normal-form index in Problem 6.9.1 is unique. -/
theorem Etingof.Problem6_9_1_unique (ρ : Q₂Rep ℂ)
    {c d : Etingof.Q₂Family} (ec : Nonempty (ρ.Iso c.rep))
    (ed : Nonempty (ρ.Iso d.rep)) : c = d := by
  obtain ⟨ec⟩ := ec
  obtain ⟨ed⟩ := ed
  exact Etingof.Q₂Family.eq_of_rep_iso (ec.symm.trans ed)
