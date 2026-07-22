import Mathlib

/-!
# Problem 2.13.1: The Dehn invariant and Hilbert's third problem

To any polyhedron `A` one attaches its **Dehn invariant** `D(A) ∈ ℝ ⊗ (ℝ/ℚ)` (a tensor product of
`ℚ`-vector spaces), `D(A) = Σₐ l(a) ⊗ β(a)/π`, summing over edges `a` with length `l(a)` and
dihedral angle `β(a)`. The problem has three parts:

* **(a)** cutting `A` into `B` and `C` gives `D(A) = D(B) + D(C)`;
* **(b)** `α = arccos(1/3)/π` is irrational;
* **(c)** the regular tetrahedron and cube of equal volume have different Dehn invariants, so they
  are not scissors-congruent (a negative answer to Hilbert's third problem).

## Intentional scope decision

Part **(b)**, the irrationality of `arccos(1/3)/π`, is formalized below. Parts (a) and (c) are
intentionally omitted from this project: they require a theory of polyhedra, dissection and
scissors congruence, dihedral angles, and the Dehn invariant valued in `ℝ ⊗_ℚ (ℝ/ℚ)`. This
decision is recorded in the repository's public scope document, `skipped-exercises.md`. The
omission is documentation-only; there is no placeholder declaration for parts (a) or (c).

## Proof of (b)

We follow the book's hint. Set `θ = arccos(1/3)`, so `cos θ = 1/3`. Define the integer sequence
`b₀ = 1`, `b₁ = 1`, `bₖ₊₂ = 2 bₖ₊₁ - 9 bₖ`. Multiplying the Chebyshev recurrence
`cos((k+2)θ) = 2 cos θ · cos((k+1)θ) - cos(kθ)` by `3^(k+2)` shows `bₖ = 3^k · cos(kθ)`.
Reducing the recurrence mod `3` gives `3 ∤ bₖ` for every `k`.

Now if `α = θ/π` were rational, say `α = r` with denominator `q = r.den`, then
`cos((2q)·θ) = cos(r.num · 2π) = 1`, so `b_{2q} = 3^{2q} · 1 = 3^{2q}`. But `3 ∣ 3^{2q}`
while `3 ∤ b_{2q}`, a contradiction.
-/

namespace Etingof.Problem2_13_1

open Real

/-- The integer sequence `b₀ = 1`, `b₁ = 1`, `bₖ₊₂ = 2 bₖ₊₁ - 9 bₖ`. One has `bₖ = 3^k cos(kθ)`
for `θ = arccos(1/3)` (see `Problem2_13_1.b_eq`) and `3 ∤ bₖ` (see `Problem2_13_1.b_not_dvd`). -/
private def b : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (n + 2) => 2 * b (n + 1) - 9 * b n

/-- `bₖ = 3^k · cos(kθ)` whenever `cos θ = 1/3`. Proved by two-step induction using the Chebyshev
recurrence `cos((k+2)θ) = 2 cos θ · cos((k+1)θ) - cos(kθ)`. -/
private lemma b_eq (θ : ℝ) (hθ : cos θ = 1 / 3) (n : ℕ) :
    (↑(b n) : ℝ) = 3 ^ n * cos (↑n * θ) ∧
    (↑(b (n + 1)) : ℝ) = 3 ^ (n + 1) * cos (↑(n + 1) * θ) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> norm_num [b, hθ]
  | succ n ih =>
    obtain ⟨hA, hB⟩ := ih
    refine ⟨hB, ?_⟩
    have hrec : (↑(b (n + 1 + 1)) : ℝ) = 2 * ↑(b (n + 1)) - 9 * ↑(b n) := by
      have : b (n + 1 + 1) = 2 * b (n + 1) - 9 * b n := by simp only [b]
      rw [this]; push_cast; ring
    have R : cos ((↑(n + 1 + 1) : ℝ) * θ)
        = 2 * cos θ * cos ((↑(n + 1) : ℝ) * θ) - cos ((↑n : ℝ) * θ) := by
      have e1 : (↑(n + 1 + 1) : ℝ) * θ = (↑(n + 1) : ℝ) * θ + θ := by push_cast; ring
      have e2 : (↑n : ℝ) * θ = (↑(n + 1) : ℝ) * θ - θ := by push_cast; ring
      rw [e1, e2, Real.cos_add, Real.cos_sub]; ring
    rw [hrec, hB, hA, R, hθ]
    ring

/-- `3 ∤ bₖ` for every `k`: reducing the recurrence mod `3` gives `bₖ₊₂ ≡ 2 bₖ₊₁ (mod 3)`, so the
residue stays in `{1, 2}` starting from `b₀ = b₁ = 1`. -/
private lemma b_not_dvd (n : ℕ) : ¬ (3 ∣ b n) := by
  have H : ∀ m : ℕ, (b m % 3 = 1 ∨ b m % 3 = 2) ∧ (b (m + 1) % 3 = 1 ∨ b (m + 1) % 3 = 2) := by
    intro m
    induction m with
    | zero => refine ⟨Or.inl ?_, Or.inl ?_⟩ <;> decide
    | succ m ih =>
      obtain ⟨_, h2⟩ := ih
      refine ⟨h2, ?_⟩
      have hrec : b (m + 1 + 1) = 2 * b (m + 1) - 9 * b m := by simp only [b]
      omega
  have := (H n).1
  omega

/-- **Problem 2.13.1(b).** The number `α = arccos(1/3)/π` is irrational. -/
theorem irrational_arccos_third_div_pi : Irrational (arccos (1 / 3) / π) := by
  intro h
  obtain ⟨r, hr⟩ := h
  set θ := arccos (1 / 3) with hθdef
  have hθcos : cos θ = 1 / 3 := Real.cos_arccos (by norm_num) (by norm_num)
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [eq_div_iff hπ] at hr
  -- `hr : ↑r * π = θ`.
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hrq : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
    rw [Rat.cast_def]; field_simp
  -- `cos ((2·den)·θ) = cos (num · 2π) = 1`.
  have harg : (↑(2 * r.den) : ℝ) * θ = (r.num : ℝ) * (2 * π) := by
    have hθ2 : θ = (r : ℝ) * π := hr.symm
    rw [hθ2]; push_cast; linear_combination (2 * π) * hrq
  have hcos1 : cos ((↑(2 * r.den) : ℝ) * θ) = 1 := by
    rw [harg]; exact Real.cos_int_mul_two_pi r.num
  -- Hence `b_{2·den} = 3^{2·den}`, but `3 ∤ b_{2·den}`.
  have hkey := (b_eq θ hθcos (2 * r.den)).1
  rw [hcos1, mul_one] at hkey
  have hb_eq : b (2 * r.den) = 3 ^ (2 * r.den) := by exact_mod_cast hkey
  have hn0 : 2 * r.den ≠ 0 := by have := r.den_pos; omega
  exact b_not_dvd (2 * r.den) (hb_eq ▸ dvd_pow_self 3 hn0)

end Etingof.Problem2_13_1
