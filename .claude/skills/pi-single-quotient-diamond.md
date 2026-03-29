# Pi.single DecidableEq Diamond on Quotient Groups

## The Problem

When using `Pi.single q v` where `q : G ⧸ H` (a quotient group coset), Lean
often picks `Quotient.decidableEq` for the `DecidableEq` instance instead of
`QuotientGroup.instDecidableEq`. These instances are propositionally equal but
not definitionally equal, causing `rw`, `simp`, `simp_rw`, and `exact` to fail
when matching `Pi.single` patterns.

**Symptom:** `rw [Pi.single_eq_of_ne h]` or `rw [Pi.single_eq_same]` fails
with "did not find occurrence of pattern" or "motive is not type correct".

## When You Hit This

- Working with `Pi.single` on `G ⧸ H` (quotient group cosets)
- After `G_action_at_coset` or similar rewrites that produce `Pi.single q v (g⁻¹ • q')`
- In proofs about induced representations that use coset-indexed function spaces

## Workarounds (in order of preference)

### 1. Avoid Pi.single in proof goals entirely

Instead of proving `Pi.single q₁ x = Pi.single q₁ y`, work with an intermediate
term `r` and show `r = Pi.single q₁ (r q₁)` using `ext q; by_cases`:

```lean
-- This pattern works because ext introduces q with consistent DecidableEq
have hr_eq : r = Pi.single q₁ (r q₁) := by
  ext q; by_cases hq : q = q₁
  · rw [hq, Pi.single_eq_same]
  · rw [hr_supp q hq]  -- rewrites LHS to 0; RHS reduces by rfl
```

### 2. Use `convert` to bridge instance differences

```lean
convert h_mem using 0  -- bridges Pi.single with different DecidableEq instances
```

### 3. For membership proofs, go through an intermediate function

Instead of `Pi.single q₁ (f v) ∈ σ`, prove `r ∈ σ` where `r` is computed
by the group action, then show `r` agrees with `Pi.single q₁ (f v)` pointwise
via the pattern in workaround #1.

## What Does NOT Work

- `rw [Pi.single_eq_of_ne h]` — fails to match pattern
- `simp only [Pi.single_apply]` — type family treated as dependent
- `Function.update_of_ne` — same dependent type mismatch
- `simp_rw [hg'_fix]` — motive not type correct (dependent rewrite)
- `funext` then `show ... Pi.single q₁ x q ...` — type `?m q` not `↑U.V`
