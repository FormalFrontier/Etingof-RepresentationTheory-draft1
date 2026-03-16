# References: Section 9.2: Projective covers

## External Dependencies

- **Krull-Schmidt theorem: every module of finite length has a unique decomposition into indecomposable direct summands (up to isomorphism and reordering)** (external_result)
  Mathlib (missing): `IsNoetherian`, `IsArtinian`
  The Krull-Schmidt theorem itself is NOT in Mathlib. Noetherian and Artinian module conditions exist, but the unique decomposition theorem is absent. This would need to be formalized.
- **Nakayama's lemma: if M is a finitely generated module over a local ring and IM = M for I in the maximal ideal, then M = 0** (external_result)
  Mathlib (exact): `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`
  Nakayama's lemma is in Mathlib as `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`: if N is finitely generated, N ≤ I • N, and I ≤ jacobson ⊥, then N = ⊥.
