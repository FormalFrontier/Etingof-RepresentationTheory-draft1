# Toolchain compatibility

- Draft baseline: `2712420950ca8da299737f1d21d5c395ec9e27b4`.
- Root toolchain: `leanprover/lean4:v4.32.2`.
- Mathlib: tag `v4.32.2`, commit `905b95818eb32af7874a58b427f50c1711a5e96c`.
- Verso: tag `v4.32.0`, commit `e09d21a5f7f66c9fc985b73197708298569bf583`.
- Result: a clean Lake project using Lean 4.32.2 and Mathlib 4.32.2 compiled `VersoManual` from Verso v4.32.0 successfully.

The release workspaces should therefore use Lean/Mathlib 4.32.2 and pin Verso v4.32.0 by resolved commit.
