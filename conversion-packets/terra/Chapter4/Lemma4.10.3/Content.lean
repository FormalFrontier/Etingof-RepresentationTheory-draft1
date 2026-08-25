import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Lemma4103

#doc (Manual) "Determinant of a generic matrix is irreducible" =>

# Determinant of a generic matrix is irreducible
%%%
tag := "Chapter4/Lemma4.10.3"
number := false
%%%

**Lemma 4.10.3.** _Let $`Y` be an $`n \times n` matrix with entries $`y_{ij}`. Then $`\det Y` is an irreducible polynomial of $`\{y_{ij}\}`._

**Proof.** Let $`X = t \cdot \mathrm{Id} + \sum_{i=1}^{n} x_i E_{i,i+1}`, where $`i + 1` is computed modulo $`n`, and $`E_{i,j}` are the elementary matrices. Then $`\det(X) = t^n - (-1)^n x_1 \ldots x_n`, which is obviously irreducible. Hence $`\det(Y)` is irreducible (since it is so when $`Y` is specialized to $`X`, and since irreducible factors of a homogeneous polynomial are homogeneous, so cannot specialize to nonzero constants). $`\square`
