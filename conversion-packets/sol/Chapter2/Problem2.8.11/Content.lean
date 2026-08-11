import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem2811

#doc (Manual) "Hilbert series of graded algebras" =>
# Hilbert series of graded algebras
%%%
tag := "Chapter2/Problem2.8.11"
number := false
%%%
**Problem 2.8.11.** Let $`A` be a $`\mathbb{Z}_+`-graded algebra, i.e., $`A = \bigoplus_{n \geq 0} A[n]`, and $`A[n] \cdot A[m] \subset A[n+m]`. If $`A[n]` is finite dimensional, it is useful to consider the Hilbert series $`h_A(t) = \sum \dim A[n] t^n` (the generating function of dimensions of $`A[n]`). Often this series converges to a rational function, and the answer is written in the form of such a function. For example, if $`A = k[x]` and $`\deg(x^n) = n`, then

$$`
h_A(t) = 1 + t + t^2 + \cdots + t^n + \cdots = \frac{1}{1 - t}.
`

Find the Hilbert series of the following graded algebras:

(a) $`A = k[x_1, \ldots, x_m]` (where the grading is by degree of polynomials).

(b) $`A = k\langle x_1, \ldots, x_m \rangle` (the grading is by length of words).

(c) $`A` is the exterior (= Grassmann) algebra $`\wedge_k[x_1, \ldots, x_m]` generated over some field $`k` by $`x_1, \ldots, x_m` with the defining relations $`x_i x_j + x_j x_i = 0` and $`x_i^2 = 0` for all $`i, j` (the grading is by degree).

(d) $`A` is the path algebra $`P_Q` of a quiver $`Q` (the grading is defined by $`\deg(p_i) = 0`, $`\deg(a_h) = 1`).

Hint: The closed answer is written in terms of the adjacency matrix $`M_Q` of $`Q`.
