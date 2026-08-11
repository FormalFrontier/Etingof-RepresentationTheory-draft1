/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter9.Proposition923

#doc (Manual) "Hom from projective cover computes Jordan-Holder multiplicity" =>

# Hom from projective cover computes Jordan-Holder multiplicity
%%%
tag := "Chapter9/Proposition9.2.3"
number := false
%%%

*Proposition 9.2.3.* _Let $`N` be any finite dimensional $`A`-module. Then one has $`\dim \operatorname{Hom}_A(P_i, N) = [N : M_i]`, the multiplicity of occurrence on $`M_i` in the Jordan-Hölder series of $`N`._

*Proof.* If $`N = M_j`, the statement is clear. Also, if

$$`0 \to N_1 \to N_2 \to N_3 \to 0`

is an exact sequence of $`A`-modules, then the corresponding sequence

$$`0 \to \operatorname{Hom}_A(P_i, N_1) \to \operatorname{Hom}_A(P_i, N_2) \to \operatorname{Hom}_A(P_i, N_3) \to 0`

is exact, as $`P_i` is projective. This implies the statement. $`\square`
