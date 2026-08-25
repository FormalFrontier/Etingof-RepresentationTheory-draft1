import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Discussion212Heading

#doc (Manual) "Section 2.12: The tensor algebra \u2014 heading and introduction" =>
# Section 2.12: The tensor algebra — heading and introduction
%%%
tag := "Chapter2/Discussion_2.12_heading"
number := false
%%%

## 2.12. The tensor algebra
%%%
tag := "Chapter2/Discussion_2.12_heading/heading-1"
%%%

The notion of tensor product allows us to give more conceptual (i.e., coordinate-free) definitions of the free algebra, polynomial algebra, exterior algebra, and universal enveloping algebra of a Lie algebra.

Namely, given a vector space $`V`, define its **tensor algebra** $`TV` over a field $`k` to be $`TV = \bigoplus_{n \geq 0} V^{\otimes n}`, with multiplication defined by $`a \cdot b := a \otimes b`, $`a \in V^{\otimes n}`, $`b \in V^{\otimes m}`. Observe that a choice of a basis
