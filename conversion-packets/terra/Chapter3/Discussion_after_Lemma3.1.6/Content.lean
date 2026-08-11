import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.DiscussionAfterLemma316

#doc (Manual) "Completion of alternative proof of Proposition 3.1.4" =>
# Completion of alternative proof of Proposition 3.1.4
%%%
tag := "Chapter3/Discussion_after_Lemma3.1.6"
number := false
%%%
Now we are ready to prove Proposition 3.1.4. Let $`W` be a submodule of $`V := \bigoplus_X V_X \otimes X`, where $`\dim V < \infty`. We claim that $`W = \bigoplus_X W_X \otimes X` for some vector spaces $`W_X \subseteq V_X`. Indeed, by Lemma 3.1.6 have $`V/W = \bigoplus_X U_X \otimes X` for some vector spaces $`U_X`, so

$$`W = \operatorname{Ker}(V \to V/W) = \bigoplus_X \operatorname{Ker}(V_X \to U_X) \otimes X,`

as desired.
