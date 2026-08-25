import BookRef.Attribute

namespace BookRef.Examples

/-- A theorem with existing prose in its docstring. -/
@[book_ref "Chapter6/Theorem6.5.2" (role := primary)]
theorem theorem652 : 2 + 2 = 4 := by decide

@[book_ref "Chapter6/Theorem6.5.2" (role := supporting)]
theorem theorem652_helper : True := by trivial

@[book_ref "Chapter2/Definition2.1" (role := primary)]
def sampleDefinition : Nat := 42

end BookRef.Examples
