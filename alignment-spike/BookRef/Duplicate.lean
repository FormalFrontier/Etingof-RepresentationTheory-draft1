import BookRef.Attribute

namespace BookRef.Duplicate

@[book_ref "Chapter9/Theorem9.1" (role := primary),
  book_ref "Chapter9/Theorem9.1" (role := primary)]
theorem exactDuplicateIsIdempotent : True := by trivial

end BookRef.Duplicate
