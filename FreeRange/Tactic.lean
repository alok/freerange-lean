import FreeRange.Soundness

namespace FreeRange

/-- Prove a closed `Safe context expression` goal by the sound analyzer and kernel computation. -/
macro "freerange" : tactic =>
  `(tactic| exact FreeRange.safe_of_no_requirements (by decide))

end FreeRange
