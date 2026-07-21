import FreeRange.Soundness

namespace FreeRange

/-- Prove a closed `Safe context expression` goal by the sound analyzer and native computation. -/
macro "freerange" : tactic =>
  `(tactic| exact FreeRange.safe_of_no_requirements (by native_decide))

end FreeRange
