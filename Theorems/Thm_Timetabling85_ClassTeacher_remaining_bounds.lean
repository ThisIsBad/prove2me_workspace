import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- The remaining days stay balanced (de Werra 1985, §2.1, p. 153): if `p ≥ 2` and a day receives
`y` of `s` lectures with `⌊s/p⌋ ≤ y ≤ ⌈s/p⌉`, the remaining `s − y` lectures over `p − 1` days
have bounds `⌊(s−y)/(p−1)⌋ ≥ ⌊s/p⌋` and `⌈(s−y)/(p−1)⌉ ≤ ⌈s/p⌉`. -/
theorem remaining_bounds (s y p : ℕ) (hp : 2 ≤ p) (hlo : lo s p ≤ y) (hhi : y ≤ hi s p) :
    lo s p ≤ lo (s - y) (p - 1) ∧ hi (s - y) (p - 1) ≤ hi s p := by sorry

end Timetabling85.ClassTeacher

