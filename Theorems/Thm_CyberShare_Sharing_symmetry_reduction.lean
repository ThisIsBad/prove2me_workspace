import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

namespace CyberShare.Sharing

/-- The symmetry observation in the proof of Proposition 2, pp. A.17–A.18 (PDF 49–50):
interchanging the firms interchanges the investment equilibria and ex-ante profits. Thus a
single firm's deviation comparison suffices for mutual sharing when all relevant investment
subgames have equilibria. -/
theorem symmetry_reduction (P : Params) (hP : P.Standing) :
    (∀ s1 s2 K1 K2, IsInvEq P s1 s2 K1 K2 ↔ IsInvEq P s2 s1 K2 K1) ∧
    (∀ K1 K2, exAnte2 P K1 K2 = exAnte1 P K2 K1) ∧
    ((∃ K1 K2, IsInvEq P .S .S K1 K2) →
     (∃ K1 K2, IsInvEq P .N .S K1 K2) →
     (IsSharingEq P .S .S ↔
       ∀ K1 K2 K1' K2', IsInvEq P .S .S K1 K2 → IsInvEq P .N .S K1' K2' →
         exAnte1 P K1' K2' ≤ exAnte1 P K1 K2)) := by sorry

end CyberShare.Sharing

