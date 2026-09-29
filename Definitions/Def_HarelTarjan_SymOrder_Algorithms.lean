import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- The algorithm to solve the nca depth problem (Harel–Tarjan, §3, p. 342), which uses only the
numbers `sym(·)`, the heights `h(·)` and the depth `d` of the tree:
* if `sym(w) ∈ [sym(v) − 2^{h(v)} + 1, sym(v) + 2^{h(v)} − 1]` (written additively), return
  `d − h(v)`;
* otherwise, if `sym(v) ∈ [sym(w) − 2^{h(w)} + 1, sym(w) + 2^{h(w)} − 1]`, return `d − h(w)`;
* otherwise return `d − ⌊lg (sym(v) ⊕ sym(w))⌋`, where `⊕` is bitwise exclusive or and
  `⌊lg x⌋` is `Nat.log 2 x`. -/
def ncaDepthAlg {d : ℕ} (v w : Vertex d) : ℕ :=
  if sym v + 1 ≤ sym w + 2 ^ height v ∧ sym w + 1 ≤ sym v + 2 ^ height v then
    d - height v
  else if sym w + 1 ≤ sym v + 2 ^ height w ∧ sym v + 1 ≤ sym w + 2 ^ height w then
    d - height w
  else
    d - Nat.log 2 (sym v ^^^ sym w)

/-- The number computed by the algorithm to solve the depth problem (Harel–Tarjan, §3, p. 342):
given a vertex `v` and a depth `d₂`, let `h = d − d₂` and return
`2^{h+1} ⌊sym(v) / 2^{h+1}⌋ + 2^h` (the algorithm then returns `sym⁻¹` of this number). -/
def depthAlgNum {d : ℕ} (v : Vertex d) (d₂ : ℕ) : ℕ :=
  2 ^ (d - d₂ + 1) * (sym v / 2 ^ (d - d₂ + 1)) + 2 ^ (d - d₂)

end HarelTarjan.SymOrder
