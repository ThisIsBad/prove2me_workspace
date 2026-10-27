import Mathlib

namespace QAlgorithms.Complexity
open Computability Turing

/-- Copied from `PvsNP.Str` (Cook, p.2): a binary string `w ∈ Σ*` with `Σ = {0,1}`. Used by de
Wolf p.122 (§13.2) for languages and reductions. -/
abbrev Str := List Bool

/-- Copied from `PvsNP.PolyTimeComputable` (Cook, Definition 3); de Wolf p.122 (§13.2), p.187
(§20.3): a function `f : Σ* → Σ*` is polynomial-time computable: a multi-stack machine started
with `w` on its input stack halts within `p(|w|)` steps with `f w` on its output stack, for some
polynomial `p`. -/
def PolyTimeComputable (f : Str → Str) : Prop :=
  Nonempty (TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f)

/-! ### From `Def_ShiShallow_Core.lean` (verbatim) -/

/-- Copied from `ShiBQP.encNat`: a natural number in unary, terminated by `false`. -/
def encNat (k : ℕ) : Str := List.replicate k true ++ [false]

end QAlgorithms.Complexity
