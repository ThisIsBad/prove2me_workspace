import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum

namespace OnlinePrimalDual.Framework

/-- The final value Algorithm 1 (the basic discrete algorithm, p. 118, PDF p. 29) assigns to
primal variable `xᵢ`. Algorithm 1's own update rule (p. 118, step (1a)) is
`xᵢ ← xᵢ(1 + 1/cᵢ) + 1/(|S(j)|cᵢ)`, applied once per inner-loop iteration to every `i ∈ S(j)`
while constraint `j` is being processed — using *that round's own* `|S(j)| = (inst.S j).card`,
not a fixed bound. Since which rounds touch `i`, and in what order, matters (the multiplicative
`(1+1/cᵢ)` factor compounds differently depending on interleaving), the true final value needs an
explicit arrival order on the constraints; `ord : List J` is that order (the sequence in which
the online algorithm sees constraints `j`, one entry per element of `J`). For a fixed `i`, we walk
`ord` restricted to the rounds `j` with `i ∈ S j`, in order, and for each such round apply the
round's own affine update `t j` times in a row (all `t j` increments of round `j` share the same
`|S(j)|`, since `S(j)` does not change mid-round), starting from `x = 0`. This is Algorithm 1's
own recurrence, exactly, with no substitution. -/
noncomputable def alg1X {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (inst : CoveringInstance I J) (ord : List J) (t : J → ℕ) (i : I) : ℝ :=
  (ord.filter (fun j => i ∈ inst.S j)).foldl
    (fun x j => (fun y => y * (1 + 1 / inst.c i) + 1 / ((inst.S j).card * inst.c i))^[t j] x) 0

end OnlinePrimalDual.Framework
