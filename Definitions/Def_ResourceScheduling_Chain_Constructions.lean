import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Model
import Definitions.Def_ResourceScheduling_Chain_ThreePartition

/-!
# The scheduling instances built from a 3-PARTITION instance

* `p3Instance`: the `P3 | res1··, p_j = 1` instance of the proof of Theorem 4 (p. 16).
* `chainInstance`: the `P2 | res111, chain, p_j = 1` instance of the proof of Theorem 7
  (pp. 18–19).
-/

namespace ResourceScheduling.Chain

/-- The arcs of consecutive chains of the given lengths laid out one after another from
position `off`: a chain of length `len` starting at `off` has arcs `(off + c, off + c + 1)` for
`c + 1 < len`. -/
def chainArcsFrom : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | len :: rest, off =>
      (List.range (len - 1)).map (fun c => (off + c, off + c + 1)) ++ chainArcsFrom rest (off + len)

/-- A pair of positions as a pair of job indices in `Fin n`, when both are below `n`. -/
def toFinArc (n : ℕ) (e : ℕ × ℕ) : Option (Fin n × Fin n) :=
  if h : e.1 < n ∧ e.2 < n then some (⟨e.1, h.1⟩, ⟨e.2, h.2⟩) else none

namespace ThreePartition

variable (P : ThreePartition)

/-- The instance of the proof of Theorem 4: `3t` unit jobs, three machines, one resource of size
`b`, job `j` requiring `a_j`, and no precedence constraints. -/
def p3Instance : Instance where
  n := 3 * P.t
  m := 3
  l := 1
  s := fun _ => P.b
  r := fun _ j => P.a j
  arcs := []

/-- Requirements along the chain `L`: `2t` blocks of `b` jobs, the even-numbered blocks
(`J'_{ib+1}, …, J'_{(i+1)b}`) primed (requirement 1), the odd-numbered blocks
(`J_{ib+1}, …, J_{(i+1)b}`) unprimed (requirement 0). -/
def chainLReqs : List ℕ :=
  (List.range (2 * P.t)).flatMap fun k => List.replicate P.b (if k % 2 = 0 then 1 else 0)

/-- Requirements along the chains `K_j K'_j` for `j = 0, …, 3t − 1`: `a_j` unprimed jobs followed
by `a_j` primed jobs. -/
def chainKReqs : List ℕ :=
  (List.ofFn fun j => List.replicate (P.a j) 0 ++ List.replicate (P.a j) 1).flatten

/-- Requirements of all jobs, in position order: the chain `L`, then `K_0 K'_0`, `K_1 K'_1`, …. -/
def chainReqs : List ℕ := P.chainLReqs ++ P.chainKReqs

/-- The lengths of the chains in position order: `2tb` for `L`, then `2a_j` for `K_j K'_j`. -/
def chainLengths : List ℕ := (2 * P.t * P.b) :: List.ofFn fun j => 2 * P.a j

/-- The instance of the proof of Theorem 7: two machines, one resource of size one, primed jobs
requiring it and unprimed jobs not, precedence arcs along the chain `L` and along each chain
`K_j → K'_j`. -/
def chainInstance : Instance where
  n := P.chainReqs.length
  m := 2
  l := 1
  s := fun _ => 1
  r := fun _ j => P.chainReqs.get j
  arcs := (chainArcsFrom P.chainLengths 0).filterMap (toFinArc P.chainReqs.length)

end ThreePartition

end ResourceScheduling.Chain
