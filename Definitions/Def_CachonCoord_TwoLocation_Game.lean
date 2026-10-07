import Mathlib

namespace CachonCoord.TwoLocation

/-- A (pure-strategy) Nash equilibrium of a two-player cost-minimization game in which each
player chooses a real number (here: a base stock level, which may be negative). Player `r` has
cost `costR (s_r, s_s)`, player `s` has cost `costS (s_r, s_s)`; `{s_r, s_s}` is a Nash
equilibrium when neither firm can lower its own cost by a unilateral deviation
(Cachon 2003, §6.8.3, p. 79). -/
def IsNashMin (costR costS : ℝ → ℝ → ℝ) (sr ss : ℝ) : Prop :=
  IsMinOn (fun x => costR x ss) Set.univ sr ∧ IsMinOn (fun y => costS sr y) Set.univ ss

end CachonCoord.TwoLocation
