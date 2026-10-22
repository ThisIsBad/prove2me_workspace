import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.AWC

/-- The trivial seed `(b - 1, …, b - 1, 1)`: all digits `b - 1` and carry one (p. 472). -/
def topSeed (b r : ℕ) (hb : 2 ≤ b) : State b r :=
  ⟨fun _ => ⟨b - 1, by omega⟩, 1⟩

end CarryRNG.AWC
