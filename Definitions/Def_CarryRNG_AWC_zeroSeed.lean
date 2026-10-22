import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.AWC

/-- The trivial seed `(0, …, 0, 0)`: all digits zero and carry zero (p. 472). -/
def zeroSeed (b r : ℕ) (hb : 2 ≤ b) : State b r :=
  ⟨fun _ => ⟨0, by omega⟩, 0⟩

end CarryRNG.AWC
