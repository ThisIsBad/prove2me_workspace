import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.SymSum

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Symmetric (single-commodity) congestion game (Sect. 2, PDF p. 2): all the players have the same
strategy set, `Σᵢ = Σ` for every player `i`. -/
def IsSymmetric (G : CongestionPoA.AsymSum.CongestionGame ι E) : Prop := ∀ i j, G.strategies i = G.strategies j

end CongestionPoA.SymSum
