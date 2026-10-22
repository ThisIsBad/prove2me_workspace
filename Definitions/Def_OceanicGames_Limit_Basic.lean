import Mathlib
import Definitions.Def_OceanicGames_Limit_WeightedMajority
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_OceanicGames_Interior_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset Filter

variable {m : ℕ}

/-- The finite game's Shapley OceanicGames.Interior.value to major player i; the major players come
first in the concatenated player list. -/
noncomputable def finiteValue {n : ℕ} (c : ℝ) (w : Fin m → ℝ)
    (a : Fin n → ℝ) (i : Fin m) : ℝ :=
  Supermodularity.Cooperative.ShapleyValue (wmGame c (Fin.append w a)) (Fin.castAdd n i)

/-- B_{i,S} of (3.3), including its ambient OceanicGames.Interior.cube. -/
def orderSet (i : Fin m) (S : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {x | x ∈ OceanicGames.Interior.cube m ∧ (∀ j ∈ S, x j < x i) ∧ ∀ j ∉ S, x i ≤ x j}

/-- The bracket of p. 8: the median of 0, t, and 1. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

/-- The expression (A.3), with the integral over the intersection of the
two closed intervals specified on p. 26. -/
noncomputable def limitFormula (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ S ∈ (Finset.univ.erase i).powerset,
    ∫ t in Set.Icc (0 : ℝ) 1 ∩
      Set.Icc ((c - OceanicGames.Interior.wsum w S - w i) / alpha) ((c - OceanicGames.Interior.wsum w S) / alpha),
      t ^ S.card * (1 - t) ^ (m - S.card - 1)

end OceanicGames.Limit
