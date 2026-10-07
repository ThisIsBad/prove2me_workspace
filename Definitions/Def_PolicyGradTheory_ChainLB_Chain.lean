import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace PolicyGradTheory.ChainLB

open FoundationsML.ReinforcementLearning

/-- Figure 2 and (27): the deterministic chain transition kernel. -/
def chainP (H : ℕ) (s : Fin (H + 2)) (a : Fin 4) (s' : Fin (H + 2)) : ℝ :=
  if s.val = 0 then
    if s'.val = 1 then 1 else 0
  else if s.val = H + 1 then
    if s' = s then 1 else 0
  else if a.val = 0 then
    if s'.val = s.val + 1 then 1 else 0
  else
    if s'.val + 1 = s.val then 1 else 0

/-- Figure 2: the only positive reward is one at `(s_{H+1},a₁)`. -/
def chainR (H : ℕ) (s : Fin (H + 2)) (a : Fin 4) : ℝ :=
  if s = Fin.last (H + 1) ∧ a.val = 0 then 1 else 0

/-- The discount factor of Proposition 4.1. -/
noncomputable def chainGamma (H : ℕ) : ℝ := (H : ℝ) / (H + 1)

/-- The direct policy parameterization from §4.3, with three coordinates per interior state. -/
noncomputable def chainPolicy (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (s : Fin (H + 2)) (a : Fin 4) : ℝ :=
  if hs : 0 < s.val ∧ s.val ≤ H then
    let i : Fin H := ⟨s.val - 1, by omega⟩
    if ha : a.val < 3 then
      θ (i, ⟨a.val, ha⟩)
    else
      1 - θ (i, 0) - θ (i, 1) - θ (i, 2)
  else
    if a.val = 0 then 1 else 0

/-- The discounted return from s₀ for the chain. -/
noncomputable def chainValue (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) : ℝ :=
  PolicyValue (chainPolicy H θ) (chainP H) (chainR H) (chainGamma H) 0

/-- The vector of a₁ probabilities in the interior states. -/
noncomputable def forwardProb (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) : Fin H → ℝ :=
  fun i => θ (i, 0)

/-- Equation (27), parameterized by the forward probabilities. -/
def chainMatrix (H : ℕ) (p : Fin H → ℝ) : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ :=
  fun s s' =>
    if s.val = 0 then
      if s'.val = 1 then 1 else 0
    else if s.val = H + 1 then
      if s' = s then 1 else 0
    else if hs : 0 < s.val ∧ s.val ≤ H then
      let i : Fin H := ⟨s.val - 1, by omega⟩
      if s'.val = s.val + 1 then p i
      else if s'.val + 1 = s.val then 1 - p i
      else 0
    else 0

/-- The resolvent `M^θ = (I - γP^θ)⁻¹` of Appendix B.2. -/
noncomputable def chainResolvent (H : ℕ) (p : Fin H → ℝ) :
    Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ :=
  (1 - chainGamma H • chainMatrix H p)⁻¹

/-- The five-state MDP in Figure 1, for Lemma 3.1. -/
def nonconcaveP (s : Fin 5) (a : Fin 2) (s' : Fin 5) : ℝ :=
  let dest : Fin 5 :=
    if s.val = 0 then (if a.val = 0 then 2 else 1)
    else if s.val = 1 then (if a.val = 0 then 3 else 4)
    else s
  if s' = dest then 1 else 0

/-- Figure 1: the transition s₂ --a₁→ s₄ earns reward `r`. -/
def nonconcaveR (r : ℝ) (s : Fin 5) (a : Fin 2) : ℝ :=
  if s.val = 1 ∧ a.val = 0 then r else 0

/-- Softmax policies on Figure 1. -/
noncomputable def nonconcaveSoftmax (θ : EuclideanSpace ℝ (Fin 5 × Fin 2))
    (s : Fin 5) (a : Fin 2) : ℝ :=
  Real.exp (θ (s, a)) / ∑ b : Fin 2, Real.exp (θ (s, b))

/-- Direct policies on Figure 1, with one free coordinate per state. -/
noncomputable def nonconcaveDirect (θ : EuclideanSpace ℝ (Fin 5))
    (s : Fin 5) (a : Fin 2) : ℝ :=
  if a.val = 0 then θ s else 1 - θ s

/-- Feasible direct policy parameters for Figure 1. -/
def directSimplex : Set (EuclideanSpace ℝ (Fin 5)) :=
  {θ | ∀ s, 0 ≤ θ s ∧ θ s ≤ 1}

end PolicyGradTheory.ChainLB
