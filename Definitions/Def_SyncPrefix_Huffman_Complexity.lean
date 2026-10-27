import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Instance

namespace SyncPrefix.Huffman

open SetCoverThreshold.SetCover

/-- `P = NP`: every NP language over every finite nonempty alphabet is in P. -/
def PEqNP : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym

/-- Short Sync Word can be approximated in polynomial time within `ρ(n)` on the class `C`
(value form): a polynomial-time `Alg` and a threshold `n₀` such that, on every synchronizing
automaton `A` of the class with `n₀ ≤ n` states, the output length `v` satisfies
`syncLength ≤ v ≤ ρ(n) · syncLength`. -/
def SSWApproxWithin (C : Automaton → Prop) (ρ : ℕ → ℝ) : Prop :=
  ∃ Alg : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg ∧
    ∃ n₀ : ℕ, ∀ A : Automaton, C A → IsSynchronizing A.δ → n₀ ≤ A.n →
      syncLength A.δ ≤ (Alg A.encode).length ∧
        ((Alg A.encode).length : ℝ) ≤ ρ A.n * syncLength A.δ

/-- The minimum size of a set cover. Junk value `0` when the instance is not coverable. -/
noncomputable def minCover (I : SCInstance) : ℕ :=
  sInf {c | ∃ C, I.IsCover C ∧ C.card = c}

/-- Set Cover can be approximated in polynomial time within `ρ(p)` on the class `C` (value
form, `p = I.n` points): a polynomial-time `Alg` and a threshold `n₀` such that, on every
coverable instance of the class with `n₀ ≤ p`, the output length `v` satisfies
`minCover ≤ v ≤ ρ(p) · minCover`. -/
def SCApproxWithinOn (C : SCInstance → Prop) (ρ : ℕ → ℝ) : Prop :=
  ∃ Alg : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg ∧
    ∃ n₀ : ℕ, ∀ I : SCInstance, C I → I.Coverable → n₀ ≤ I.n →
      minCover I ≤ (Alg I.encode).length ∧
        ((Alg I.encode).length : ℝ) ≤ ρ I.n * minCover I

/-- The Set Cover hardness of [4] quoted on p. 5: for every `γ > 0` there is `c' > 0` such that
a polynomial-time `c' log p`-approximation of Set Cover on instances with `|C| ≤ |X|^{1+γ}`
implies `P = NP`. -/
def SetCoverHardness : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ c' : ℝ, 0 < c' ∧
    (SCApproxWithinOn (fun I => (I.sets.length : ℝ) ≤ (I.n : ℝ) ^ (1 + γ))
      (fun p => c' * Real.log p) → PEqNP)

end SyncPrefix.Huffman
