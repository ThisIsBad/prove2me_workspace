import Definitions.Def_agt_games
import Mathlib

namespace DGPNash.NashMap

open Finset

/-- The payoff to player `p` when they play `j` and the other players use `x` (p. 205). -/
def purePayoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) (j : S p) : ℝ :=
  AGT.expectedPayoff u (Function.update x p (fun k => if k = j then 1 else 0)) p

/-- The alternative approximate Nash condition of p. 199 and Eq. (27), p. 243. -/
def IsApproxNash {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ)
    (x : Fin r → Fin n → ℝ) (ε : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    ∀ p (y : Fin n → ℝ), AGT.IsLottery y →
      AGT.expectedPayoff u (Function.update x p y) p ≤ AGT.expectedPayoff u x p + ε

/-- The largest entry of all payoff tables, `U_max` (p. 205). -/
noncomputable def maxPayoff {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) : ℝ :=
  sSup (Set.range (fun ps : Fin r × (Fin r → Fin n) => u ps.1 ps.2))

/-- The largest payoff for player `p`'s pure strategy `j`, across opponents' profiles (Lemma 3.5). -/
noncomputable def maxPurePayoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (p : ι) (j : S p) : ℝ :=
  sSup (Set.range (fun s : ∀ i, S i => u p (Function.update s p j)))

/-- The excess payoff `B⁽ᵖ⁾ⱼ(x)` of p. 205. -/
def gain {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ)
    (x : Fin r → Fin n → ℝ) (p : Fin r) (j : Fin n) : ℝ :=
  max 0 (purePayoff u x p j - AGT.expectedPayoff u x p)

/-- Nash's map `f` from p. 205, extended by the same formula to all real profiles. -/
noncomputable def nashMap {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ)
    (x : Fin r → Fin n → ℝ) (p : Fin r) (j : Fin n) : ℝ :=
  (x p j + gain u x p j) / (1 + ∑ k : Fin n, gain u x p k)

end DGPNash.NashMap
