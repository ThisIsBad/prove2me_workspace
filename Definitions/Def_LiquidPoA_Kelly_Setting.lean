import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Mechanism

namespace LiquidPoA.Kelly

open Set Finset
open scoped ENNReal

/-- The class `𝒞` of Section 4, read as concavity and convexity in each own signal. -/
def InClassC {n : ℕ} (M : Mechanism n) : Prop :=
  ∀ s, IsSignal s → ∀ i, (∃ j, j ≠ i ∧ 0 < s j) →
    ConcaveOn ℝ (Ici 0) (allocIn M s i) ∧ ConvexOn ℝ (Ici 0) (payIn M s i)

/-- The Kelly rule of pp. 7 and 9: proportional shares and payment equal to signal. -/
noncomputable def kelly (n : ℕ) : Mechanism n where
  alloc s i := s i / ∑ j, s j
  pay s i := s i

/-- A resource allocation game with real valuations and possibly infinite budgets. -/
structure RAGame (n : ℕ) where
  v : Fin n → ℝ → ℝ
  c : Fin n → ℝ≥0∞

/-- The nonnegative, nondecreasing, concave, differentiable valuations of p. 5. -/
structure RAGame.IsAdmissible {n : ℕ} (G : RAGame n) : Prop where
  nonneg : ∀ i, ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ G.v i x
  mono : ∀ i, MonotoneOn (G.v i) (Icc 0 1)
  concave : ∀ i, ConcaveOn ℝ (Icc 0 1) (G.v i)
  diff : ∀ i, DifferentiableOn ℝ (G.v i) (Icc 0 1)

/-- A player can pay the charge at the signal profile. -/
def Affordable {n : ℕ} (M : Mechanism n) (G : RAGame n)
    (s : Fin n → ℝ) (i : Fin n) : Prop :=
  ENNReal.ofReal (M.pay s i) ≤ G.c i

/-- Real utility, used only when the player's payment is affordable. -/
def utility {n : ℕ} (M : Mechanism n) (G : RAGame n)
    (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  G.v i (M.alloc s i) - M.pay s i

/-- Pure Nash equilibrium with budget feasibility and nonnegative deviations. -/
def IsEquilibrium {n : ℕ} (M : Mechanism n) (G : RAGame n)
    (s : Fin n → ℝ) : Prop :=
  IsSignal s ∧ ∀ i, Affordable M G s i ∧
    ∀ y : ℝ, 0 ≤ y → Affordable M G (Function.update s i y) i →
      utility M G (Function.update s i y) i ≤ utility M G s i

/-- Liquid welfare of an allocation: each value is capped by the player's budget. -/
noncomputable def LW {n : ℕ} (G : RAGame n) (d : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ i, min (ENNReal.ofReal (G.v i (d i))) (G.c i)

/-- Optimal liquid welfare over the unit simplex and zero allocation. -/
noncomputable def optLW {n : ℕ} (G : RAGame n) : ℝ≥0∞ :=
  ⨆ (d : Fin n → ℝ) (_ : IsAllocation d), LW G d

/-- The game's liquid price of anarchy over all its pure Nash equilibria. -/
noncomputable def gameLPoA {n : ℕ} (M : Mechanism n) (G : RAGame n) : ℝ≥0∞ :=
  ⨆ (s : Fin n → ℝ) (_ : IsEquilibrium M G s), optLW G / LW G (M.alloc s)

/-- Liquid price of anarchy of a mechanism over all admissible games. -/
noncomputable def lpoa {n : ℕ} (M : Mechanism n) : ℝ≥0∞ :=
  ⨆ (G : RAGame n) (_ : G.IsAdmissible), gameLPoA M G

/-- The inverse allocation derivative times the payment derivative of p. 9. -/
noncomputable def lam {n : ℕ} (M : Mechanism n)
    (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  (derivWithin (allocIn M s i) (Ici 0) (s i))⁻¹ *
    derivWithin (payIn M s i) (Ici 0) (s i)

/-- The affine worst-case game `𝒢ᴹ(s,j)` of Section 4. -/
noncomputable def worstGame {n : ℕ} (M : Mechanism n)
    (s : Fin n → ℝ) (j : Fin n) : RAGame n where
  v i z := lam M s i * z + if i = j then 0 else M.pay s i
  c i := if i = j then ⊤ else ENNReal.ofReal (M.pay s i)

/-- The unit allocation to player `j` in Lemma 4.1. -/
def unitAlloc {n : ℕ} (j : Fin n) : Fin n → ℝ := Pi.single j 1

/-- The expression on the right-hand side of equation (6). -/
noncomputable def ratio {n : ℕ} (M : Mechanism n)
    (s : Fin n → ℝ) (j : Fin n) : ℝ≥0∞ :=
  ENNReal.ofReal ((∑ i ∈ univ.erase j, M.pay s i) + lam M s j) /
    ENNReal.ofReal ((∑ i ∈ univ.erase j, M.pay s i) +
      lam M s j * M.alloc s j)

end LiquidPoA.Kelly
