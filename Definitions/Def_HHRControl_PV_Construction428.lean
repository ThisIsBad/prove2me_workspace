import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

/-! # Construction 4.28: the election built from a Hitting Set instance

Hemaspaandra, Hemaspaandra & Rothe, *Anyone but Him*, arXiv:cs/0507027v5, p. 24, Construction 4.28.

The candidates are `Fin (m + 2)`: `b j = j` for `j : Fin m` (the set `B`), `c = m` and `w = m + 1`.
The construction leaves the order of the remaining candidates in every ballot, and the order of
the elements of `S i`, arbitrary; `IsConstruction428` therefore holds for every profile of the
stated shape. -/

/-- The candidate `b j` (`j : Fin m`) of Construction 4.28. -/
def candB {m : ℕ} (j : Fin m) : Fin (m + 2) := Fin.castAdd 2 j

/-- The candidate `c` of Construction 4.28. -/
def candC (m : ℕ) : Fin (m + 2) := ⟨m, by omega⟩

/-- The candidate `w` of Construction 4.28. -/
def candW (m : ℕ) : Fin (m + 2) := ⟨m + 1, by omega⟩

/-- The four kinds of voters of Construction 4.28. -/
inductive VoterType (m n : ℕ) where
  /-- a voter `c > w > ⋯` -/
  | cw
  /-- a voter `w > c > ⋯` -/
  | wc
  /-- a voter `Sᵢ > c > ⋯` -/
  | set (i : Fin n)
  /-- a voter `bⱼ > w > ⋯` -/
  | elem (j : Fin m)
  deriving DecidableEq

/-- The ballot `r` has the form its type `t` prescribes:
`c > w > ⋯`, `w > c > ⋯`, `Sᵢ > c > ⋯` (the elements of `Sᵢ` in the first `|Sᵢ|` positions, in some
order, then `c`), or `bⱼ > w > ⋯`. -/
def BallotForm {m n : ℕ} (S : Fin n → Finset (Fin m)) : VoterType m n → Ranking (m + 2) → Prop
  | .cw, r => (r (candC m) : ℕ) = 0 ∧ (r (candW m) : ℕ) = 1
  | .wc, r => (r (candW m) : ℕ) = 0 ∧ (r (candC m) : ℕ) = 1
  | .set i, r => (∀ j : Fin m, j ∈ S i ↔ (r (candB j) : ℕ) < (S i).card) ∧
      (r (candC m) : ℕ) = (S i).card
  | .elem j, r => (r (candB j) : ℕ) = 0 ∧ (r (candW m) : ℕ) = 1

/-- `P` is an election of Construction 4.28 for the Hitting Set instance `(B, S, k)` with
`B = Fin m`, `S : Fin n → Finset (Fin m)` and a positive integer `k ≤ m`: its voters can be labelled
so that there are `2(m − k) + 2n(k + 1) + 4` voters `c > w > ⋯`, `2n(k + 1) + 5` voters `w > c > ⋯`,
for each `i` exactly `2(k + 1)` voters `Sᵢ > c > ⋯`, and for each `j` exactly two voters
`bⱼ > w > ⋯`. -/
def IsConstruction428 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ}
    (P : Fin N → Ranking (m + 2)) : Prop :=
  1 ≤ k ∧ k ≤ m ∧
    ∃ τ : Fin N → VoterType m n,
      (Finset.univ.filter fun v => τ v = .cw).card = 2 * (m - k) + 2 * n * (k + 1) + 4 ∧
      (Finset.univ.filter fun v => τ v = .wc).card = 2 * n * (k + 1) + 5 ∧
      (∀ i, (Finset.univ.filter fun v => τ v = .set i).card = 2 * (k + 1)) ∧
      (∀ j, (Finset.univ.filter fun v => τ v = .elem j).card = 2) ∧
      ∀ v, BallotForm S (τ v) (P v)

end HHRControl.PV
