import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

open CookPvsNP ProjSchedTW.Complexity

/-! # The decision problems of §2.1, their languages, and the instances built in the proofs of
LEMMA 1 and THEOREM 1 (Garey, Tarjan & Wilfong 1988, pp. 332–336)

Instances are written over the published four-letter alphabet `BSym`, every number in binary
(`encNats`). -/

noncomputable section

/-! ## Even-odd partition (p. 332) -/

/-- The paper's PARTITION source problem (p. 333): a nonempty list of positive integers has
an equal-sum partition. The imported `partitionLang` also accepts zero entries and the empty
list, so the source language is restricted here to the instances printed in the paper. -/
def positivePartitionLang : Lang BSym :=
  { w | ∃ y : List ℕ, y ≠ [] ∧ (∀ v ∈ y, 0 < v) ∧ PartitionYes y ∧ w = encNats y }

/-- An instance `X = {x₁, …, x₂ₙ}` of even-odd partition (p. 332), given as the list
`[x₁, …, x₂ₙ]`: its length is even and positive (`n ∈ Z⁺`), its entries are positive integers,
and it is strictly increasing (`xᵢ < xᵢ₊₁`). -/
def EOInstance (x : List ℕ) : Prop :=
  Even x.length ∧ 0 < x.length ∧ (∀ v ∈ x, 0 < v) ∧ x.Pairwise (· < ·)

/-- The question of even-odd partition (p. 332): there is a set `X₁` of positions (its complement
is `X₂`) containing exactly one of the positions of `x₂ᵢ₋₁, x₂ᵢ` for every `i` (0-based positions
`2i − 2, 2i − 1`, i.e. two distinct positions with the same quotient by `2`), with
`∑_{X₁} x = ∑_{X₂} x`. -/
def EOYes (x : List ℕ) : Prop :=
  ∃ X₁ : Finset (Fin x.length),
    (∀ p q : Fin x.length, p ≠ q → p.val / 2 = q.val / 2 → (p ∈ X₁ ↔ q ∉ X₁)) ∧
    ∑ p ∈ X₁, x.get p = ∑ p ∈ X₁ᶜ, x.get p

/-- The even-odd partition language: binary codes `x₁ x₂ … x₂ₙ` of the yes-instances. -/
def evenOddLang : Lang BSym :=
  { w | ∃ x : List ℕ, EOInstance x ∧ EOYes x ∧ w = encNats x }

/-! ## Total discrepancy (p. 332) -/

/-- The binary code of a total discrepancy instance: the numbers `N, k, M₁, …, M_N, l₁, …, l_N`.
The first number `N` fixes how many follow, so the code determines the instance. -/
def tdCode (N k : ℕ) (M l : Fin N → ℕ) : List BSym :=
  encNats (N :: k :: (List.ofFn M ++ List.ofFn l))

/-- The total discrepancy language (p. 332): codes of the instances `N, k ∈ Z⁺`, `Mᵢ, lᵢ ∈ Z⁺`
(`1 ≤ i ≤ N`) for which some schedule `S` (real starting times) has
`cost(S) = ∑ᵢ |mᵢ(S) − Mᵢ| ≤ k`. -/
def tdLang : Lang BSym :=
  { w | ∃ (N k : ℕ) (M l : Fin N → ℕ), 0 < N ∧ 0 < k ∧ (∀ i, 0 < M i) ∧ (∀ i, 0 < l i) ∧
      TDYesReal (fun i => (l i : ℝ)) (fun i => (M i : ℝ)) (k : ℝ) ∧ w = tdCode N k M l }

/-! ## The instance EO of the proof of LEMMA 1 (p. 333) -/

/-- `eoAux a [yᵢ, yᵢ₊₁, …]` lists `x₂ᵢ₋₁ = a, x₂ᵢ = x₂ᵢ₋₁ + yᵢ`, then continues with
`x₂ᵢ₊₁ = x₂ᵢ + 1`. -/
def eoAux : ℕ → List ℕ → List ℕ
  | _, [] => []
  | a, y :: ys => a :: (a + y) :: eoAux (a + y + 1) ys

/-- The instance `X` of even-odd partition built from a partition instance `Y = [y₁, …, yₙ]`
(p. 333): `x₁ = 1`, `x₂ᵢ = x₂ᵢ₋₁ + yᵢ` (`1 ≤ i ≤ n`), `x₂ᵢ₊₁ = x₂ᵢ + 1` (`1 ≤ i < n`). -/
def eoOfPartition (y : List ℕ) : List ℕ := eoAux 1 y

/-! ## The instance D of the proof of THEOREM 1 (p. 336) -/

/-- The lengths of the `2n + 2` tasks `T₀, …, T₂ₙ₊₁` of the instance D built from an even-odd
instance `x = [x₁, …, x₂ₙ]` (`n = |x|/2`; position `i` of `Fin (2n+2)` is `Tᵢ`):
`l₀ = x₁ − 1`, `lᵢ = xᵢ` for `1 ≤ i ≤ 2n`, `l₂ₙ₊₁ = 2`. -/
def dLen (x : List ℕ) (i : Fin (2 * (x.length / 2) + 2)) : ℝ :=
  if i.val = 0 then (x.getD 0 0 : ℝ) - 1
  else if i.val ≤ 2 * (x.length / 2) then (x.getD (i.val - 1) 0 : ℝ)
  else 2

/-- `M = ∑ᵢ₌₀²ⁿ lᵢ/2`, the common preferred midtime of `T₀, …, T₂ₙ` in D (p. 336). -/
def dM (x : List ℕ) : ℝ :=
  ∑ i : Fin (2 * (x.length / 2) + 1), dLen x i.castSucc / 2

/-- The preferred midtimes of D (p. 336): `Mⱼ = M` for `0 ≤ j ≤ 2n` and
`M₂ₙ₊₁ = 2M + l₂ₙ₊₁/2`. -/
def dMid (x : List ℕ) (j : Fin (2 * (x.length / 2) + 2)) : ℝ :=
  if j.val ≤ 2 * (x.length / 2) then dM x
  else 2 * dM x + dLen x (Fin.last _) / 2

/-- The threshold of D (p. 336): `k = ∑ᵢ₌₁ⁿ (l₂ᵢ + l₂ᵢ₋₁)(n − i + 1/2) + (l₀)n`, computed from the
lengths of `T₀, …, T₂ₙ`. -/
def dK (x : List ℕ) : ℝ :=
  kStar (fun i : Fin (2 * (x.length / 2) + 1) => dLen x i.castSucc)

end

end GTWSched.NPC
