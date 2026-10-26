import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A node set `S` with `2r + 1` elements for a strictly positive integer `r` (§2–§3, p. 126). -/
def IsOddSet (S : Finset V) : Prop :=
  ∃ r : ℕ, 1 ≤ r ∧ S.card = 2 * r + 1

open Classical in
/-- The finite family of all odd node sets `S` (`|S| = 2r + 1`, `r ≥ 1`), which index the dual
variables `z` (§3, p. 126). -/
noncomputable def oddSets : Finset (Finset V) :=
  Finset.univ.filter (fun S : Finset V => IsOddSet S)

/-- The number `r` of an odd set, `r = (|S| - 1)/2`, computed in `ℝ`. -/
noncomputable def rOf (S : Finset V) : ℝ :=
  ((S.card : ℝ) - 1) / 2

/-- The dual objective (5) (§3, p. 126): `U = ∑_v y v + ∑_S r z S`, the second sum over all odd
sets `S`. -/
noncomputable def U (y : V → ℝ) (z : Finset V → ℝ) : ℝ :=
  ∑ v, y v + ∑ S ∈ oddSets, rOf S * z S

/-- The left side of inequality (7) for an edge `e` with ends `v₁, v₂` (§3, p. 126):
`y v₁ + y v₂ + ∑ z S`, the sum over the odd sets `S` containing both `v₁` and `v₂`. -/
noncomputable def edgeDual (G : Graph V E) (y : V → ℝ) (z : Finset V → ℝ) (e : E) : ℝ :=
  Sym2.lift ⟨fun a b => y a + y b, fun a b => add_comm (y a) (y b)⟩ (G.ends e) +
    ∑ S ∈ oddSets.filter (fun S : Finset V => G.ends e ∈ S.sym2), z S

/-- Dual feasibility (6)–(7) (§3, p. 126): `y ≥ 0`, `z ≥ 0` on every odd set, and for every edge
`e`, `y v₁ + y v₂ + ∑_{S ∋ v₁, v₂} z S ≥ c e`. -/
def DualFeasible (G : Graph V E) (c : E → ℝ) (y : V → ℝ) (z : Finset V → ℝ) : Prop :=
  (∀ v, 0 ≤ y v) ∧ (∀ S ∈ (oddSets : Finset (Finset V)), 0 ≤ z S) ∧
    ∀ e, c e ≤ edgeDual G y z e

/-- The conditions (8)–(10) (§3, p. 127) for a matching `M` and a dual vector `⟨y, z⟩`:
(8) `y v = 0` for each node `v` which is not an endpoint of an edge in `M`;
(9) equality holds in (7) for each `e ∈ M`;
(10) for each odd set `S` with `z S > 0`, `S` contains both endpoints of `r` edges of `M`. -/
noncomputable def CompSlack (G : Graph V E) (c : E → ℝ) (M : Finset E) (y : V → ℝ)
    (z : Finset V → ℝ) : Prop :=
  (∀ v, (∀ e ∈ M, v ∉ G.ends e) → y v = 0) ∧
  (∀ e ∈ M, edgeDual G y z e = c e) ∧
  (∀ S ∈ (oddSets : Finset (Finset V)), 0 < z S →
    ((M.filter (fun e => G.ends e ∈ S.sym2)).card : ℝ) = rOf S)

end EdmondsMatching65.Polyhedron
