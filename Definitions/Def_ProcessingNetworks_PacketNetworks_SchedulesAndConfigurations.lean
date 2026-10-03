import Mathlib

namespace ProcessingNetworks.PacketNetworks

/-- Link configuration data (Section 12.2): `K` links, a `K × J` link usage matrix `A` with a
single `1` in each column (`hA`: activity `j` uses exactly one link), and a finite set `C` of
feasible link configurations. `C`/`S` are taken as `Finset`s throughout this mission — every
worked example in the book has finitely many configurations and (since each column of `A` has a
single `1`, so `As ≤ c` bounds each `s j` by the capacity of `j`'s own link) finitely many
schedules per configuration; this is a standing convention, not a per-item hypothesis, documented
in `MODERATION_NOTES.md`. -/
structure LinkConfigData (J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  hA : ∀ j : Fin J, ∃! k : Fin K, A k j = 1
  hA0 : ∀ j : Fin J, ∀ k : Fin K, A k j ≠ 1 → A k j = 0
  C : Finset (Fin K → ℕ)

/-- Assumption 12.4, Dai & Harrison p. 228 (PDF p. 244): for each link `k` there exists a
feasible configuration giving it positive capacity. -/
def SatisfiesAssumption124 {J K : ℕ} (cfg : LinkConfigData J K) : Prop :=
  ∀ k : Fin K, ∃ c ∈ cfg.C, 0 < c k

/-- The packet availability / capacity constraint `As ≤ c` (Eq. 12.3 specialized with a fixed
configuration `c` in place of a general capacity vector): schedule `s` is available under
configuration `c`. -/
def scheduleAvailable {J K : ℕ} (cfg : LinkConfigData J K) (c : Fin K → ℕ) (s : Fin J → ℕ) : Prop :=
  ∀ k : Fin K, (cfg.A.mulVec (fun j => (s j : ℝ))) k ≤ (c k : ℝ)

/-- `Sc` (Eq. 12.9), characterized rather than constructed: `Sc` is *the* schedule set for
configuration `c` iff it contains exactly the schedules available under `c`. -/
def IsScheduleSetAt {J K : ℕ} (cfg : LinkConfigData J K) (c : Fin K → ℕ)
    (Sc : Finset (Fin J → ℕ)) : Prop :=
  ∀ s : Fin J → ℕ, s ∈ Sc ↔ scheduleAvailable cfg c s

/-- `S := ⋃_{c∈C} Sc` (Eq. 12.10), characterized rather than constructed, matching
`IsScheduleSetAt`'s convention. -/
def IsScheduleSet {J K : ℕ} (cfg : LinkConfigData J K) (S : Finset (Fin J → ℕ)) : Prop :=
  ∀ s : Fin J → ℕ, s ∈ S ↔ ∃ c ∈ cfg.C, scheduleAvailable cfg c s

/-- `S` is monotone (Eq. 12.4): every schedule dominated (componentwise) by a feasible schedule
is itself feasible. -/
def IsMonotoneScheduleSet {J : ℕ} (S : Finset (Fin J → ℕ)) : Prop :=
  ∀ s ∈ S, ∀ s' : Fin J → ℕ, (∀ j, s' j ≤ s j) → s' ∈ S

end ProcessingNetworks.PacketNetworks
