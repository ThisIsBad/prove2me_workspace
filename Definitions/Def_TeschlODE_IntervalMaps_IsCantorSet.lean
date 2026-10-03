import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.4, p. 299 (and §11.5, p. 302): a Cantor set is a compact set which is totally
disconnected and perfect (every point of it is an accumulation point of it). Total
disconnectedness is Mathlib's `IsTotallyDisconnected` (every preconnected subset is a
subsingleton); for subsets of `ℝ` this is the book's "contains no open subintervals"
(Problem 11.8). -/
def IsCantorSet {X : Type*} [TopologicalSpace X] (C : Set X) : Prop :=
  IsCompact C ∧ IsTotallyDisconnected C ∧ Preperfect C

end TeschlODE.IntervalMaps
