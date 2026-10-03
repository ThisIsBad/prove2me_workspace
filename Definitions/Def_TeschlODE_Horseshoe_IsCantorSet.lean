import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §11.4, p. 299 and §11.5, p. 302: a Cantor set is a set which is compact, perfect
(every point of it is an accumulation point of it: Mathlib's `Preperfect`) and totally
disconnected in the sense of p. 302: any two distinct points `x, y` have disjoint open
neighborhoods `U ∋ x`, `V ∋ y` with `U ∪ V` covering the set (Mathlib's `IsTotallySeparated`).
For subsets of `ℝ` this agrees with "contains no open subintervals" of p. 299 (Problem 11.8). -/
def IsCantorSet {X : Type*} [TopologicalSpace X] (C : Set X) : Prop :=
  IsCompact C ∧ IsTotallySeparated C ∧ Preperfect C

end TeschlODE.Horseshoe
