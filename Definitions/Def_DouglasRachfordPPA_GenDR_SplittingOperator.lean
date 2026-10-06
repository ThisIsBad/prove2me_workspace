import Mathlib

open InnerProductSpace

namespace DouglasRachfordPPA.GenDR

/-- The splitting operator of `A` and `B` with respect to `lam` (Eckstein–Bertsekas, p. 16):
`S_{lam,A,B} = {(v + lam b, u - v) | (u, b) ∈ B, (v, a) ∈ A, v + lam a = u - lam b}`. -/
def splittingOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam : ℝ) (A B : H → Set H) : H → Set H :=
  fun w => {s | ∃ u b v a : H, b ∈ B u ∧ a ∈ A v ∧ v + lam • a = u - lam • b ∧
    w = v + lam • b ∧ s = u - v}

/-- The set `Z*_lam = {u + lam b | b ∈ B u, -b ∈ A u}` (Theorem 5, p. 17). -/
def Zstar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam : ℝ) (A B : H → Set H) : Set H :=
  {z | ∃ u b : H, b ∈ B u ∧ -b ∈ A u ∧ z = u + lam • b}

/-- The Douglas–Rachford map `G = J_{lam A} ∘ (2 J_{lam B} - I) + (I - J_{lam B})` (p. 16),
built from given single-valued resolvent maps `JA`, `JB`. -/
def drMap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (JA JB : H → H) : H → H :=
  fun z => JA ((2 : ℝ) • JB z - z) + (z - JB z)

end DouglasRachfordPPA.GenDR
