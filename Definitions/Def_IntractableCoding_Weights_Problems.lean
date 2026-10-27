import Mathlib

namespace IntractableCoding.Weights

/-- An instance of COSET WEIGHTS (Section III-A, p. 385): a binary `m × n` matrix `A`
(entries in GF(2) = `ZMod 2`), a binary vector `y` of length `n`, and a nonnegative
integer `w`. -/
structure CosetInstance where
  /-- number of rows of `A` (= length of the unknown row vector `x`) -/
  m : ℕ
  /-- number of columns of `A` (= length of `y`) -/
  n : ℕ
  A : Matrix (Fin m) (Fin n) (ZMod 2)
  y : Fin n → ZMod 2
  w : ℕ

/-- An instance of SUBSPACE WEIGHTS (Section III-B, p. 385): a binary `m × n` matrix `A`
and a nonnegative integer `w`. -/
structure SubspaceInstance where
  /-- number of rows of `A` (= length of the unknown row vector `x`) -/
  m : ℕ
  /-- number of columns of `A` -/
  n : ℕ
  A : Matrix (Fin m) (Fin n) (ZMod 2)
  w : ℕ

/-- COSET WEIGHTS property: there is a row vector `x` of Hamming weight `≤ w` with `xA = y`
(computed over GF(2)). -/
def CosetWeightsYes (I : CosetInstance) : Prop :=
  ∃ x : Fin I.m → ZMod 2, hammingNorm x ≤ I.w ∧ Matrix.vecMul x I.A = I.y

/-- SUBSPACE WEIGHTS property: there is a row vector `x` of Hamming weight exactly `w` with
`xA = 0` (computed over GF(2)). -/
def SubspaceWeightsYes (I : SubspaceInstance) : Prop :=
  ∃ x : Fin I.m → ZMod 2, hammingNorm x = I.w ∧ Matrix.vecMul x I.A = 0

/-- The bit of an element of GF(2). -/
def bitOf (a : ZMod 2) : Bool := decide (a = 1)

/-- Self-delimiting binary encoding of a natural number: each bit of `k` (least significant
first, `Nat.bits`) is preceded by a `true` marker, and a final `false` ends the number. -/
def encodeNatBinary (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- Encoding of a COSET WEIGHTS instance: `m` in unary, a separator, `n` in unary, a
separator, the `m n` entries of `A` row by row, the `n` entries of `y`, and `w` in binary. -/
def encodeCoset (I : CosetInstance) : List Bool :=
  List.replicate I.m true ++ [false] ++ List.replicate I.n true ++ [false] ++
    (List.finRange I.m).flatMap (fun i => (List.finRange I.n).map (fun j => bitOf (I.A i j))) ++
    (List.finRange I.n).map (fun j => bitOf (I.y j)) ++ encodeNatBinary I.w

/-- Encoding of a SUBSPACE WEIGHTS instance: `m` in unary, a separator, `n` in unary, a
separator, the `m n` entries of `A` row by row, and `w` in binary. -/
def encodeSubspace (I : SubspaceInstance) : List Bool :=
  List.replicate I.m true ++ [false] ++ List.replicate I.n true ++ [false] ++
    (List.finRange I.m).flatMap (fun i => (List.finRange I.n).map (fun j => bitOf (I.A i j))) ++
    encodeNatBinary I.w

end IntractableCoding.Weights
