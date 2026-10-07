import Mathlib

namespace WarshallBool.Closure

/-- Warshall (1962), p. 11, first sentence: the boolean product `A ∧ B` of two `d × d` boolean
matrices, whose `(i, j)` entry is `∨_k (a_ik ∧ b_kj)`. Written with `∃ k` (boolean OR over `k`),
not with Mathlib's `Matrix` product over `Bool`, whose addition is XOR. -/
def boolProd {d : ℕ} (A B : Fin d → Fin d → Bool) : Fin d → Fin d → Bool :=
  fun i j => decide (∃ k, A i k = true ∧ B k j = true)

/-- Warshall (1962), p. 11, introduction display: the boolean powers `M^p`, with
`M^(p+1) = M^p ∧ M`. The base `boolPow M 0` is the boolean identity matrix, so that
`boolPow M 1 = M` (the page's `M^1 = M`); the exponent `0` is not on the page and is never used
in the sum `powerSum`. -/
def boolPow {d : ℕ} (M : Fin d → Fin d → Bool) : ℕ → Fin d → Fin d → Bool
  | 0 => fun i j => decide (i = j)
  | p + 1 => boolProd (boolPow M p) M

/-- Warshall (1962), p. 11, introduction display: `M′ = ∨_{p=1}^{d} M^p`, the boolean sum of
the boolean powers `M^1, …, M^d`; its `(i, j)` entry is `1` iff some `M^p` with `1 ≤ p ≤ d`
has `(i, j)` entry `1`. -/
def powerSum {d : ℕ} (M : Fin d → Fin d → Bool) : Fin d → Fin d → Bool :=
  fun i j => decide (∃ p ∈ (Finset.Icc 1 d : Finset ℕ), boolPow M p i j = true)

/-- Warshall (1962), p. 11, THEOREM: the chain definition of `M′`. `m′_ij = 1` iff `m_ij = 1`
(`ks = []`) or there are indices `k_1, …, k_n` with
`m_{i k_1} = m_{k_1 k_2} = ⋯ = m_{k_n j} = 1` (`ks = [k_1, …, k_n]`). -/
def ChainRel {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) : Prop :=
  ∃ ks : List (Fin d), List.IsChain (fun a c => M a c = true) (i :: ks ++ [j])

/-- Warshall (1962), p. 11, footnote 3: the recursive definition
`(m_ij)_0 = m_ij`, `(m_ij)_{n+1} = (m_ij)_n ∨ ((m_{i,n+1})_n ∧ (m_{n+1,j})_n)`.
The page's 1-based pivot `n + 1` is the 0-based index `⟨n, h⟩`; for `n ≥ d` (never used by the
footnote, which stops at `(m_ij)_d`) the matrix is left unchanged. -/
def warshallRec {d : ℕ} (M : Fin d → Fin d → Bool) : ℕ → Fin d → Fin d → Bool
  | 0 => M
  | n + 1 => fun i j =>
      if h : n < d then
        warshallRec M n i j || (warshallRec M n i ⟨n, h⟩ && warshallRec M n ⟨n, h⟩ j)
      else warshallRec M n i j

end WarshallBool.Closure
