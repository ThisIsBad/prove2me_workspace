import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.SWB

/-- Method 1 of Section 3: shift the digits and append
`x_(r+1-s) - x_1 - c` modulo `b`, borrowing exactly when negative. -/
def step (b : ℕ) (L : CarryRNG.AWC.Lags) (_hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) : CarryRNG.AWC.State b L.r := by
  have hs := L.hs
  have hsr := L.hsr
  let a : ℕ := (z.x ⟨L.r - L.s, by omega⟩).val
  let d : ℕ := (z.x ⟨0, by omega⟩).val
  let borrow : Bool := a < d + z.c.val
  let newDigit : ℕ := if borrow then a + b - (d + z.c.val) else a - (d + z.c.val)
  refine ⟨fun i => if h : i.val + 1 < L.r then z.x ⟨i.val + 1, h⟩ else ⟨newDigit, ?_⟩,
    ⟨if borrow then 1 else 0, by split <;> omega⟩⟩
  have ha : a < b := (z.x ⟨L.r - L.s, by omega⟩).isLt
  have hd : d < b := (z.x ⟨0, by omega⟩).isLt
  have hc : z.c.val < 2 := z.c.isLt
  by_cases hborrow : a < d + z.c.val
  · simp [newDigit, borrow, hborrow]
    omega
  · simp [newDigit, borrow, hborrow]
    omega

end CarryRNG.SWB
