import Definitions.Def_ZudilinZetaSetup

namespace ZudilinZeta
theorem zudilin_series_summable (P : Params) (n : ℕ) (hn : 0 < n) :
    Summable (fun t : ℕ => iteratedDeriv (P.r - 1) (R P n) (t : ℝ)) := by sorry
end ZudilinZeta
