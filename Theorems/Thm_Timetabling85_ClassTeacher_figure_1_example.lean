import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- The requirement matrix of Figure 1 (de Werra 1985, pp. 153–154): two classes, three teachers. -/
theorem figure_1_example :
    IsCT3 (m := 2) (n := 3) ![![1, 2, 4], ![3, 0, 2]] 3
      (fun i j k => (![![![0, 0, 2], ![1, 0, 0]],
                       ![![0, 1, 1], ![1, 0, 1]],
                       ![![1, 1, 1], ![1, 0, 1]]] : Fin 3 → Fin 2 → Fin 3 → ℕ) k i j) := by sorry

end Timetabling85.ClassTeacher

