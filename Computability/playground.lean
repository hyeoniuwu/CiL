import Computability.Constructions
open Nat

-- theorem h0' (h:x>0): x-1+1=x := by exact Nat.sub_add_cancel h

-- theorem 1p1 : (if 4=2 then 13 else 14) =14 := by
--   simp only [reduceEqDiff, ↓reduceIte]

theorem asd : ¬ (s+1=0) := by exact add_one_ne_zero s
