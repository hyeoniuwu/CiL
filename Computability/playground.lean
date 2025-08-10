import Computability.Constructions

open Nat

-- theorem h0' (h:x>0): x-1+1=x := by exact Nat.sub_add_cancel h

-- theorem 1p1 : (if 4=2 then 13 else 14) =14 := by
--   simp only [reduceEqDiff, ↓reduceIte]ℕ 

-- theorem asd : ¬ (s+1=0) := by exact add_one_ne_zero s
-- theorem asd (h:x>0): x-1+1=x := by exact Nat.sub_add_cancel h
-- have asd:n%2≤1 := by exact?
theorem bounds {m:ℕ} (h:Nat.pair m.l (s + 1) < k+1) : Nat.pair m.l (s + 1) ≤ k := by
  exact le_of_lt_succ h
theorem bruh {x y:ℕ} (h:¬x≤y) : x>y := by exact gt_of_not_le h


--  m.l≤n+4 := by
--     unfold m
--     simp [div2_val]
--     exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
--   have bounds_left_aux_1 : m.l<n+4+1
