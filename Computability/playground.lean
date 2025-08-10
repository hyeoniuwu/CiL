import Computability.Constructions

open Nat

-- theorem h0' (h:x>0): x-1+1=x := by exact Nat.sub_add_cancel h

-- theorem 1p1 : (if 4=2 then 13 else 14) =14 := by
--   simp only [reduceEqDiff, ↓reduceIte]ℕ 

-- theorem asd : ¬ (s+1=0) := by exact add_one_ne_zero s
-- theorem asd (h:x>0): x-1+1=x := by exact Nat.sub_add_cancel h
-- have asd:n%2≤1 := by exact?
theorem bounds_aux_2 : Nat.pair m.l (s + 1) < Nat.pair (n + 4 + 1) (s + 1) := by
      exact pair_lt_pair_left (s+1) bounds_aux_1
have bounds : Nat.pair m.l (s + 1) ≤ k := by
