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
-- theorem bruh {x} (h:x>0) : (Nat.pair x y)>0 := by exact?
theorem pair_r_gt0 {x} : x>0→(Nat.pair y x)>0 := by
  contrapose
  simp
  intro h
  rw [show x=(pair y x).unpair.2 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
theorem pair_l_gt0 {x} : x>0→(Nat.pair x y)>0 := by
  contrapose
  simp
  intro h
  rw [show x=(pair x y).unpair.1 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
  
  -- apply unpair_zero


--  m.l≤n+4 := by
--     unfold m
--     simp [div2_val]
--     exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
--   have bounds_left_aux_1 : m.l<n+4+1
