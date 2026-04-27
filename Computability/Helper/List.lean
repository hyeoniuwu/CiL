import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.GetD

open List

theorem reversed_range_indt (n) : (range (n + 1)).reverse = n :: (range n).reverse := by
  simpa only [reverse_eq_cons_iff, reverse_reverse] using range_succ
@[simp] theorem map_getI {f s x} :
    (List.map f (List.range (s + 1))).getI x = if x < s+1 then f x else 0 := by
  unfold List.getI
  cases Classical.em (x<s+1) with
  | inl h => simp [h]
  | inr h => simp [h]
-- theorem getI_eq_getElem {i} {l : List ℕ} {h : i < l.length} :
--     l.getI i = l[i] := by
--   exact List.getI_eq_getElem l h
--   unfold List.getI
--   simp [h]
