import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.GetD

open List

theorem reversed_range_indt (n) : (range (n + 1)).reverse = n :: (range n).reverse := by
  simpa only [reverse_eq_cons_iff, reverse_reverse] using range_succ
