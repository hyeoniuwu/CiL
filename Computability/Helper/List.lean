import Mathlib.Data.List.Basic

open List

theorem rr_indt (n): (range (n + 1)).reverse = n :: (range n).reverse := by
  simp only [reverse_eq_cons_iff, reverse_reverse]
  exact range_succ

theorem rr_mem_bound {i} (h : i ∈ (range (ro + 1)).reverse) : i≤ro := by
  contrapose h
  simpa using h

lemma listrevlem (h:∃ l'':List ℕ, l'' ++ l' = (range x).reverse) : ∃ y, l'=(range y).reverse∧y≤x := by
  rcases h with ⟨h1,h2⟩
  induction h1 generalizing x with
  | nil =>
    simp at h2
    aesop
  | cons head tail ih =>
    simp at h2
    have : x>0 := by
      grind only [=_ cons_append, = range_zero, reverse_nil, → eq_nil_of_append_eq_nil]
    have : tail ++ l' = (range (x-1)).reverse := by
      rw [show x=x-1+1 from (Nat.sub_eq_iff_eq_add this).mp rfl] at h2
      simp [rr_indt] at h2
      simp_all only [reverse_inj, gt_iff_lt]
    have := @ih (x-1) this

    grind
lemma listrevlem2 (h:∃ l'':List ℕ, l'' ++ l' = (range x).reverse) (h2:a∈l') : a<x := by
  have := listrevlem h
  grind

theorem list_access_small {i} {l1 l2 : List α} (h:i<l1.length) : (l1 ++ l2)[i]? = (l1)[i]? := by
    simp [getElem?_pos, List.getElem?_append, h]

@[simp] theorem getI_eq_getElem {l:List ℕ} {h:i<l.length} : l.getI i = l[i] := by
  unfold List.getI
  simp [h]

@[simp] theorem map_getI :
    (List.map f (List.range (s + 1))).getI x = if x < s+1 then f x else 0 := by
  unfold List.getI
  cases Classical.em (x<s+1) with
  | inl h => simp [h]
  | inr h => simp [h]
