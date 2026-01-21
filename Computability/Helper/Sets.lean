/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park.
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Defs

import Mathlib.Tactic.Linarith

theorem nonempt_int_iff_not_subset_compl {α} (A B : Set α) : A ∩ B ≠ ∅ ↔ ¬ A ⊆ Bᶜ := by
  constructor
  · intro h1
    have : ∃ a:α, a ∈ A ∧ a ∈ B := by
      contrapose h1
      simp_all
      ext x : 1
      simp_all
    contrapose this
    simp at this ⊢
    exact fun x a ↦ this a
  · intro h1
    have : ∃ a:α, a ∈ A ∧ a ∈ B := by
      contrapose h1
      simp_all
      exact h1
    exact Set.nonempty_iff_ne_empty.mp this
theorem inf_imp_inhabited {A:Set ℕ} (h:A.Infinite) : ∃ y, y ∈ A := by
  simpa using h.nonempty
theorem setrange_card (i : ℕ) : {x | x ≤ i}.ncard = i + 1 := by
  have h_interval : {x | x ≤ i} = Set.Iio (i + 1) := by
    ext x
    simp [Nat.lt_succ_iff]
  rw [h_interval]
  rw [← Finset.coe_range (i + 1)]
  rw [Set.ncard_coe_finset]
  exact Finset.card_range (i + 1)

theorem big_imp_big_wit {i} {A : Set ℕ} : A.ncard > i → ∃ y ∈ A, y ≥ i := by
  contrapose
  simp only [ge_iff_le, not_exists, not_and, not_le, gt_iff_lt, not_lt]
  intro h
  have a0 : A ⊆ {x | x < i} := by aesop
  have a1 := Set.ncard_diff_add_ncard_of_subset a0
  have a2 : {x | x < i}.ncard = i := by
    cases i with
    | zero => simp
    | succ i =>
      have : {x | x < i + 1} = {x | x ≤ i} := by
        ext x
        simp only [Set.mem_setOf_eq]
        exact Nat.lt_add_one_iff
      rw [this]
      exact setrange_card i
  rw [a2] at a1
  linarith

theorem infinite_iff_unbounded {A : Set ℕ} : Set.Infinite A ↔ (∀ x, ∃ y∈A, y≥x) := by
  constructor
  · intro h x
    contrapose h
    simp at h
    simp
    exact Finite.Set.subset {i | i < x} h

  · intro h
    classical
    by_contra hfin
    simp at hfin
    have hA : Finite A := hfin
    have hne : A.Nonempty := by
      obtain ⟨y, hy, _⟩ := h 0
      exact ⟨y, hy⟩
    let m := (Set.Finite.toFinset hA).max' ((Set.Finite.toFinset_nonempty hA).mpr hne)
    let hm := Finset.le_max' (Set.Finite.toFinset hA)
    obtain ⟨y, hyA, hy⟩ := h (m+1+1)
    have : y ≤ m := hm y ((Set.Finite.mem_toFinset hA).mpr hyA)
    have a1 : y < m+1 := by exact Order.lt_add_one_iff.mpr this
    exact lt_asymm hy a1
