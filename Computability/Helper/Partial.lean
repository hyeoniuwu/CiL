/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Data.Option.Basic
import Mathlib.Data.Part

-- helper functions for Part/Option
protected theorem isSome.bind {o : Option α} (h : o.isSome) (f : α → Option β) : o.bind f = f (o.get h) := by
  have : o = some (o.get h) := by exact Option.eq_some_of_isSome h
  ext b
  constructor
  intro h2
  rw [this] at h2
  simp only [Option.bind_some] at h2
  exact h2

  intro h2
  rw [this]
  simp only [Option.bind_some]
  exact h2
theorem ne_of_mem_imp_not_mem {y:Part ℕ} (h:x∈y) (h2:x≠z) : z∉y := by
  have aux: y=Part.some x := by exact Part.eq_some_iff.mpr h
  rw [aux]
  aesop
theorem opt_ne_of_mem_imp_not_mem {y:Option ℕ} (h:x∈y) (h2:x≠z) : z∉y := by
  aesop
lemma forall_mem_part {y:Part ℕ} (h1:y.Dom) (h2:∀ x ∈ y, x = c) : c∈y := by
  contrapose h2
  simp
  use y.get h1
  constructor
  exact Part.get_mem h1
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  have : y.get h1 ∈ y := by exact Part.get_mem h1
  contradiction
lemma forall_mem_option {y:Option ℕ} (h1:y.isSome) (h2:∀ x ∈ y, x = c) : c∈y := by
  contrapose h2
  simp
  use y.get h1
  constructor
  exact Option.eq_some_of_isSome h1
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  have : y.get h1 ∈ y := by exact Option.eq_some_of_isSome h1
  contradiction
theorem Part.eq_some_imp_dom {p:Part ℕ} : p=Part.some x → p.Dom := by
  intro a
  subst a
  exact trivial
theorem Part.mem_imp_dom {p:Part ℕ} : x∈p → p.Dom := λ h ↦ Part.eq_some_imp_dom (Part.eq_some_iff.mpr h)
theorem Part.dom_imp_some {x:Part ℕ} (h:x.Dom) : x=Part.some (x.get h) := by
  exact Part.get_eq_iff_eq_some.mp rfl
theorem Option.dom_imp_some {x:Option ℕ} (h:x.isSome) : x=some (x.get h) := by
  exact Option.eq_some_of_isSome h
theorem Option.isSome_iff_mem {o:Option β}: o.isSome ↔ (∃z,z∈o) := by
  have h1 := @Option.isSome_iff_exists β o
  simp [h1]
lemma isSome_iff_not_none : (¬o=Option.none)↔(o.isSome) := by
  apply Iff.intro
  · intro a
    simp [Option.eq_none_iff_forall_ne_some] at a
    rcases a with ⟨h1,h2⟩
    exact Option.isSome_of_mem h2
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [Option.isSome_none, Bool.false_eq_true]
lemma Part.eq_none_iff_forall_ne_some : o = Part.none ↔ ∀ a, o ≠ Part.some a := by
  have := (@Part.ne_none_iff _ o).not
  simp at this
  exact this
lemma Part.not_none_iff_dom : (¬o=Part.none)↔(o.Dom) := by
  apply Iff.intro
  · intro a
    simp [Part.eq_none_iff_forall_ne_some] at a
    rcases a with ⟨h1,h2⟩
    rw [h2]
    exact trivial
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    exact a
lemma Part.ne_of_get_ne {p1 p2:Part ℕ} {h1:p1.Dom} {h2:p2.Dom} (h:p1.get h1≠p2.get h2) : (p1≠p2) := by aesop
lemma Part.ne_of_get_ne' {p1:Part ℕ} {h1:p1.Dom} (h:p1.get h1≠x) : (p1≠Part.some x) := by aesop
lemma part_add {x y : ℕ}: Part.some x + Part.some y = Part.some (x+y) := by
  exact Part.some_add_some x y
