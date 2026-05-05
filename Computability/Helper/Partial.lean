/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Basic

import Mathlib.Data.Option.Basic
import Mathlib.Data.Part

-- helper functions for Part/Option
protected theorem Option.isSome.bind {α β} {o : Option α}
    (h : o.isSome) (f : α → Option β) :
    o.bind f = f (o.get h) := by
  simp (config := {singlePass := true}) only [Option.eq_some_of_isSome h]
  ext b
  constructor
  · intro h2
    simp only [Option.bind_some] at h2
    exact h2
  intro _
  simpa only [Option.bind_some]
theorem Part.mem_imp_dom {x} {p : Part ℕ} : x ∈ p  → p.Dom :=
  fun h => by simp [Part.eq_some_iff.mpr h]
theorem Option.isSome_iff_mem {β} {o : Option β} : o.isSome ↔ (∃z ,z∈o) := by
  have h1 := @Option.isSome_iff_exists β o
  simp [h1]
lemma Part.eq_none_iff_forall_ne_some {α} {o : Part α} : o = Part.none ↔ ∀ a, o ≠ Part.some a := by
  simpa using (@Part.ne_none_iff _ o).not
lemma Part.not_none_iff_dom {α} {o : Part α} : (o ≠ Part.none) ↔ (o.Dom) := by
  apply Iff.intro
  · intro a
    simp only [eq_none_iff_forall_ne_some, ne_eq, not_forall, not_not] at a
    rcases a with ⟨h1,h2⟩
    rw [h2]
    exact trivial
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    exact a
lemma Part.ne_some_of_get_ne {x : ℕ} {p1 : Part ℕ} {h1 : p1.Dom} (h : p1.get h1 ≠ x) :
  p1 ≠ Part.some x := by aesop

-- option
open Nat Denumerable Encodable List
private lemma ge_0_rw {x} (h2 : ¬x=0) : x=x-1+1 := (succ_pred_eq_of_ne_zero h2).symm
theorem hnat_0 {o : Option ℕ} (ho : o.isSome) : ¬ o2n o = 0 := by
  rw [Option.eq_some_of_isSome ho]
  exact add_one_ne_zero (Encodable.encode (o.get ho))
theorem hnat_1 {o : Option ℕ} (ho : ¬ o = Option.none) : ¬ o2n o = 0 := by
  exact hnat_0 (Option.isSome_iff_ne_none.mpr ho)
theorem hnat_2 {o : Option ℕ} (ho : o.isSome) : (o2n o) - 1 = o.get ho := by
  simp (config := {singlePass := true}) [Option.eq_some_of_isSome ho]
  exact rfl
theorem isSome_of_n2o {i} (h : i ≠ 0) : (n2o i).isSome := by
  rewrite [(succ_pred_eq_of_ne_zero h).symm]; rfl
theorem getD_eq_get {x} {o : Option ℕ} (h : o.isSome) : o.getD x = o.get h :=
  Eq.symm (Option.get_eq_getD o)
theorem o2n_a0 {x} : o2n x = 0 ↔ x = Option.none := by
  constructor
  · intro h
    contrapose h
    exact hnat_1 h
  · intro h
    simp [h]
theorem hnat_10 {x} (h : o2n x ≠ 0) : x.isSome := by
  simpa using isSome_of_n2o h
theorem hnat_11 {x : Option ℕ} (h : x.isSome) : x = some (o2n x - 1) := by
  rw [hnat_2 h];
  exact Option.eq_some_of_isSome h
theorem hnat_12 {a} {x : ℕ} (h : n2o x = some a) : x-1 = a := by
  have : (n2o x).isSome := Option.isSome_of_mem h
  have := hnat_11 this
  rw [this] at h
  simp at h
  assumption
