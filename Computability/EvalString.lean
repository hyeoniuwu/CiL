import Computability.Use
open Nat.RecursiveIn.Code
open Classical

namespace Nat.RecursiveIn.Code

-- stands for "evaln clamped"
noncomputable def evalnc (O:ℕ→ℕ) (u:ℕ) : ℕ → Code → ℕ → Option ℕ := λ s c x ↦ do
  let use ← usen O c s x
  if use ≤ u  then evaln O s c x else Option.none
noncomputable def evalc (O:ℕ→ℕ) (u:ℕ) : Code → ℕ → Part ℕ := λ c x ↦ do
  let use ← use O c x
  if use ≤ u  then eval O c x else Part.none

theorem evalnc_imp_usen (h:(evalnc O u s c x).isSome): (usen O c s x).isSome := by
  unfold evalnc at h
  exact Option.isSome_of_isSome_bind h
theorem evalnc_prop_1 (h:(evalnc O u s c x).isSome): (usen O c s x).get (evalnc_imp_usen h)≤u := by
  unfold evalnc at h
  simp at h
  have := evalnc_imp_usen h
  simp [isSome.bind this] at h
  contrapose h
  simp [h]
theorem evalc_prop_0 (h:(evalc O u c x).Dom): evalc O u c x = eval O c x := by

    sorry
theorem evalc_imp_use (h:(evalc O u c x).Dom): (use O c x).Dom := by
  have := evalc_prop_0 h
  apply e2u
  rw [←this]
  exact h
theorem evalc_prop_1 (h:(evalc O u c x).Dom): (use O c x).get (evalc_imp_use h)≤u := by
  sorry



theorem evalc_prop''_rev_aux (h:(eval O c x).Dom) (h0:(use O c x).get (e2u h)≤u): (evalc O u c x).Dom := by
  sorry
theorem evalc_prop''_rev (h:(eval O c x).Dom) (h0:(use O c x).get (e2u h)≤u): evalc O u c x=Part.some ((eval O c x).get h) := by
  sorry
open Part
theorem evalc_prop''_rev2: (use O c x).get h≤u ↔ (evalc O u c x).Dom :=
  ⟨
    λ h0 ↦ Part.eq_some_imp_dom $ evalc_prop''_rev (u2e h) h0
    ,
    λ h0 ↦ evalc_prop_1 h0
  ⟩

end Nat.RecursiveIn.Code
