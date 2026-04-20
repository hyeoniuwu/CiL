/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Use
open Oracle.Single.Code
open Classical

/-!
# Strings as oracles

In this file we define the evaluation function `evals`, which is like `eval` but takes a (finite) *string* as an oracle, rather than a set.

This is done via defining "clamped" evaluation, where a computation diverges if its use exceeds a set limit.

For the construction of these functions via codes, see Computability/Constructions/EvalString.lean.

-/

namespace Oracle.Single.Code

-- stands for "evaln clamped"
noncomputable def evalnc (O : ℕ→ℕ) (u : ℕ) : ℕ → Code → ℕ → Option ℕ := fun s c x ↦ do
  let use ← usen O c s x
  if use ≤ u  then evaln O s c x else Option.none
noncomputable def evalc (O : ℕ→ℕ) (u : ℕ) : Code → ℕ → Part ℕ := fun c x ↦ do
  let use ← use O c x
  if use ≤ u  then eval O c x else Part.none
theorem evalnc_imp_usen {O u s c x} (h : (evalnc O u s c x).isSome) : (usen O c s x).isSome := by
  unfold evalnc at h
  exact Option.isSome_of_isSome_bind h
theorem evalnc_prop_1 {O u s c x} (h : (evalnc O u s c x).isSome) : (usen O c s x).get (evalnc_imp_usen h)≤u := by
  unfold evalnc at h
  simp at h
  simp [isSome.bind (evalnc_imp_usen h)] at h
  contrapose h; simp [h]
theorem evalc_imp_use {O u c x} (h : (evalc O u c x).Dom) : (use O c x).Dom := by
  unfold evalc at h
  exact Part.Dom.of_bind h
theorem evalc_prop_1 {O u c x} (h : (evalc O u c x).Dom) : (use O c x).get (evalc_imp_use h)≤u := by
  unfold evalc at h
  simp at h
  rcases h with ⟨h0,h1⟩
  contrapose h1; simp [h1]
theorem evalc_prop_0 {O u c x} (h : (evalc O u c x).Dom) : evalc O u c x = eval O c x := by
  simp [evalc]
  simp [Part.Dom.bind <| evalc_imp_use h]
  simp [evalc_prop_1 h]
theorem evalc_prop_2 {O u c x} (h : (eval O c x).Dom) (h0 : (use O c x).get (e2u h)≤u) : (evalc O u c x).Dom := by
  simp [evalc]
  use e2u h
  simpa [h0]
theorem evalc_prop_3 {O u c x} (h : (eval O c x).Dom) (h0 : (use O c x).get (e2u h)≤u) : evalc O u c x=Part.some ((eval O c x).get h) := by
  simp [evalc]
  simp [Part.Dom.bind <| e2u h]
  simp [h0]
theorem evalc_prop_4 {O u c x h}: (use O c x).get h≤u ↔ (evalc O u c x).Dom :=
  ⟨
    fun h0 ↦ Part.eq_some_imp_dom <| evalc_prop_3 (u2e h) h0,
    fun h0 ↦ evalc_prop_1 h0
  ⟩

-- the b2n <| n2b is to simplify later proofs where evals will be compared against _.
def whatever := 0
noncomputable def evals (σ : List ℕ) (c : Code) (x : ℕ) := evalc (fun e ↦ b2n <| n2b <| σ.getD e whatever) σ.length c x
/-
the `whatever` *should* be unnecessary, because the evaluation is clamped by
`σ.length`, so out-of-bound values are never passed to the function.

I'm not sure how to remove it.
-/

end Oracle.Single.Code
