/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.Simple

open Computability.Code
open Computability


-- def c_bdd_total_search (c:Code) := zero
-- theorem c_bdd_total_search_evp : evalp O (c_bdd_total_search c) x = 0 ↔ ∀ y≤x, evalp O c y = 0 := by
--   sorry


/-
`c_bdd_search c` is a primrec code that, on input `⟪x, l⟫`, evaluates:
  `[c](x,0)`
  `[c](x,1)`
  ... up to
  `[c](x,l)`,
  until one of the computations return a non-zero output. Suppose `[c](x,i)` is the first such computation.

  Then, `some ⟪i, [c](x,i)⟫` is returned.

  If no such value is found, `none` is returned.

  The code `c` must be total.
-/
def c_bdd_search (c:Code) := prec
  (
    pair zero $ c_eval.comp₂ c (pair c_id (c_const 0))
  ) -- abusing the fact that ⟪0,0⟫ = 0 = Option.none
  (
    let prev_comp := right.comp right
    let iP1 := left.comp right
    let computation := c_eval.comp₂ c (pair c_id iP1)

    c_ifz.comp₃ prev_comp
    (c_ifz.comp₃ computation zero (pair iP1 computation))
    prev_comp
    -- pair zero $ c_eval.comp₂ c (pair c_id iP1)
  )
theorem c_bdd_search_evp_total (h:code_total O c) : code_total O (c_bdd_search c) := by
  sorry
theorem c_bdd_search_evp_0 (h:code_total O c) :
  (eval O (c_bdd_search c) ⟪x, l⟫).get (c_bdd_search_evp_total h ⟪x, l⟫) = 0
  ↔
  ∀ i ≤ l, (eval O c ⟪x,i⟫).get (h ⟪x,i⟫) = 0 := by
  sorry

theorem c_bdd_search_evp_1 (h:code_total O c) :
  ⟪i, r⟫ ∈ ((eval O (c_bdd_search c) ⟪x, l⟫).get (c_bdd_search_evp_total h ⟪x, l⟫) : Option ℕ)
  ↔
  r ∈ ((eval O c ⟪x,i⟫).get (h ⟪x,i⟫) : Option ℕ) ∧ ∀ j ≤ i,(eval O c ⟪x,j⟫).get (h ⟪x,j⟫) = 0 := by
  sorry
--   by sorry

-- note. i can offload some of the conditions below to C, from C_aux
/-
`C_aux` is a code that checks, on input `⟪i, s, R⟫`, the following:
  1. i ≤ s
  2. ¬ fs_in R i
  3. ∃ x ∈ Wn ∅ i s, x > 2*i,
  and returns the minimal `x` in condition 3.
-/
def C_aux : Code := zero
theorem C_aux_evp_0 : x ∈ (evalp Nat.fzero C_aux ⟪⟪s,R⟫, i⟫ : Option ℕ) → i ≤ s ∧ ¬ fs_in R i ∧ x ∈ Wn ∅ i s ∧ x > 2*i := by
  sorry
theorem C_aux_evp_2 : (i ≤ s ∧ ¬ fs_in R i ∧ ∃ x ∈ Wn ∅ i s, x > 2*i) → (evalp Nat.fzero C_aux ⟪⟪s,R⟫, i⟫ : Option ℕ).isSome := by
  sorry
theorem C_aux_evp_1 : evalp Nat.fzero C_aux ⟪⟪s,R⟫, i⟫ = 0 ↔ (¬ fs_in R i → ∀ x ∈ Wn ∅ i s, x ≤ 2*i) := by
  sorry
theorem C_aux_total : code_total O C_aux := by
  sorry

def c_simple := zero
theorem c_simple_ev : W ∅ c_simple = Simple.A := by sorry

theorem exists_simple_set : ∃ A:Set ℕ, simpleIn ∅ A := by
  use Simple.A
  rw [←c_simple_ev]
  apply simpleInReq.mp
  constructor
  ·
    rw [c_simple_ev]
    exact Simple.A_CoInfinite
  intro c inf
  have a0 := Simple.P c
  simp at a0
  have := a0 inf
  rw [c_simple_ev]
  exact Set.nonempty_iff_ne_empty.mp (a0 inf)
