/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Basic
import Computability.Constructions.Primitive
import Computability.Constructions.Meta
import Computability.Order

/-!
# Jump.lean

This file defines the jump operator on total functions, and basic reducibility results
involving the jump.

## Main declarations
- `K0` : the K₀ operator, on total functions
- `K`  : the K operator, on total functions
- `jump`: the jump operator, on total functions

- `K0_eq_K` : asserts that K and K0 are of the same degree
- `not_jump_le` : asserts that the jump of an oracle is strictly above the oracle

-/

open Computability
open Oracle.Single

open Classical in
@[simp] noncomputable def K0 (O : ℕ → ℕ) : ℕ → ℕ := fun n =>
  let part := eval O n.l n.r
  if h : part.Dom then (part.get h) + 1 else 0
open Classical in
@[simp] noncomputable def K (O : ℕ → ℕ) : ℕ → ℕ := fun n =>
  let part := eval O n n
  if h : part.Dom then (part.get h) + 1 else 0
noncomputable abbrev jump (O : ℕ → ℕ) : ℕ → ℕ := K0 O

notation : 10000 f"⌜" => jump f

namespace Oracle.Single.Code

def c_jump_decode (c : Code) := c_ite c c_diverge (c_pred.comp c)
open Classical in
@[simp, ev_simps] theorem c_jump_decode_ev {O c x} (hc : code_total O c) :
    eval O (c_jump_decode c) x =
    if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  simp only [c_jump_decode, ev_simps, Part.map_eq_map]
  simp only [c_ite_ev hc, c_diverge_ev]
  congr
  simp only [ev_simps, Part.bind_eq_bind]
  if h : (eval O c x).Dom then
    rw [Part.eq_some_of_dom h]
    simp [-Part.some_get]
  else
    simp [Part.eq_none_iff'.mpr h]
open Classical in
@[simp, ev_simps] theorem c_jump_decode_ev' {O c} (hc : code_total O c) :
    eval O (c_jump_decode c) =
    fun x => if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  funext xs
  exact c_jump_decode_ev hc

theorem le_K0 (O : ℕ → ℕ) :  O ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr  -- changes goal to: ∃ c, eval (K0 O) c = O
  let q := oracle.comp (pair (c_const oracle) c_id)
  use c_jump_decode q
  have compute_total : code_total (K0 O) q := by apply prim_total; apply_cp
  simpa [compute_total, q, ev_simps, Seq.seq] using by exact rfl
theorem le_jump (O : ℕ → ℕ) : O ≤ᵀᶠ O⌜ := le_K0 O

open Classical in
theorem K_le_K0 (O : ℕ → ℕ) : (K O) ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr
  use oracle.comp <| pair c_id c_id
  simpa [ev_simps, Seq.seq] using by exact rfl

open Classical in
theorem K0_le_K (O : ℕ → ℕ) : (K0 O) ≤ᵀᶠ (K O) := by
  apply exists_code.mpr
  let compute := oracle.comp c_ev_const
  use compute
  have compute_total : code_total (K O) compute := by apply prim_total; apply_cp
  funext x
  rw [eval_total_comp compute_total]
  simp [eval, c_ev_const_ev']
theorem K_eq_K0 {O : ℕ → ℕ} : (K O)  ≡ᵀᶠ (K0 O) := ⟨K_le_K0 O,K0_le_K O⟩
theorem K0_eq_K {O : ℕ → ℕ} : (K0 O) ≡ᵀᶠ (K O) := K_eq_K0.symm
theorem le_K (O : ℕ → ℕ) : O ≤ᵀᶠ (K O) := TuringReducible.trans (le_K0 O) (K0_le_K O)

open Classical in
theorem not_jump_le (O : ℕ → ℕ) : ¬(O⌜ ≤ᵀᶠ O) := by
  intro h
  rcases exists_code.mp h with ⟨c_jO,hc_jO⟩
  let g := c_ite (c_jO.comp (pair c_id c_id)) zero c_diverge
  have fg :
      eval O g =
      fun (x : ℕ) => if (O⌜) (Nat.pair x x) = 0
        then Part.some 0
        else Part.none := by
    unfold g
    funext x
    have : code_total O (c_jO.comp (pair c_id c_id)) := by intro x; simp [eval,hc_jO,Seq.seq]
    simp [c_ite_ev this, eval, hc_jO, Seq.seq]
  cases Classical.em (eval O g g).Dom with
  | inl hh => have hh2 := hh; rw [fg] at hh2; simp [hh] at hh2
  | inr hh => have hh2 := hh; rw [fg] at hh2; simp [hh] at hh2

theorem not_K_le (O : ℕ → ℕ) : ¬(K O ≤ᵀᶠ O) :=
  fun h => not_jump_le O (TuringReducible.trans (K0_le_K O) h)

theorem lt_K0 {O : ℕ → ℕ} : O <ᵀᶠ (K0 O) := ⟨le_jump O,not_jump_le O⟩

end Oracle.Single.Code
