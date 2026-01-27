/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Basic
import Computability.Constructions.Primitive
import Computability.Constructions.Meta
import Computability.Order

open Computability
open Classical
open Computability.Code

@[simp] noncomputable def K0 (O : ℕ → ℕ) : ℕ → ℕ := λ n =>
  let part := eval O n.l n.r
  if h:part.Dom then part.get h+1 else 0
@[simp] noncomputable def K (O : ℕ → ℕ) : ℕ → ℕ := λ n =>
  let part := eval O n n
  if h:part.Dom then part.get h + 1 else 0
noncomputable abbrev jump (O:ℕ→ℕ) : ℕ → ℕ := K0 O

notation:10000 f"⌜" => jump f

namespace Computability.Code

def c_jump_decode (c:Code) := c_ite c c_diverge (c_pred.comp c)
@[simp] theorem c_jump_decode_ev (hc:code_total O c): eval O (c_jump_decode c) x = if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  simp [c_jump_decode]
  simp [c_ite_ev hc]
  congr
  simp [eval]
  if h:(eval O c x).Dom then
    rw [Part.dom_imp_some h]
    simp [-Part.some_get]
  else
    simp [Part.eq_none_iff'.mpr h]
theorem c_jump_decode_ev' (hc:code_total O c): eval O (c_jump_decode c) = fun x => if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  funext xs
  exact c_jump_decode_ev hc

theorem O_le_K0 (O:ℕ→ℕ) :  O ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr  -- changes goal to: ∃ c, eval (K0 O) c = O
  let q := oracle.comp (pair (c_const oracle) c_id)
  use c_jump_decode q

  have compute_total : code_total (K0 O) q := by
    apply prim_total
    apply_cp 60

  simp only [c_jump_decode_ev' compute_total]
  simp only [q]
  simp [eval, Seq.seq]
  exact rfl
theorem O_le_J (O:ℕ→ℕ) : O ≤ᵀᶠ O⌜ :=  O_le_K0 O

theorem K_leq_K0 (O:ℕ→ℕ) : (K O) ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr
  use oracle.comp $ pair c_id c_id

  simp [eval,Seq.seq]
  exact rfl
theorem K0_leq_K (O:ℕ→ℕ) : (K0 O) ≤ᵀᶠ (K O)  := by
  apply exists_code.mpr
  let compute := oracle.comp c_ev_const
  use compute

  have compute_total : code_total (K O) compute := by
    apply prim_total
    apply_cp 60

  unfold compute
  funext x
  rw [eval_total_comp compute_total]
  simp [eval, c_ev_const_ev']
theorem K_eq_K0 {O} : (K O)  ≡ᵀᶠ (K0 O) := ⟨K_leq_K0 O,K0_leq_K O⟩
theorem K0_eq_K {O} : (K0 O) ≡ᵀᶠ (K O)  := K_eq_K0.symm
theorem O_le_K (O:ℕ→ℕ) : O ≤ᵀᶠ (K O) := TuringReducible.trans (O_le_K0 O) (K0_leq_K O)

theorem jump_not_le_id (O:ℕ→ℕ) : ¬(O⌜ ≤ᵀᶠ O) := by
  intro h
  rcases exists_code.mp h with ⟨c_jO,hc_jO⟩
  let g := c_ite (c_jO.comp (pair c_id c_id)) zero c_diverge
  have fg : eval O g = fun (x:ℕ) => if (O⌜) (Nat.pair x x) = 0 then Part.some 0 else Part.none := by
    unfold g
    funext x
    have : code_total O (c_jO.comp (pair c_id c_id)) := by intro x; simp [eval,hc_jO,Seq.seq]
    simp [c_ite_ev this, eval, hc_jO, Seq.seq]
  -- why does this blow up lean?
  -- nvm, fixed [25-09-24 00:10:28]
  cases Classical.em (eval O g g).Dom with
  | inl hh =>
    have hh2 := hh
    rw [fg] at hh2
    simp [hh] at hh2
  | inr hh =>
    have hh2 := hh
    rw [fg] at hh2
    simp [hh] at hh2


theorem K_nle_O (O:ℕ→ℕ) : ¬(K O ≤ᵀᶠ O) := by
  intro h
  apply jump_not_le_id
  exact TuringReducible.trans (K0_leq_K O) h

theorem O_lt_K0 {O:ℕ→ℕ} : O <ᵀᶠ (K0 O) := ⟨O_le_J O,jump_not_le_id O⟩
