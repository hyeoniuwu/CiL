/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Primitive
import Computability.Helper.Partial

/-!
# Construction of basic primitive recursive functions on option types

This file defines basic primitive recursive codes for basic functions on option types.

-/

open Nat
open Denumerable
open Encodable
open List

section isSome
namespace Computability.Code
def c_isSome := c_sg'
@[cp] theorem c_isSome_prim : code_prim c_isSome := by unfold c_isSome; apply_cp
@[simp] theorem c_isSome_evp {O : ℕ → ℕ} : evalp O c_isSome = fun o => b'2n $ (n2o o).isSome := by
  funext x; cases x <;> simp [c_isSome, b'2n, n2o]
@[simp] theorem c_isSome_ev:eval O c_isSome = fun o => b'2n $ (n2o o).isSome := by rw [← evalp_eq_eval c_isSome_prim]; simp only [c_isSome_evp];
end Computability.Code
end isSome

section opt_iget
namespace Computability.Code
def c_opt_iget := c_pred
@[cp] theorem c_opt_iget_prim : code_prim c_opt_iget := by unfold c_opt_iget; apply_cp
@[simp] theorem c_opt_iget_evp {O : ℕ → ℕ} : evalp O c_opt_iget o = Option.getD (n2o o) 0 := by
  simp [c_opt_iget]
  by_cases ho:o=0
  · simp [ho];
  · rcases exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho) with ⟨k,hk⟩
    simp [←hk]
@[simp] theorem iget_evp_2 (h:o≠0) : Option.getD (n2o o) 0 = o-1:= by
  rw [Eq.symm (succ_pred_eq_of_ne_zero h)]
  exact rfl

@[simp] theorem c_opt_iget_ev:eval O c_opt_iget o = Option.getD (n2o o) 0 := by simp [← evalp_eq_eval c_opt_iget_prim]
end Computability.Code
end opt_iget
section opt_getD
namespace Computability.Code
def c_opt_getD := c_ifz.comp₃ left right (c_opt_iget.comp left)
@[cp] theorem c_opt_getD_prim : code_prim c_opt_getD := by unfold c_opt_getD; apply_cp
@[simp] theorem c_opt_getD_evp {O : ℕ → ℕ} : evalp O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by
  simp [c_opt_getD]
  by_cases ho:o=0
  · simp [ho];
  · rcases exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho) with ⟨k,hk⟩
    simp [←hk]
@[simp] theorem c_opt_getD_ev:eval O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by simp [← evalp_eq_eval c_opt_getD_prim]
end Computability.Code
end opt_getD

section opt_none
namespace Computability.Code
def c_opt_none := c_const 0
@[cp] theorem c_opt_none_prim : code_prim c_opt_none := by
  unfold c_opt_none; apply_cp
@[simp] theorem c_opt_none_evp {O : ℕ → ℕ} : evalp O c_opt_none o = o2n Option.none := by
  simp [c_opt_none]
@[simp] theorem c_opt_none_ev {O : ℕ → ℕ} : n2o <$> (eval O c_opt_none o) = (Option.none : Option ℕ) := by
  simp [← evalp_eq_eval c_opt_none_prim]
end Computability.Code
end opt_none

section opt_bind
namespace Computability.Code
def c_opt_bind (cf cg:Code) :=  c_ifz.comp₃ cf zero (cg.comp₂ c_id (c_opt_iget.comp cf))
@[cp] theorem c_opt_bind_prim(hcf:code_prim cf) (hcg:code_prim cg) : code_prim (c_opt_bind cf cg) := by unfold c_opt_bind; apply_cp
@[simp] theorem c_opt_bind_evp {O : ℕ → ℕ} : evalp O (c_opt_bind cf cg) x =
  o2n do
    let t ← n2o (evalp O cf x)
    let r ← n2o (evalp O cg (Nat.pair x t))
    return r
:= by
  simp [c_opt_bind,evalp]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp [h]
    simp [isSome.bind $ hnat_6 h]
    congr
    exact Eq.symm hnat_7
end Computability.Code
end opt_bind

section opt_bind'
namespace Computability.Code
def c_opt_bind' (cf cg:Code) :=  c_ifz.comp₃ cf zero cg
@[cp] theorem c_opt_bind'_prim(hcf:code_prim cf) (hcg:code_prim cg) : code_prim (c_opt_bind' cf cg) := by unfold c_opt_bind'; apply_cp
@[simp] theorem c_opt_bind'_evp {O : ℕ → ℕ} : evalp O (c_opt_bind' cf cg) x =
  o2n do
    let _ ← n2o (evalp O cf x)
    let r ← n2o (evalp O cg x)
    return r
:= by
  simp [c_opt_bind',evalp]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp [h]
    simp [isSome.bind $ hnat_6 h]
end Computability.Code
end opt_bind'

section part_bind
namespace Computability.Code
def c_part_bind (cf cg:Code) := cg.comp₂ c_id cf
@[simp] theorem c_part_bind_ev {O : ℕ → ℕ} : eval O (c_part_bind cf cg) x =
  do
    let t ← eval O cf x
    let r ← eval O cg (Nat.pair x t)
    return r := by
 simp [c_part_bind, Seq.seq]

end Computability.Code
end part_bind
