/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.KP54

open Computability.Code
open Computability

@[irreducible] def c_c_rfind := c_comp.comp₂ c_rfind' (c_pair.comp₂ (c_const c_id) (c_zero))
@[cp] theorem c_c_rfind_prim : code_prim c_c_rfind := by
  unfold c_c_rfind; apply_cp
@[simp] theorem c_c_rfind_evp : evalp O c_c_rfind = fun x:ℕ => c2n (c_rfind x) := by simp [c_c_rfind, c_rfind]

def c_dovetailn :=
  c_c_rfind.comp $
  c_comp₂.comp₃
  (c_const c_if_eq')
  (c_comp₃.comp₄ (c_const c_evaln) (c_pair.comp₂ c_left (c_comp.comp₂ c_left c_right)) (c_c_const) (c_comp.comp₂ c_right c_right))
  (c_const (c_const 1))
@[cp] theorem c_dovetailn_prim : code_prim c_dovetailn := by
  unfold c_dovetailn; apply_cp
@[simp] theorem c_dovetailn_evp : evalp O c_dovetailn = λ x ↦ c2n (dovetailn $ n2c x) := by
  -- just doing simp [c_dovetailn, dovetailn] should work, but gives a kernel recursion error. why?
  -- this was fixed by moving simp from def of comp_n to the comp_n_evp theorems.
  simp [c_dovetailn, dovetailn]
def c_dovetail := c_comp.comp₂ c_left c_dovetailn
@[cp] theorem c_dovetail_prim : code_prim c_dovetail := by
  unfold c_dovetail; apply_cp
@[simp] theorem c_dovetail_evp : evalp O c_dovetail = λ x ↦ c2n (dovetail $ n2c x) := by
  simp [c_dovetail, dovetail]

def c_c_evals :=
  c_comp₃.comp₄
  (c_const c_evalo)
  (c_const c_c_evals_oracle)
  (c_const $ c_const c_evals_code)
  (c_const c_id)
@[cp] theorem c_c_evals_prim : code_prim c_c_evals := by
  unfold c_c_evals; apply_cp
@[simp] theorem c_c_evals_evp : evalp O c_c_evals x = c_evals := by simp [c_c_evals, c_evals]
def c_c_ifdom :=
  c_comp₂.comp₃ (c_const c_add) (c_comp.comp₂ c_zero left) (right)
@[cp] theorem c_c_ifdom_prim : code_prim c_c_ifdom := by
  unfold c_c_ifdom; apply_cp
@[simp] theorem c_c_ifdom_evp : evalp O c_c_ifdom = λ x ↦ c2n (c_ifdom x.l x.r) := by
  simp [c_c_ifdom, c_ifdom]
