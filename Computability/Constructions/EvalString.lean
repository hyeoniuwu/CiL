/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Use
import Computability.Constructions.Basic
import Computability.Constructions.Meta
import Computability.EvalString

open Nat

section evalnc
namespace Computability.Code
def c_evalnc :=
  let u0 := left.comp left
  let s0 := right.comp left
  let c0 := left.comp right
  let x0 := right.comp right
  let bind_prev := left
  let u1 := u0.comp bind_prev
  let s1 := s0.comp bind_prev
  let c1 := c0.comp bind_prev
  let x1 := x0.comp bind_prev

  c_opt_bind
  (c_usen.comp₃ x0 c0 s0) $
  c_if_le_te.comp₄ right u1 (c_evaln.comp₃ x1 c1 s1) zero
@[cp] theorem c_evalnc_prim : code_prim c_evalnc := by unfold c_evalnc; apply_cp 90
@[simp] theorem c_evalnc_evp:evalp O c_evalnc ⟪u,s,c,x⟫ = o2n (evalnc O u s c x) := by
  simp [c_evalnc,evalp];
  simp [evalnc]
  congr; funext a_0
  simp only [apply_ite]
  aesop
@[simp] theorem c_evalnc_ev : eval O c_evalnc ⟪u,s,c,x⟫ = o2n (evalnc O u s c x) := by simp [← evalp_eq_eval c_evalnc_prim]
end Computability.Code
end evalnc

section evalc
namespace Computability.Code
def c_evalc :=
  let u0 := left
  let c0 := left.comp right
  let x0 := right.comp right
  let bind_prev := left
  let u1 := u0.comp bind_prev
  let c1 := c0.comp bind_prev
  let x1 := x0.comp bind_prev

  c_part_bind
  (c_use.comp₂ c0 x0) $
  c_if_le_te' right u1 (c_eval.comp₂ c1 x1) c_diverge

@[simp] theorem c_evalc_ev: eval O c_evalc ⟪u, c, x⟫ = (evalc O u c x) := by
  unfold c_evalc
  simp [eval, Seq.seq, evalc]
  if h:(use O (n2c c) x).Dom then
    simp [Part.Dom.bind h]
    have hc1 : code_total O right := by exact right_total
    have hc2 : code_total O (left.comp left) := by exact total_comp_of hc1 hc1
    simp [c_if_le_te'_ev hc1 hc2]
    simp [eval, Seq.seq]
  else
    simp [Part.eq_none_iff'.mpr h]

end Computability.Code
end evalc

section evals
namespace Computability.Code
section c_evalo
def c_evalo :=
  let o := left
  let c := left.comp right
  let x := right.comp right
  c_eval.comp₂ (c_replace_oracle.comp₂ o c) x
theorem c_evalo_ev (ho:code_total O o) : eval O c_evalo ⟪o, c, x⟫ = eval (λ t ↦ (eval O o t).get (ho t)) c x := by
  simp [c_evalo]
  simp [eval,Seq.seq]
  rw [@eval_replace_oracle_prop O o c ho]
end c_evalo

section c_evals_oracle
def c_evals_oracle (o:Code):= c_sg.comp $ c_list_getD.comp₃ (c_const o) c_id (c_const whatever)
@[cp] theorem c_evals_oracle_prim : code_prim (c_evals_oracle o) := by unfold c_evals_oracle; apply_cp
theorem c_evals_oracle_evp : evalp O (c_evals_oracle o) =
λ x:ℕ ↦ b2n $ n2b $ (n2l o).getD x whatever := by
  simp [c_evals_oracle]
  funext x
  split
  next h =>
    simp [h]; rfl
  next h =>
    rw [Eq.symm (succ_pred_eq_of_ne_zero h)]
    simp [n2b]
    exact rfl
theorem c_evals_oracle_ev : eval O (c_evals_oracle o) =
λ x:ℕ ↦ b2n $ n2b $ (n2l o).getD x whatever
:= by
  simp [← evalp_eq_eval c_evals_oracle_prim]
  simp [c_evals_oracle_evp]
end c_evals_oracle

section c_c_evals_oracle
def c_c_evals_oracle := c_comp.comp₂ (c_const c_sg) (c_comp₃.comp₄ (c_const c_list_getD) (c_c_const.comp left) (c_const c_id) (c_const $ c_const whatever))
@[cp] def c_c_evals_oracle_prim : code_prim c_c_evals_oracle := by unfold c_c_evals_oracle; apply_cp
@[simp] theorem c_c_evals_oracle_evp : evalp O c_c_evals_oracle ⟪o,c,x⟫ =
c2n (c_evals_oracle o) := by simp [c_c_evals_oracle, c_evals_oracle]
theorem c_c_evals_oracle_ev : eval O c_c_evals_oracle ⟪o,c,x⟫ = c2n (c_evals_oracle o) := by simp [← evalp_eq_eval c_c_evals_oracle_prim]
end c_c_evals_oracle

section c_evals
def c_evals_code := c_evalc.comp₂ (c_list_length.comp left) right
theorem c_evals_code_ev : eval O c_evals_code ⟪o,c,x⟫ = evalc O (n2l o).length c x := by
  simp [c_evals_code]
  simp [eval, Seq.seq]
def c_evals := c_evalo.comp₃
  c_c_evals_oracle
  (c_const c_evals_code)
  c_id
@[simp] theorem c_evals_ev: eval O c_evals ⟪o,c,x⟫ = (evals (n2l o) c x) := by
  unfold evals
  unfold c_evals
  simp [Seq.seq]
  have t1 : code_total O c_c_evals_oracle := prim_total c_c_evals_oracle_prim
  have : code_total O ((eval O c_c_evals_oracle ⟪o,c,x⟫).get (t1 ⟪o,c,x⟫)) := by
    simp [c_c_evals_oracle_ev]
    apply prim_total
    exact c_evals_oracle_prim
  simp [Part.Dom.bind $ t1 ⟪o,c,x⟫]
  have := @c_evalo_ev O _ (c_evals_code.c2n) ⟪o,c,x⟫ this
  simp at this
  simp [this]
  simp [c_c_evals_oracle_ev]
  simp [c_evals_oracle_ev]
  simp [c_evals_code_ev]
end c_evals

section c_c_evals
def c_c_evals :=
  c_comp₃.comp₄
  (c_const c_evalo)
  (c_const c_c_evals_oracle)
  (c_const $ c_const c_evals_code)
  (c_const c_id)
@[cp] theorem c_c_evals_prim : code_prim c_c_evals := by unfold c_c_evals; apply_cp
@[simp] theorem c_c_evals_evp : evalp O c_c_evals x = c_evals := by simp [c_c_evals, c_evals]
end c_c_evals

end Computability.Code
end evals
