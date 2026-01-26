/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Primitive
import Computability.Helper.Partial

open Nat
open Denumerable
open Encodable
open List

@[simp] theorem hnat_to_opt_0 : (Denumerable.ofNat (Option ℕ) 0) = Option.none := by exact rfl
@[simp] theorem hnat_to_opt_0' : (Denumerable.ofNat (Option ℕ) (x+1)) = Option.some (x) := by exact rfl
theorem ge_0_rw {x} (h2:¬x=0) : x=x-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h2)
theorem hnat_to_opt_2 {x} (h3:¬x=o2n Option.none) : n2o x = (Option.some (x-1)) := by
  rw (config := {occs := .pos [1]}) [ge_0_rw h3]
  exact rfl
theorem not_none_imp_not_zero {xx} (h:¬xx=o2n Option.none):¬xx=0:=by
  simp at h
  exact h
theorem hnat_0 {o:Option ℕ} (ho: o.isSome) : ¬ o2n o = 0 := by
  have : o = Option.some (o.get ho) := by exact Option.dom_imp_some ho
  rw [this]
  exact add_one_ne_zero (Encodable.encode (o.get ho))
theorem hnat_1 {o:Option ℕ} (ho: ¬ o = Option.none) : ¬ o2n o = 0 := by
  exact hnat_0 (Option.isSome_iff_ne_none.mpr ho)
theorem hnat_2 {o:Option ℕ} (ho: o.isSome) : (o2n o) - 1 = o.get ho := by
  simp (config:={singlePass:=true}) [Option.dom_imp_some ho]
  exact rfl

theorem hnat_5 (h:n≠0) : ((n-1).max (a-1))+1 = n.max a := by
  grind only [= Nat.max_def, cases Or]
theorem hnat_6 (h:i≠0) : (n2o i).isSome := by
  have : i=i-1+1 := by exact ge_0_rw h
  rw [this]
  rfl
theorem hnat_8 (h:(n2o o).isSome): o≠0 := by
  contrapose h
  simp at h
  simp [h]
theorem hnat_7 : (n2o o).get h = o-1 := by
  have : o ≠ 0 := by exact hnat_8 h
  have : o=o-1+1 := by exact ge_0_rw this
  simp (config:={singlePass:=true}) [this]
theorem hnat_9 : o.get h = (o2n o)-1 := by
  exact Eq.symm (hnat_2 h)
theorem iget_eq_get {o:Option ℕ} (h:o.isSome) : o.iget = o.get h := by
  have : o= some (o.get h) := by exact Option.dom_imp_some h
  exact Option.iget_of_mem this
theorem o2n_a0 : o2n x = 0 ↔ x = Option.none := by
  constructor
  · intro h
    contrapose h
    exact hnat_1 h
  · intro h
    simp [h]
theorem hnat_10 (h : o2n x ≠ 0) : x.isSome := by
  have := hnat_6 h
  simp at this
  exact this
theorem hnat_11 {x:Option ℕ} (h : x.isSome) : x = some (o2n x - 1) := by
  rw [hnat_2 h]
  simp
theorem hnat_12 {x : ℕ} (h : n2o x = some a) : x-1 = a := by
  have : (n2o x).isSome := by exact Option.isSome_of_mem h
  have := hnat_11 this
  rw [this] at h
  simp at h
  assumption



section isSome
namespace Computability.Code
def c_isSome := c_sg'
@[cp] theorem c_isSome_prim : code_prim c_isSome := by unfold c_isSome; apply_cp
@[simp] theorem c_isSome_evp:evalp O c_isSome = fun o => b'2n $ (n2o o).isSome := by
  simp [c_isSome]
  funext x
  simp
  simp [b'2n, n2o]
  cases x <;> simp
@[simp] theorem c_isSome_ev:eval O c_isSome = fun o => b'2n $ (n2o o).isSome := by rw [← evalp_eq_eval c_isSome_prim]; simp only [c_isSome_evp];
end Computability.Code
-- theorem Nat.PrimrecIn.isSome:Nat.PrimrecIn O Nat.isSome := by ...
-- theorem Nat.Primrec.isSome:Nat.Primrec Nat.isSome := by ...
end isSome


section opt_iget
namespace Computability.Code
def c_opt_iget := c_pred
@[cp] theorem c_opt_iget_prim : code_prim c_opt_iget := by unfold c_opt_iget; apply_cp
@[simp] theorem c_opt_iget_evp : evalp O c_opt_iget o = Option.iget (n2o o) := by
  simp [c_opt_iget]
  by_cases ho:o=0
  · simp [ho];
  · have asd := exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho)
    rcases asd with ⟨k,hk⟩
    simp [←hk]
@[simp] theorem iget_evp_2 (h:o≠0):  Option.iget (n2o o) = o-1:= by
  have asd : o = (o-1)+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h)
  rw [asd]
  exact rfl

@[simp] theorem c_opt_iget_ev:eval O c_opt_iget o = Option.iget (n2o o) := by simp [← evalp_eq_eval c_opt_iget_prim]
end Computability.Code
end opt_iget
section opt_getD
namespace Computability.Code
def c_opt_getD := c_ifz.comp₃ left right (c_opt_iget.comp left)
@[cp] theorem c_opt_getD_prim : code_prim c_opt_getD := by unfold c_opt_getD; apply_cp
@[simp] theorem c_opt_getD_evp : evalp O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by
  simp [c_opt_getD]
  by_cases ho:o=0
  · simp [ho];
  ·
    have asd := exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho)
    rcases asd with ⟨k,hk⟩
    simp [←hk]
@[simp] theorem c_opt_getD_ev:eval O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by simp [← evalp_eq_eval c_opt_getD_prim]
end Computability.Code
end opt_getD

section opt_none
namespace Computability.Code
def c_opt_none := (c_const 0)
@[cp] theorem c_opt_none_prim : code_prim c_opt_none := by unfold c_opt_none; apply_cp
@[simp] theorem c_opt_none_evp : evalp O c_opt_none o = o2n Option.none := by
  simp [c_opt_none]
-- @[simp] theorem c_opt_none_ev: n2o (eval O c_opt_none o) = (Option.none : Option ℕ) := by simp [← evalp_eq_eval c_opt_none_prim]
end Computability.Code
end opt_none

section opt_bind
namespace Computability.Code
-- def c_opt_bind := c_ifz.comp₃ left zero (right.comp (c_opt_iget.comp left))
def c_opt_bind (cf cg:Code) :=  c_ifz.comp₃ cf zero (cg.comp₂ c_id (c_opt_iget.comp cf))
@[cp] theorem c_opt_bind_prim(hcf:code_prim cf) (hcg:code_prim cg) : code_prim (c_opt_bind cf cg) := by unfold c_opt_bind; apply_cp
@[simp] theorem c_opt_bind_evp: evalp O (c_opt_bind cf cg) x =
  o2n do
    let t ← n2o (evalp O cf x)
    let r ← n2o (evalp O cg (Nat.pair x t))
    -- return ←r
    return r
    -- return evalp O cg t
:= by
  -- sorry
  simp [c_opt_bind,evalp]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp [h]
    simp [isSome.bind $ hnat_6 h]
    congr
    exact Eq.symm hnat_7

-- @[simp] theorem c_opt_bind_ev:eval O c_opt_bind = unpaired2 Nat.opt_bind := by rw [← evalp_eq_eval c_opt_bind_prim]; simp only [c_opt_bind_evp]
end Computability.Code
-- theorem Nat.PrimrecIn.opt_bind:Nat.PrimrecIn O Nat.opt_bind := by ...
-- theorem Nat.Primrec.opt_bind:Nat.Primrec Nat.opt_bind := by ...
end opt_bind

section opt_bind'
namespace Computability.Code
-- def c_opt_bind' := c_ifz.comp₃ left zero (right.comp (c_opt_iget.comp left))
def c_opt_bind' (cf cg:Code) :=  c_ifz.comp₃ cf zero cg
@[cp] theorem c_opt_bind'_prim(hcf:code_prim cf) (hcg:code_prim cg) : code_prim (c_opt_bind' cf cg) := by unfold c_opt_bind'; apply_cp
@[simp] theorem c_opt_bind'_evp: evalp O (c_opt_bind' cf cg) x =
  o2n do
    let _ ← n2o (evalp O cf x)
    let r ← n2o (evalp O cg x)
    -- return ←r
    return r
    -- return evalp O cg t
:= by
  -- sorry
  simp [c_opt_bind',evalp]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp [h]
    simp [isSome.bind $ hnat_6 h]
    -- congr
    -- exact Eq.symm hnat_7


-- @[simp] theorem c_opt_bind'_ev:eval O c_opt_bind' = unpaired2 Nat.opt_bind' := by rw [← evalp_eq_eval c_opt_bind'_prim]; simp only [c_opt_bind'_evp]
end Computability.Code
-- theorem Nat.PrimrecIn.opt_bind':Nat.PrimrecIn O Nat.opt_bind' := by ...
-- theorem Nat.Primrec.opt_bind':Nat.Primrec Nat.opt_bind' := by ...
end opt_bind'

section part_bind
namespace Computability.Code
-- def c_part_bind := c_ifz.comp₃ left zero (right.comp (c_opt_iget.comp left))
def c_part_bind (cf cg:Code) := cg.comp₂ c_id cf
-- @[simp, aesop safe] theorem c_part_bind_prim(hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_part_bind cf cg) := by repeat (first|assumption|simp|constructor)
-- @[simp] theorem c_part_bind_evp: evalp O (c_part_bind cf cg) x =
--   o2n do
--     let t ← n2o (evalp O cf x)
--     let r ← n2o (evalp O cg (Nat.pair x t))
--     -- return ←r
--     return r
--     -- return evalp O cg t
-- := by
--   -- sorry
--   simp [c_part_bind,evalp]
--   cases Classical.em (evalp O cf x = 0) with
--   | inl h => simp [h, n2o0]
--   | inr h =>
--     simp [h]
--     simp [isSome.bind $ hnat_6 h]
--     congr
--     exact Eq.symm hnat_7

@[simp] theorem c_part_bind_ev : eval O (c_part_bind cf cg) x =
  do
    let t ← eval O cf x
    let r ← eval O cg (Nat.pair x t)
    return r
 := by
 simp [c_part_bind]
 simp [Seq.seq]

end Computability.Code
-- theorem Nat.PrimrecIn.part_bind:Nat.PrimrecIn O Nat.part_bind := by ...
-- theorem Nat.Primrec.part_bind:Nat.Primrec Nat.part_bind := by ...
end part_bind
