import Computability.Constructions.Primitive

open Nat
open Denumerable
open Encodable
open List



-- theorem option_isSome : Primrec (@Option.isSome α) :=
--   (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl
theorem hnat_to_opt_0 : (Denumerable.ofNat (Option ℕ) 0) = Option.none := by exact rfl
theorem hnat_to_opt_1_aux {x} (h2:¬x=0) : x=x-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h2)
theorem hnat_to_opt_1 {x} (h3:¬x=0) : (Denumerable.ofNat (Option ℕ) x) = Option.some (x-1) := by
  rw (config := {occs := .pos [1]}) [hnat_to_opt_1_aux h3]
  exact rfl
theorem hnat_to_opt_2 {x} (h3:¬x=o2n Option.none) : n2o x = (Option.some (x-1)) := by
  rw (config := {occs := .pos [1]}) [hnat_to_opt_1_aux h3]
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
theorem n2o0 : n2o 0 = Option.none := by exact rfl
theorem hnat_4 (hn:¬n=0) : n2o n = Option.some (n-1) := by
  exact hnat_to_opt_2 hn
theorem hnat_5 (h:n≠0) : ((n-1).max (a-1))+1 = n.max a := by
  grind only [= Nat.max_def, cases Or]
theorem hnat_6 (h:i≠0) : (n2o i).isSome := by
  have : i=i-1+1 := by exact hnat_to_opt_1_aux h
  rw [this]
  rfl
theorem hnat_8 (h:(n2o o).isSome): o≠0 := by
  contrapose h
  simp at h
  simp [h]
  rfl
theorem hnat_7 : (n2o o).get h = o-1 := by
  have : o ≠ 0 := by exact hnat_8 h
  have : o=o-1+1 := by exact hnat_to_opt_1_aux this
  simp (config:={singlePass:=true}) [this]
  rfl
theorem hnat_9 : o.get h = (o2n o)-1 := by
  exact Eq.symm (hnat_2 h)
theorem iget_eq_get {o:Option ℕ} (h:o.isSome) : o.iget = o.get h := by
  have : o= some (o.get h) := by exact Option.dom_imp_some h
  exact Option.iget_of_mem this





section isSome
namespace Nat.RecursiveIn.Code
def c_isSome := c_sg'
@[simp] theorem c_isSome_ev_pr:code_prim c_isSome := by repeat (first|assumption|simp|constructor)
@[simp] theorem c_isSome_evp:eval_prim O c_isSome = fun o => b'2n $ (n2o o).isSome := by
  simp [c_isSome]
  funext x
  simp
  simp [b'2n, n2o]
  cases x with
  | zero => simp; exact rfl
  | succ n => simp; exact Option.isSome_iff_ne_none.mp rfl
@[simp] theorem c_isSome_ev:eval O c_isSome = fun o => b'2n $ (n2o o).isSome := by rw [← eval_prim_eq_eval c_isSome_ev_pr]; simp only [c_isSome_evp];
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.isSome:Nat.PrimrecIn O Nat.isSome := by ...
-- theorem Nat.Primrec.isSome:Nat.Primrec Nat.isSome := by ...
end isSome


section opt_iget
namespace Nat.RecursiveIn.Code
def c_opt_iget := c_pred
@[simp] theorem c_opt_iget_ev_pr:code_prim c_opt_iget := by repeat (first|assumption|simp|constructor)
@[simp] theorem c_opt_iget_evp : eval_prim O c_opt_iget o = Option.iget (n2o o) := by
  simp [c_opt_iget]
  by_cases ho:o=0
  · simp [ho]; exact rfl
  · have asd := exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho)
    rcases asd with ⟨k,hk⟩
    simp [←hk]
    have rwma : n2o (k + 1) = Option.some k := by exact rfl
    rw [rwma]
@[simp] theorem iget_evp_2 (h:o≠0):  Option.iget (n2o o) = o-1:= by
  have asd : o = (o-1)+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h)
  rw [asd]
  exact rfl

@[simp] theorem c_opt_iget_ev:eval O c_opt_iget o = Option.iget (n2o o) := by simp [← eval_prim_eq_eval c_opt_iget_ev_pr]
end Nat.RecursiveIn.Code
end opt_iget
section opt_getD
namespace Nat.RecursiveIn.Code
def c_opt_getD := c_ifz.comp₃ left right (c_opt_iget.comp left)
@[simp] theorem c_opt_getD_ev_pr:code_prim c_opt_getD := by repeat (first|assumption|simp|constructor)
@[simp] theorem c_opt_getD_evp : eval_prim O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by
  simp [c_opt_getD]
  by_cases ho:o=0
  · simp [ho];
    simp [n2o0]
  · 
    have asd := exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho)
    rcases asd with ⟨k,hk⟩
    simp [←hk]
    have rwma : n2o (k + 1) = Option.some k := by exact rfl
    rw [rwma]
    rfl
@[simp] theorem c_opt_getD_ev:eval O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by simp [← eval_prim_eq_eval c_opt_getD_ev_pr]
end Nat.RecursiveIn.Code
end opt_getD

section opt_none
namespace Nat.RecursiveIn.Code
def c_opt_none := (c_const 0)
@[simp] theorem c_opt_none_ev_pr:code_prim c_opt_none := by repeat (first|assumption|simp|constructor)
@[simp] theorem c_opt_none_evp : eval_prim O c_opt_none o = o2n Option.none := by
  simp [c_opt_none]
-- @[simp] theorem c_opt_none_ev: n2o (eval O c_opt_none o) = (Option.none : Option ℕ) := by simp [← eval_prim_eq_eval c_opt_none_ev_pr]
end Nat.RecursiveIn.Code
end opt_none

section opt_bind
namespace Nat.RecursiveIn.Code
-- def c_opt_bind := c_ifz.comp₃ left zero (right.comp (c_opt_iget.comp left))
def c_opt_bind (cf cg:Code) :=  c_ifz.comp₃ cf zero (cg.comp₂ c_id (c_opt_iget.comp cf))
@[simp, aesop safe] theorem c_opt_bind_ev_pr(hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_opt_bind cf cg) := by repeat (first|assumption|simp|constructor)
@[simp] theorem c_opt_bind_evp: eval_prim O (c_opt_bind cf cg) x =
  o2n do
    let t ← n2o (eval_prim O cf x)
    let r ← n2o (eval_prim O cg (Nat.pair x t))
    -- return ←r
    return r
    -- return eval_prim O cg t
:= by
  -- sorry
  simp [c_opt_bind,eval_prim]
  cases Classical.em (eval_prim O cf x = 0) with
  | inl h => simp [h, n2o0]
  | inr h =>
    simp [h]
    simp [isSome.bind $ hnat_6 h]
    congr
    exact Eq.symm hnat_7

-- @[simp] theorem c_opt_bind_ev:eval O c_opt_bind = unpaired2 Nat.opt_bind := by rw [← eval_prim_eq_eval c_opt_bind_ev_pr]; simp only [c_opt_bind_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.opt_bind:Nat.PrimrecIn O Nat.opt_bind := by ...
-- theorem Nat.Primrec.opt_bind:Nat.Primrec Nat.opt_bind := by ...
end opt_bind

section opt_bind'
namespace Nat.RecursiveIn.Code
-- def c_opt_bind' := c_ifz.comp₃ left zero (right.comp (c_opt_iget.comp left))
def c_opt_bind' (cf cg:Code) :=  c_ifz.comp₃ cf zero cg
@[simp, aesop safe] theorem c_opt_bind'_ev_pr(hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_opt_bind' cf cg) := by repeat (first|assumption|simp|constructor)
@[simp] theorem c_opt_bind'_evp: eval_prim O (c_opt_bind' cf cg) x =
  o2n do
    let t ← n2o (eval_prim O cf x)
    let r ← n2o (eval_prim O cg x)
    -- return ←r
    return r
    -- return eval_prim O cg t
:= by
  -- sorry
  simp [c_opt_bind',eval_prim]
  cases Classical.em (eval_prim O cf x = 0) with
  | inl h => simp [h, n2o0]
  | inr h =>
    simp [h]
    simp [isSome.bind $ hnat_6 h]
    -- congr
    -- exact Eq.symm hnat_7


-- @[simp] theorem c_opt_bind'_ev:eval O c_opt_bind' = unpaired2 Nat.opt_bind' := by rw [← eval_prim_eq_eval c_opt_bind'_ev_pr]; simp only [c_opt_bind'_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.opt_bind':Nat.PrimrecIn O Nat.opt_bind' := by ...
-- theorem Nat.Primrec.opt_bind':Nat.Primrec Nat.opt_bind' := by ...
end opt_bind'

section part_bind
namespace Nat.RecursiveIn.Code
-- def c_part_bind := c_ifz.comp₃ left zero (right.comp (c_opt_iget.comp left))
def c_part_bind (cf cg:Code) := cg.comp₂ c_id cf
-- @[simp, aesop safe] theorem c_part_bind_ev_pr(hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_part_bind cf cg) := by repeat (first|assumption|simp|constructor)
-- @[simp] theorem c_part_bind_evp: eval_prim O (c_part_bind cf cg) x =
--   o2n do
--     let t ← n2o (eval_prim O cf x)
--     let r ← n2o (eval_prim O cg (Nat.pair x t))
--     -- return ←r
--     return r
--     -- return eval_prim O cg t
-- := by
--   -- sorry
--   simp [c_part_bind,eval_prim]
--   cases Classical.em (eval_prim O cf x = 0) with
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
 simp [eval]
 simp [Seq.seq]
 
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.part_bind:Nat.PrimrecIn O Nat.part_bind := by ...
-- theorem Nat.Primrec.part_bind:Nat.Primrec Nat.part_bind := by ...
end part_bind
