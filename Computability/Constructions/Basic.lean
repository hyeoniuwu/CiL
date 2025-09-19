import Computability.Constructions.Primitive
import Computability.Constructions.Eval

open Nat.RecursiveIn.Code
open Classical

namespace Nat.RecursiveIn.Code

def c_diverge := rfind' (c_const 1)
@[simp] theorem c_diverge_ev : eval O c_diverge x = Part.none := by
  simp [c_diverge,eval]
  apply Part.eq_none_iff.mpr
  simp


def c_ifz1 (c) (a b:ℕ) := c_add.comp₂ (c_mul.comp₂ (c_const b) (c_sg.comp c)) (c_mul.comp₂ (c_const a) (c_sg'.comp c))
@[simp] theorem c_ifz1_ev (hc:code_total O c) : eval O (c_ifz1 c a b) x = if (eval O c x=Part.some 0) then Part.some a else Part.some b := by
  simp [c_ifz1]
  simp [eval]
  simp [Seq.seq]
  have : (eval O c x).Dom := by exact hc x
  simp [Part.Dom.bind (hc x)]
  split
  next h => simp [Part.get_eq_iff_eq_some.mp h]
  next h => simp [Part.ne_of_get_ne' h]
theorem c_ifz1_total (hc:code_total O c) : code_total O (c_ifz1 c a b) := by
  intro x
  simp [c_ifz1_ev hc]
  split
  next h => simp_all only [Part.some_dom]
  next h => simp_all only [Part.some_dom]

def c_ite (c a b:Nat.RecursiveIn.Code) := c_eval.comp₂ (c_ifz1 c a b) (c_id)
@[simp] theorem c_ite_ev (hc:code_total O c) : eval O (c_ite c a b) x = if (eval O c x=Part.some 0) then (eval O a x) else (eval O b x) := by
  simp [c_ite]
  simp [eval]
  simp [Seq.seq]
  have d := @c_ifz1_total O c a b hc x
  simp [Part.Dom.bind d]
  simp [c_ifz1_ev hc]
  split
  next h => simp only [Part.get_some, decodeCode_encodeCode]
  next h => simp only [Part.get_some, decodeCode_encodeCode]
theorem Nat.RecursiveIn.ite {O:ℕ→ℕ} {f g:ℕ→.ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c) (hf:Nat.RecursiveIn O f) (hg:Nat.RecursiveIn O g):Nat.RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
  apply exists_code.mpr
  rcases exists_code_total.mp hc with ⟨cc,hcc,hcct⟩
  rcases exists_code_nat.mp hf with ⟨ca,hca⟩
  rcases exists_code_nat.mp hg with ⟨cb,hcb⟩
  use c_ite cc ca cb
  funext x
  simp [c_ite_ev hcct]
  simp [hcc, hca, hcb]
  

def c_if_le_te' (c1 c2 c3 c4:Code) := c_ite (c_sub.comp₂ c1 c2) c3 c4
@[simp] theorem c_if_le_te'_ev (hc1:code_total O c1) (hc2:code_total O c2) : eval O (c_if_le_te' c1 c2 c3 c4) x = if (eval O c1 x).get (hc1 x) ≤ (eval O c2 x).get (hc2 x) then (eval O c3 x) else (eval O c4 x) := by
  simp [c_if_le_te']
  have : code_total O (c_sub.comp (c1.pair c2)) := by
    apply total_comp_of $ prim_total c_sub_ev_pr
    apply total_pair_of hc1 hc2
  simp [this]
  congr
  simp [eval, Seq.seq]
  simp [Part.Dom.bind $ hc1 x]
  simp [Part.Dom.bind $ hc2 x]
  exact Nat.sub_eq_zero_iff_le

end Nat.RecursiveIn.Code
