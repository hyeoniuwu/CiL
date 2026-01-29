/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Primitive
import Computability.Constructions.Eval

/-!
# Construction of codes of basic non-primrec functions

This file defines codes for basic functions which are not primitive recursive.

## Main declarations

- `c_diverge`: A code which diverges on all inputs.
- `c_ite`: A code which implements if-then-else, where the entire computation
  does not necessarily diverge even if one the branches does.

-/

open Computability.Code
open Classical

namespace Computability.Code

section diverge
def c_diverge := rfind' (c_const 1)
@[simp] theorem c_diverge_ev : eval O c_diverge x = Part.none := by
  simp [c_diverge,eval]
  apply Part.eq_none_iff.mpr
  simp
theorem c_diverge_ev' : eval O c_diverge = λ _ ↦ Part.none := by funext; simp
end diverge

section ifz1
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
end ifz1

section ite
def c_ite (c a b:Computability.Code) := c_eval.comp₂ (c_ifz1 c a.c2n b.c2n) (c_id)
@[simp] theorem c_ite_ev (hc:code_total O c) : eval O (c_ite c a b) x = if (eval O c x=Part.some 0) then (eval O a x) else (eval O b x) := by
  simp [c_ite]
  simp [Seq.seq]
  have d := @c_ifz1_total O c a.c2n b.c2n hc x
  simp [Part.Dom.bind d]
  simp [c_ifz1_ev hc]
  split
  next h => simp only [Part.get_some, n2c_c2n]
  next h => simp only [Part.get_some, n2c_c2n]
theorem exists_code_nat {O:ℕ → ℕ} {f:ℕ →. ℕ} : Nat.RecursiveIn O f ↔ ∃ c:ℕ , eval O c.n2c = f := by
  rw [@exists_code O f]
  exact Function.Surjective.exists n2c_sur
theorem exists_code_total {O:ℕ → ℕ} {f:ℕ → ℕ} : Nat.RecursiveIn O f ↔ ∃ c , eval O c = f ∧ code_total O c := by
  constructor
  · intro h
    rcases exists_code.mp h with ⟨c,hc⟩
    use c
    constructor
    exact hc
    intro x
    rw [hc]
    exact trivial
  intro h
  rcases h with ⟨c,hc,_⟩
  apply exists_code.mpr ⟨c,hc⟩
end ite

section if_le_te'
-- like c_if_le_te, but allows either branch to diverge
def c_if_le_te' (c1 c2 c3 c4:Code) := c_ite (c_sub.comp₂ c1 c2) c3 c4
@[simp] theorem c_if_le_te'_ev (hc1:code_total O c1) (hc2:code_total O c2) : eval O (c_if_le_te' c1 c2 c3 c4) x = if (eval O c1 x).get (hc1 x) ≤ (eval O c2 x).get (hc2 x) then (eval O c3 x) else (eval O c4 x) := by
  simp [c_if_le_te']
  have : code_total O (c_sub.comp₂ c1 c2) := by
    apply total_comp_of $ prim_total c_sub_prim
    apply total_pair_of hc1 hc2
  simp [this]
  congr
  simp [Seq.seq]
  simp [Part.Dom.bind $ hc1 x]
  simp [Part.Dom.bind $ hc2 x]
  exact Nat.sub_eq_zero_iff_le
end if_le_te'

section if_eq_te'
-- like c_if_eq_te, but allows either branch to diverge
def c_if_eq_te' (c1 c2 c3 c4:Code) := c_ite (c_dist.comp₂ c1 c2) c3 c4
@[simp] theorem c_if_eq_te'_ev (hc1:code_total O c1) (hc2:code_total O c2) : eval O (c_if_eq_te' c1 c2 c3 c4) x = if (eval O c1 x).get (hc1 x) = (eval O c2 x).get (hc2 x) then (eval O c3 x) else (eval O c4 x) := by
  simp [c_if_eq_te']
  have : code_total O (c_dist.comp₂ c1 c2) := by
    apply total_comp_of $ prim_total c_dist_prim
    apply total_pair_of hc1 hc2
  simp [this]
  simp [Seq.seq]
  simp [Part.Dom.bind $ hc1 x]
  simp [Part.Dom.bind $ hc2 x]
end if_eq_te'

section ifdom
def c_ifdom (c a:Computability.Code) := c_add.comp₂ (zero.comp c) a
@[simp] theorem c_ifdom_ev  : eval O (c_ifdom c a) x = if (eval O c x).Dom then (eval O a x) else Part.none := by
  simp [c_ifdom]
  simp [eval]
  simp [Seq.seq]
  split
  next h =>
    simp [Part.Dom.bind h]
  next h =>
    simp [Part.eq_none_iff'.mpr h]
end ifdom

section evaln₁
def c_evaln₁ := c_evaln.comp₃ (left.comp right) (left) (right.comp right)
def evaln₁ (O:ℕ→ℕ):ℕ→ℕ := fun abc => Encodable.encode (evaln O abc.r.r abc.l.n2c abc.r.l)
theorem c_evaln₁_evp : evalp O c_evaln₁ = evaln₁ O := by
  simp [c_evaln₁]
  exact rfl
theorem prim_evaln₁ : Nat.PrimrecIn O (evaln₁ O) := by
  simp [← c_evaln₁_evp]
end evaln₁

section eval₁
def eval₁ (O:ℕ→ℕ):ℕ→.ℕ := fun ex => eval O ex.l.n2c ex.r
def c_eval₁ := c_eval
@[simp] theorem c_eval₁_ev : eval O c_eval₁ = eval₁ O := by
  simp [c_eval₁]
  unfold eval₁
  funext ex
  rw (config:={occs:=.pos [1]}) [show ex = ⟪ex.l, ex.r⟫ from by simp]
  exact c_eval_ev

theorem rec_eval₁ : Nat.RecursiveIn O (eval₁ O) := Nat.RecursiveIn.Rin.eval
end eval₁

end Computability.Code

open Computability
open Code
namespace Nat.RecursiveIn
theorem Rin.ite {O:ℕ→ℕ} {f g:ℕ→.ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c) (hf:Nat.RecursiveIn O f) (hg:Nat.RecursiveIn O g):Nat.RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
  apply exists_code.mpr
  rcases exists_code_total.mp hc with ⟨cc,hcc,hcct⟩
  rcases exists_code_nat.mp hf with ⟨ca,hca⟩
  rcases exists_code_nat.mp hg with ⟨cb,hcb⟩
  use c_ite cc ca.n2c cb.n2c
  funext x
  simp [c_ite_ev hcct]
  simp [hcc, hca, hcb]
theorem Rin.evalRecInO' {O} {f:ℕ→.ℕ} (h:Nat.RecursiveIn O f):Nat.RecursiveIn O (fun x => (f x) >>= (eval₁ O)) := by
  simp only [Part.bind_eq_bind]
  refine Nat.RecursiveIn.comp ?_ h
  apply rec_eval₁
theorem Rin.none : Nat.RecursiveIn O fun _ => Part.none := by
  rw [← c_diverge_ev']
  exact RecursiveIn_of_eval
