/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park.
-/
import Computability.Constructions.Primitive
import Computability.Constructions.Eval

open Computability.Code
open Classical

namespace Computability.Code

def c_diverge := rfind' (c_const 1)
@[simp] theorem c_diverge_ev : eval O c_diverge x = Part.none := by
  simp [c_diverge,eval]
  apply Part.eq_none_iff.mpr
  simp
theorem c_diverge_ev' : eval O c_diverge = λ _ ↦ Part.none := by funext; simp
theorem _root_.Nat.RecursiveIn.none : Nat.RecursiveIn O fun _ => Part.none := by
  rw [← c_diverge_ev']
  exact RecursiveIn_of_eval

def c_pair_proj (x:ℕ) := pair (c_const x) c_id
theorem c_pair_proj_evp : evalp O (c_pair_proj x) = Nat.pair x := by simp [c_pair_proj]
lemma _root_.Nat.PrimrecIn.pair_proj : Nat.PrimrecIn O (Nat.pair x) := by
  rw [←c_pair_proj_evp]
  exact code_prim_prop

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
  ·
    intro h
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
theorem Nat.RecursiveIn.ite {O:ℕ→ℕ} {f g:ℕ→.ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c) (hf:Nat.RecursiveIn O f) (hg:Nat.RecursiveIn O g):Nat.RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
  apply exists_code.mpr
  rcases exists_code_total.mp hc with ⟨cc,hcc,hcct⟩
  rcases exists_code_nat.mp hf with ⟨ca,hca⟩
  rcases exists_code_nat.mp hg with ⟨cb,hcb⟩
  use c_ite cc ca.n2c cb.n2c
  funext x
  simp [c_ite_ev hcct]
  simp [hcc, hca, hcb]


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




def eval₁ (O:ℕ→ℕ):ℕ→.ℕ := fun ex => eval O ex.l.n2c ex.r
def c_evaln₁ := c_evaln.comp₃ (left.comp right) (left) (right.comp right)
def evaln₁ (O:ℕ→ℕ):ℕ→ℕ := fun abc => Encodable.encode (evaln O abc.r.r abc.l.n2c abc.r.l)
theorem c_evaln₁_evp : evalp O c_evaln₁ = evaln₁ O := by
  simp [c_evaln₁]
  exact rfl
theorem rec_eval₁:Nat.RecursiveIn O (eval₁ O) := Computability.eval
theorem prim_evaln₁:Nat.PrimrecIn O (evaln₁ O) := by
  simp [← c_evaln₁_evp]

end Computability.Code


namespace Computability.Code
/-- c_evconst takes as input a natural `(e,x)`, and returns an index to a program which calculates `[e](x)` regardless of its input. -/
def c_evconst (ex:ℕ) : Code := comp ex.l.n2c (c_const ex.r)
def c_c_evconst := c_comp.comp₂ left (c_c_const.comp right)
@[simp] theorem c_c_evconst_evp : evalp O c_c_evconst = fun x:ℕ => c2n (c_evconst (x.n2c)) := by
  unfold c_evconst
  funext x
  simp [c_c_evconst]
@[simp] theorem c_evconst_ev : eval O (c_evconst (Nat.pair e x)) _z = eval O e.n2c x := by unfold c_evconst; simp [eval]
-- hm, the proof shouldnt be this long?

@[simp] theorem c_c_evconst_pr : Nat.PrimrecIn O fun x:ℕ => c2n (c_evconst (x.n2c)) := by
  rw [← c_c_evconst_evp]
  exact code_prim_prop
-- @[simp] theorem c_evconst_pr : Nat.PrimrecIn O c_evconst := by
--   have rwmain : c_evconst = (fun ex:ℕ => (comp ex.l ex.r:ℕ)) ∘ (fun ex:ℕ => Nat.pair ex.l (c_const ex.r)) := by
--     funext xs
--     simp
--     unfold c_evconst
--     exact rfl
--   rw [rwmain]
--   have main2 : Nat.PrimrecIn O fun ex:ℕ => Nat.pair ex.l (c_const ex.r) := by
--     refine Nat.PrimrecIn.pair ?_ ?_
--     · exact Nat.PrimrecIn.left
--     · have main3 : (fun ex:ℕ ↦ ((c_const ex.r):ℕ)) = (fun ex => (c_const ex :ℕ)) ∘ fun exa => exa.r := by
--         funext xs
--         simp only [Function.comp_apply]
--       have main4 : Nat.PrimrecIn O fun ex => (c_const ex:ℕ) := by
--         exact Nat.PrimrecIn.c_const
--         -- refine PrimrecIn.nat_iff.mp ?_

--         -- apply
--       have main5 : Nat.PrimrecIn O fun exa => exa.r := by
--         exact Nat.PrimrecIn.right
--       rw [main3]
--       apply Nat.PrimrecIn.comp main4 main5
--   apply Nat.PrimrecIn.comp (Nat.PrimrecIn.c_comp) main2




theorem _root_.Nat.RecursiveIn.evalRecInO' {O} {f:ℕ→.ℕ} (h:Nat.RecursiveIn O f):Nat.RecursiveIn O (fun x => (f x) >>= (eval₁ O)) := by
  simp only [Part.bind_eq_bind]
  refine _root_.Nat.RecursiveIn.comp ?_ h
  apply rec_eval₁

end Computability.Code
