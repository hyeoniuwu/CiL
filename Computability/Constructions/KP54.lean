import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.KP54

open Nat.RecursiveIn.Code
open Computability

section kp54
-- namespace Nat.RecursiveIn.Code

-- def c_kp54 := zero

-- theorem c_kp54_ev : eval (K0 Nat.fzero) c_kp54 = KP54 := by sorry

@[irreducible] noncomputable def c_c_kp54_aux (i n:ℕ) :=
  zero
-- theorem c_c_kp54_aux_evp : 


def c_kp54_main :=
  have s := left
  have KP54s := right
  let i := c_div2.comp s
  let Aₚ := left.comp (KP54s)
  let Bₚ := right.comp (KP54s)
  let lb := c_list_length.comp Bₚ
  let la := c_list_length.comp Aₚ
  c_ifz.comp₃ (c_mod.comp₂ (succ.comp s) (c_const 2))
  (
    let dvt := oracle.comp zero
    c_eval
  )
  c_evaln
  -- c_eval
def c_kp54 :=
  (
    prec
    zero $
    c_kp54_main.comp right
  ).comp₂ zero c_id
-- theorem c_kp54_t : code_total O c_kp54 := by sorry
@[simp] theorem c_kp54_evp : eval_prim (K0 Nat.fzero) c_kp54 x = KP54.KP54 x := by
  induction x with
  | zero =>
    simp [c_kp54]
    unfold KP54.KP54
    rfl
  | succ x ih =>
    unfold c_kp54
    simp
    have : (Nat.rec 0 (fun y IH ↦ eval_prim (K0 Nat.fzero) c_kp54_main (Nat.pair y IH)) x) = eval_prim (K0 Nat.fzero) c_kp54 x := by 
      unfold c_kp54
      cases x <;> simp
    -- simp (config := {zeta:=false}) only []
    rw [this, ih]; clear this ih
    
    unfold c_kp54_main
    simp
    rw (config:={occs:=.pos [1]}) [KP54.KP54]
    simp (config := {zeta:=false}) []

    sorry

  
-- theorem c_kp54_ev : (eval (∅⌜) c_kp54 x).get (c_kp54_t x) = KP54.KP54 x := by sorry

section n2b
namespace Nat.RecursiveIn.Code
def c_n2b := c_sg
@[simp, aesop safe] theorem c_n2b_ev_pr:code_prim c_n2b := by repeat (first|assumption|simp|constructor)
@[simp] theorem c_n2b_evp:eval_prim O c_n2b = fun x => if n2b x = true then 1 else 0 := by
  simp [c_n2b]
  unfold sg; unfold n2b
  aesop
@[simp] theorem c_n2b_ev:eval O c_n2b = fun x => if n2b x = true then 1 else 0 := by rw [← eval_prim_eq_eval c_n2b_ev_pr]; simp only [c_n2b_evp]; funext x; aesop
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.n2b:Nat.PrimrecIn O Nat.n2b := by ...
-- theorem Nat.Primrec.n2b:Nat.Primrec Nat.n2b := by ...
end n2b

@[simp] theorem getI_eq_getElem {l:List ℕ} {h:i<l.length} : l.getI i = l[i] := by
  unfold List.getI
  simp [h]


def c_kp54_A := c_n2b.comp $ c_list_getI.comp₂ (left.comp $ c_kp54.comp succ) c_id
theorem c_kp54_A_evp : eval_prim (K0 Nat.fzero) c_kp54_A = χ KP54.A := by
  funext x
  simp [c_kp54_A]
  unfold KP54.A
  unfold KP54.As
  simp [χ]
  congr
  exact getI_eq_getElem
  
  
  

theorem A_le_J1 : KP54.A ≤ᵀ ∅⌜ := by
  unfold KP54.A
  unfold KP54.As
  simp only [← c_kp54_ev]
  simp
  unfold SetTuringReducible
  simp [SetTuringReducible]
  

  
  sorry

-- end Nat.RecursiveIn.Code
end kp54
