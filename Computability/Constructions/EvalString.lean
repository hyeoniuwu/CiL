import Computability.Constructions.Use
import Computability.EvalString

section evalnc
namespace Nat.RecursiveIn.Code
/-- eval c_evalnc (x,y) = [x=y] -/
def c_evalnc :=
  let u0 := left.comp left
  let s0 := right.comp left
  let c0 := left.comp right
  let x0 := right.comp right
  let bind_prev := left
  let u1 := left.comp (left.comp bind_prev)
  let s1 := right.comp (left.comp bind_prev)
  let c1 := left.comp (right.comp bind_prev)
  let x1 := right.comp (right.comp bind_prev)

  c_opt_bind
  (c_usen.comp₃ x0 c0 s0) $
  c_if_le_te.comp₄ right u1 (c_evaln.comp₃ x1 c1 s1) zero
@[simp, aesop safe] theorem c_evalnc_ev_pr:code_prim c_evalnc := by unfold c_evalnc; repeat (first|assumption|simp|constructor)
@[simp] theorem c_evalnc_evp:eval_prim O c_evalnc (Nat.pair (Nat.pair u s) (Nat.pair c x)) = o2n (evalnc O u s c x) := by
  simp [c_evalnc,eval_prim];
  simp [evalnc]
  congr; funext a_0
  simp only [apply_ite]
  aesop
  
-- @[simp] theorem c_evalnc_ev:eval O c_evalnc (Nat.pair (Nat.pair u s) (Nat.pair c x)) = o2n (evalnc O u s c x) then Part.some 0 else Part.some 1 := by
--   rw [← eval_prim_eq_eval c_evalnc_ev_pr]; simp only [c_evalnc_evp]; funext xs; exact apply_ite Part.some (xs.l = xs.r) 0 1
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.evalnc:Nat.PrimrecIn O Nat.evalnc := by ...
-- theorem Nat.Primrec.evalnc:Nat.Primrec Nat.evalnc := by ...
end evalnc
