import Computability.Constructions.Primitive

open Nat
open Denumerable
open Encodable
open List



-- theorem option_isSome : Primrec (@Option.isSome α) :=
--   (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl



section isSome
namespace Nat.RecursiveIn.Code
def c_isSome := c_sg'
@[simp] theorem c_isSome_ev_pr:code_prim c_isSome := by unfold c_isSome; repeat (first|assumption|simp|constructor)
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
