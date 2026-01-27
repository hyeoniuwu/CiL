/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Primitive
import Computability.Constructions.Eval_Aux
import Computability.Constructions.Dovetail
import Computability.Constructions.Basic

/-!
# Meta.lean

This file constructs "meta-codes" (codes which implement functions from codes to codes) of various functions.

We first define such codes for constructors of `Code`;
`c_zero`, where `evalp O c_zero = c2n zero`, `c_succ`, and so on.

Then, the meta-code for any subsequent code `c` can be
implemented by replacing each of its components with its corresponding meta-code.

For example, suppose `c = comp succ left`.

Then the meta-code, named `c_c`, will be: `c_c = c_comp.comp₂ c_succ c_left`.

## Notation/quirks

 - The meta-code for a code has `c_` attached as a prefix.

-/


open Computability.Code
open Computability

section constructors
namespace Computability.Code
def c_zero := c_const (c2n zero)
@[cp] theorem c_zero_prim : code_prim c_zero := by unfold c_zero; apply_cp
@[simp] theorem c_zero_evp {O x} : evalp O c_zero x = c2n zero := by simp [c_zero]
@[simp] theorem c_zero_evp' {O} : evalp O c_zero = fun _:ℕ => c2n (zero) := by funext x; simp
@[simp] theorem c_zero_ev {O x}:eval O c_zero x = c2n zero := by rw [← evalp_eq_eval c_zero_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_zero {O} : Nat.PrimrecIn O (fun _:ℕ => c2n zero) := by rw [←c_zero_evp']; exact code_prim_prop
def c_succ := c_const (c2n succ)
@[cp] theorem c_succ_prim : code_prim c_succ := by unfold c_succ; apply_cp
@[simp] theorem c_succ_evp {O x} : evalp O c_succ x = c2n succ := by simp [c_succ]
@[simp] theorem c_succ_evp' {O} : evalp O c_succ = fun _:ℕ => c2n (succ) := by funext x; simp
@[simp] theorem c_succ_ev {O x}:eval O c_succ x = c2n succ := by rw [← evalp_eq_eval c_succ_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_succ {O} : Nat.PrimrecIn O (fun _:ℕ => c2n succ) := by rw [←c_succ_evp']; exact code_prim_prop
def c_left := c_const (c2n left)
@[cp] theorem c_left_prim : code_prim c_left := by unfold c_left; apply_cp
@[simp] theorem c_left_evp {O x} : evalp O c_left x = c2n left := by simp [c_left]
@[simp] theorem c_left_evp' {O} : evalp O c_left = fun _:ℕ => c2n (left) := by funext x; simp
@[simp] theorem c_left_ev {O x}:eval O c_left x = c2n left := by rw [← evalp_eq_eval c_left_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_left {O} : Nat.PrimrecIn O (fun _:ℕ => c2n left) := by rw [←c_left_evp']; exact code_prim_prop
def c_right := c_const (c2n right)
@[cp] theorem c_right_prim : code_prim c_right := by unfold c_right; apply_cp
@[simp] theorem c_right_evp {O x} : evalp O c_right x = c2n right := by simp [c_right]
@[simp] theorem c_right_evp' {O} : evalp O c_right = fun _:ℕ => c2n (right) := by funext x; simp
@[simp] theorem c_right_ev {O x} : eval O c_right x = c2n right := by rw [← evalp_eq_eval c_right_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_right : Nat.PrimrecIn O (fun _:ℕ => c2n right) := by rw [←c_right_evp']; exact code_prim_prop
def c_oracle := c_const (c2n oracle)
@[cp] theorem c_oracle_prim : code_prim c_oracle := by unfold c_oracle; apply_cp
@[simp] theorem c_oracle_evp {O x} : evalp O c_oracle x = c2n oracle := by simp [c_oracle]
@[simp] theorem c_oracle_evp' {O} : evalp O c_oracle = fun _:ℕ => c2n (oracle) := by funext x; simp
@[simp] theorem c_oracle_ev {O x} : eval O c_oracle x = c2n oracle := by rw [← evalp_eq_eval c_oracle_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_oracle {O} : Nat.PrimrecIn O (fun _:ℕ => c2n oracle) := by rw [←c_oracle_evp']; exact code_prim_prop

def c_pair := c_add.comp₂ (c_mul2.comp $ c_mul2) (c_const 5)
@[cp] theorem c_pair_prim : code_prim c_pair := by unfold c_pair; apply_cp
@[simp] theorem c_pair_evp {O a b} : evalp O c_pair ⟪a, b⟫ = c2n (pair (n2c a) (n2c b)) := by simp [c2n, c_pair, Nat.mul_comm]
@[simp] theorem c_pair_evp' {O} : evalp O c_pair = fun ab:ℕ => c2n (pair (n2c ab.l) (n2c ab.r)) := by simp [c2n, c_pair, Nat.mul_comm]
@[simp] theorem c_pair_ev {O a b} : eval O c_pair ⟪a, b⟫ = c2n (pair (n2c a) (n2c b)) := by rw [← evalp_eq_eval c_pair_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_pair {O} : Nat.PrimrecIn O (fun ab:ℕ => c2n (pair (n2c ab.l) (n2c ab.r))) := by rw [←c_pair_evp']; exact code_prim_prop

def c_comp := c_add.comp₂ (c_mul2.comp $ c_mul2) (c_const 6)
@[cp] theorem c_comp_prim : code_prim c_comp := by unfold c_comp; apply_cp
@[simp] theorem c_comp_evp {O a b} : evalp O c_comp ⟪a, b⟫ = c2n (comp (n2c a) (n2c b)) := by simp [c2n, c_comp, Nat.mul_comm]
@[simp] theorem c_comp_evp' {O} : evalp O c_comp = fun ab:ℕ => c2n (comp (n2c ab.l) (n2c ab.r)) := by simp [c2n, c_comp, Nat.mul_comm]
@[simp] theorem c_comp_ev {O a b} : eval O c_comp ⟪a, b⟫ = c2n (comp (n2c a) (n2c b)) := by rw [← evalp_eq_eval c_comp_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_comp {O} : Nat.PrimrecIn O (fun ab:ℕ => c2n (comp (n2c ab.l) (n2c ab.r))) := by rw [←c_comp_evp']; exact code_prim_prop

def c_prec := c_add.comp₂ (c_mul2.comp $ c_mul2) (c_const 7)
@[cp] theorem c_prec_prim : code_prim c_prec := by unfold c_prec; apply_cp
@[simp] theorem c_prec_evp {O a b} : evalp O c_prec ⟪a, b⟫ = c2n (prec (n2c a) (n2c b)) := by simp [c2n, c_prec, Nat.mul_comm]; exact rfl
@[simp] theorem c_prec_evp' {O} : evalp O c_prec = fun ab:ℕ => c2n (prec (n2c ab.l) (n2c ab.r)) := by simp [c2n, c_prec, Nat.mul_comm]; exact rfl
@[simp] theorem Nat.PrimrecIn.c_prec {O} : Nat.PrimrecIn O (fun ab:ℕ => c2n (prec (n2c ab.l) (n2c ab.r))) := by rw [←c_prec_evp']; exact code_prim_prop
@[simp] theorem c_prec_ev {O a b} : eval O c_prec ⟪a, b⟫ = c2n (prec (n2c a) (n2c b)) := by rw [← evalp_eq_eval c_prec_prim]; simp

def c_rfind' := c_add.comp₂ (c_mul2.comp $ c_mul2) (c_const 8)
@[cp] theorem c_rfind'_prim : code_prim c_rfind' := by unfold c_rfind'; apply_cp
@[simp] theorem c_rfind'_evp {O c} : evalp O c_rfind' c = c2n (rfind' $ n2c c) := by simp [c2n, c_rfind', Nat.mul_comm]; exact rfl
@[simp] theorem c_rfind'_ev {O c} : eval O c_rfind' c = c2n (rfind' $ n2c c) := by rw [← evalp_eq_eval c_rfind'_prim]; simp

def c_c_const := (c_nat_iterate (c_comp.comp₂ (c_const $ c2n succ) (c_id))).comp₂ zero c_id
@[cp] theorem c_c_const_prim : code_prim c_c_const := by unfold c_c_const; apply_cp
@[simp] theorem c_c_const_evp : evalp O c_c_const n = c2n (c_const n) := by
  unfold c_const
  unfold c_c_const
  simp
  induction n with
  | zero => simp [c2n]
  | succ n ih =>
    simp [Function.iterate_succ', -Function.iterate_succ]
    rw [ih]
    apply Eq.symm
    rw [c_const.eq_def] -- bug? cant rw without the eq.symm, even with occs
    simp only [n2c_c2n]
theorem c_c_const_evp' {O} : evalp O c_c_const = c_const := by
  funext x
  simp
  exact rfl
@[simp] theorem c_c_const_ev {O c} : eval O c_c_const c = c2n (c_const c) := by rw [← evalp_eq_eval c_c_const_prim]; simp
@[simp] theorem Nat.PrimrecIn.c_const:Nat.PrimrecIn O c_const := by rw [← c_c_const_evp']; exact code_prim_prop

def c_ev_const := c_comp.comp₂ left (c_c_const.comp right)
@[cp] theorem c_ev_const_prim : code_prim c_ev_const := by unfold c_ev_const; apply_cp
theorem c_ev_const_evp' {O} : evalp O c_ev_const x = c2n (comp (n2c x.l) (c_const x.r)) := by simp [c_ev_const]
@[simp] theorem c_ev_const_evp : evalp O c_ev_const ⟪e, x⟫ = c2n (comp (n2c e) (c_const x)) := by simp [c_ev_const_evp']
theorem c_ev_const_ev':eval O c_ev_const x = c2n (comp (n2c x.l) (c_const x.r)) := by rw [← evalp_eq_eval c_ev_const_prim]; simp [c_ev_const_evp']
@[simp] theorem c_ev_const_ev {O x} : eval O c_ev_const ⟪e, x⟫ = c2n (comp (n2c e) (c_const x)) := by rw [← evalp_eq_eval c_ev_const_prim]; simp
end Computability.Code
end constructors

section c_comp₂
def c_comp₂ :=
  let a := left
  let b := left.comp right
  let c := right.comp right
  c_comp.comp₂ a $ c_pair.comp₂ b c
@[cp] theorem c_comp₂_prim : code_prim c_comp₂ := by unfold c_comp₂; apply_cp
@[simp] theorem c_comp₂_evp : evalp O c_comp₂ ⟪a,b,c⟫ = c2n (comp₂ a b c) := by
  simp [c_comp₂]; rfl
@[simp] theorem c_comp₂_ev {O a b c} : eval O c_comp₂ ⟪a,b,c⟫ = c2n (comp₂ a b c) := by rw [← evalp_eq_eval c_comp₂_prim]; simp
end c_comp₂
section c_comp₃
def c_comp₃ :=
  let a := left.comp left
  let b := left.comp right
  let c := right.comp left
  let d := right.comp right
  c_comp.comp₂ (a) (c_pair.comp₂ c (c_pair.comp₂ b d))
@[cp] theorem c_comp₃_prim : code_prim c_comp₃ := by unfold c_comp₃; apply_cp
@[simp] theorem c_comp₃_evp : evalp O c_comp₃ ⟪⟪a,b⟫,⟪c,d⟫⟫ = c2n (comp₃ a b c d) := by
  simp [c_comp₃]; rfl
@[simp] theorem c_comp₃_ev {O a b c d} : eval O c_comp₃ ⟪⟪a,b⟫,⟪c,d⟫⟫ = c2n (comp₃ a b c d) := by rw [← evalp_eq_eval c_comp₃_prim]; simp
end c_comp₃

section c_c_rfind
@[irreducible] def c_c_rfind := c_comp.comp₂ c_rfind' (c_pair.comp₂ (c_const c_id) (c_zero))
@[cp] theorem c_c_rfind_prim : code_prim c_c_rfind := by unfold c_c_rfind; apply_cp
@[simp] theorem c_c_rfind_evp : evalp O c_c_rfind = λ x:ℕ => c2n (c_rfind x) := by simp [c_c_rfind, c_rfind]
end c_c_rfind

def c_dovetailn :=
  c_c_rfind.comp $
  c_comp₂.comp₃
  (c_const c_if_eq')
  (c_comp₃.comp₄ (c_const c_evaln) (c_pair.comp₂ c_left (c_comp.comp₂ c_left c_right)) (c_c_const) (c_comp.comp₂ c_right c_right))
  (c_const (c_const 1))
@[cp] theorem c_dovetailn_prim : code_prim c_dovetailn := by unfold c_dovetailn; apply_cp
@[simp] theorem c_dovetailn_evp : evalp O c_dovetailn = λ x ↦ c2n (dovetailn $ n2c x) := by
  -- just doing simp [c_dovetailn, dovetailn] should work, but gives a kernel recursion error. why?
  -- this was fixed by moving simp from def of comp_n to the comp_n_evp theorems.
  simp [c_dovetailn, dovetailn]
def c_dovetail := c_comp.comp₂ c_left c_dovetailn
@[cp] theorem c_dovetail_prim : code_prim c_dovetail := by unfold c_dovetail; apply_cp
@[simp] theorem c_dovetail_evp : evalp O c_dovetail = λ x ↦ c2n (dovetail $ n2c x) := by
  simp [c_dovetail, dovetail]

def c_c_ifdom :=
  c_comp₂.comp₃ (c_const c_add) (c_comp.comp₂ c_zero left) (right)
@[cp] theorem c_c_ifdom_prim : code_prim c_c_ifdom := by unfold c_c_ifdom; apply_cp
@[simp] theorem c_c_ifdom_evp : evalp O c_c_ifdom = λ x ↦ c2n (c_ifdom x.l x.r) := by
  simp [c_c_ifdom, c_ifdom]
