/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
-- import Computability.Label
import Computability.Oracle
import Computability.Constructions.Eval_Aux
import Mathlib.Computability.RecursiveIn

/-!
# Notations, helper functions

In this file we define helper functions which will be used in later computability arguments.
-/

open Nat Oracle.Single

theorem SingleReducibleIff (O : ℕ → ℕ) (f : ℕ →. ℕ) :
    Oracle.Single.RecursiveIn O f ↔ Nat.RecursiveIn ({↑O}:(Set (ℕ →. ℕ))) f := by
  constructor
  · intro h
    induction h with
    | zero => exact Nat.RecursiveIn.zero
    | succ => exact Nat.RecursiveIn.succ
    | left => exact Nat.RecursiveIn.left
    | right => exact Nat.RecursiveIn.right
    | oracle => exact Nat.RecursiveIn.oracle (↑O) rfl
    | pair hf hh hf_ih hh_ih => exact Nat.RecursiveIn.pair hf_ih hh_ih
    | comp hf hh hf_ih hh_ih => exact Nat.RecursiveIn.comp hf_ih hh_ih
    | prec hf hh hf_ih hh_ih => exact Nat.RecursiveIn.prec hf_ih hh_ih
    | rfind hf ih => sorry
  · intro h
    induction h with
    | zero => exact Oracle.Single.RecursiveIn.zero
    | succ => exact Oracle.Single.RecursiveIn.succ
    | left => exact Oracle.Single.RecursiveIn.left
    | right => exact Oracle.Single.RecursiveIn.right
    | oracle g hg =>
      have : g = O := by simp_all only [Set.mem_singleton_iff]
      rw [this]
      exact Oracle.Single.RecursiveIn.oracle
    | pair hf hh hf_ih hh_ih => exact Oracle.Single.RecursiveIn.pair hf_ih hh_ih
    | comp hf hh hf_ih hh_ih => exact Oracle.Single.RecursiveIn.comp hf_ih hh_ih
    | prec hf hh hf_ih hh_ih => exact Oracle.Single.RecursiveIn.prec hf_ih hh_ih
    | rfind hf ih => exact Code.rfind_real ih
