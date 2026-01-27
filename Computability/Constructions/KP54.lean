/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.EvalString
import Computability.Constructions.Meta
import Computability.SetOracles
import Computability.KP54

open Computability.Code
open Computability

section kp54

/-- `[c_c_kp54_aux](i, n) = c2n (dovetail (c_kp54_aux i n))` -/
def c_c_kp54_aux :=
  c_dovetail.comp $
  c_c_ifdom.comp₂
  (
    c_comp₃.comp₄
    c_c_evals
    (c_comp₂.comp₃ (c_const c_list_append) (c_left) (c_comp.comp₂ c_succ c_right))
    (c_c_const.comp left)
    (c_c_const.comp right)
  )
  c_zero
@[cp] theorem c_c_kp54_aux_prim : code_prim c_c_kp54_aux := by unfold c_c_kp54_aux; apply_cp
@[simp] theorem c_c_kp54_aux_evp : evalp O c_c_kp54_aux = λ x:ℕ ↦ c2n (dovetail (KP54.c_kp54_aux x.l x.r)) := by
  simp [c_c_kp54_aux, KP54.c_kp54_aux]

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
    let q0 := oracle.comp₂ (c_c_kp54_aux.comp₂ i lb) Aₚ
    c_ifz.comp₃ q0
    (pair (c_list_concat.comp₂ Aₚ zero) (c_list_concat.comp₂ Bₚ zero))
    (
      let rf := c_pred.comp q0
      let Aₛ := c_list_append.comp₂ Aₚ (succ.comp rf)
      let A_result := c_pred.comp $ oracle.comp₂ c_c_evals (pair Aₛ (pair i lb))
      pair Aₛ (c_list_concat.comp₂ Bₚ (c_sg'.comp A_result))
    )
  )
  (
    let q0 := oracle.comp₂ (c_c_kp54_aux.comp₂ i la) Bₚ
    c_ifz.comp₃ q0
    (pair (c_list_concat.comp₂ Aₚ zero) (c_list_concat.comp₂ Bₚ zero))
    (
      let rf := c_pred.comp q0
      let Bₛ := c_list_append.comp₂ Bₚ (succ.comp rf)
      let B_result := c_pred.comp $ oracle.comp₂ c_c_evals (pair Bₛ (pair i la))
      pair (c_list_concat.comp₂ Aₚ (c_sg'.comp B_result)) Bₛ
    )
  )
def c_kp54 :=
  (
    prec
    zero $
    c_kp54_main.comp right
  ).comp₂ zero c_id

@[cp] theorem c_kp54_prim : code_prim c_kp54 := by
  unfold c_kp54
  unfold c_kp54_main
  extract_lets
  expose_names

  have cp_s : code_prim s := by apply_cp
  have cp_KP54s : code_prim KP54s := by apply_cp
  have cp_i : code_prim i := by apply_cp
  have cp_Aₚ : code_prim Aₚ := by apply_cp
  have cp_Bₚ : code_prim Bₚ := by apply_cp
  have cp_lb : code_prim lb := by apply_cp
  have cp_la : code_prim la := by apply_cp
  have cp_q0 : code_prim q0 := by apply_cp
  have cp_rf : code_prim rf := by apply_cp
  have cp_Aₛ : code_prim Aₛ := by apply_cp
  have cp_A_result : code_prim A_result := by apply_cp
  have cp_q0_1 : code_prim q0_1 := by apply_cp
  have cp_rf_1 : code_prim rf_1 := by apply_cp
  have cp_Bₛ : code_prim Bₛ := by apply_cp
  have cp_B_result : code_prim B_result := by apply_cp

  apply_cp 60

@[simp] theorem c_kp54_evp : evalp (K0 (λ_↦0)) c_kp54 x = KP54.KP54 x := by
  induction x with
  | zero =>
    simp [c_kp54]
    unfold KP54.KP54
    rfl
  | succ s_1 ih =>
    unfold c_kp54
    simp
    have : (Nat.rec 0 (fun y IH ↦ evalp (K0 (λ_↦0)) c_kp54_main (Nat.pair y IH)) s_1) = evalp (K0 (λ_↦0)) c_kp54 s_1 := by
      unfold c_kp54
      cases s_1 <;> simp
    -- we are careful with the rewriting/unfolding order here.
    rewrite [this]; clear this
    unfold c_kp54_main
    lift_lets; extract_lets; expose_names
    unfold KP54.KP54
    rw [ih]; clear ih
    lift_lets; extract_lets; expose_names

    let (eq:=hinp) inp := (Nat.pair s_1 (KP54.KP54 s_1))

    have hs : evalp (K0 (λ_↦0)) s inp = s_1 := by simp [s, inp]
    have hi : evalp (K0 (λ_↦0)) i inp = i_1 := by simp [i, i_1, hs]
    have hKP54s : evalp (K0 (λ_↦0)) KP54s inp = KP54.KP54 s_1 := by simp [KP54s, inp]
    have hAₚ : evalp (K0 (λ_↦0)) Aₚ inp = Aₚ_1 := by simp [Aₚ, Aₚ_1, hKP54s]
    have hBₚ : evalp (K0 (λ_↦0)) Bₚ inp = Bₚ_1 := by simp [Bₚ, Bₚ_1, hKP54s]
    have hla : evalp (K0 (λ_↦0)) la inp = la_1 := by simp [la, la_1, hAₚ]
    have hlb : evalp (K0 (λ_↦0)) lb inp = lb_1 := by simp [lb, lb_1, hBₚ]

    simp (config := {zeta:=false}) [←hinp]
    simp (config := {zeta:=false}) [hs]
    split
    next h0 =>
      split
      next h1 =>
        have : ¬ dvt.Dom := by
          simp [q0, hi, hlb, hAₚ] at h1;
          exact h1
        simp (config := {zeta:=false}) [this, hAₚ, hBₚ]
      next h1 =>
        have : dvt.Dom := by simp [q0, hi, hlb, hAₚ] at h1; exact h1
        simp (config := {zeta:=false}) [this]
        lift_lets; extract_lets; expose_names
        have hrf : evalp (K0 (λ_↦0)) rf inp = rf_2 := by
          simp [rf, rf_2,q0]
          split
          next h2 => simp [hi, hlb, hAₚ]; congr
          next h2 =>
            simp [hi, hlb, hAₚ] at h2
            simp [dvt, KP54.finite_ext, h2] at this
        have hAₛ : evalp (K0 (λ_↦0)) Aₛ inp = Aₛ_1 := by simp [Aₛ, Aₛ_1, hAₚ, hrf, -Denumerable.list_ofNat_succ]
        have hA_result : evalp (K0 (λ_↦0)) A_result inp = A_result_1 := by
          simp [A_result, A_result_1]
          split
          next h2 => simp [hAₛ, hi, hlb]
          next h2 =>
            -- this case is a contradiction, as we know the evals must halt from "this".
            simp [dvt] at this
            simp [hAₛ, hi, hlb] at h2
            have contra : (evals Aₛ_1 (n2c i_1) lb_1).Dom := by
              have a0 := dovetail_ev_0 this
              simp [KP54.c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at a0
              exact a0
            simp [contra] at h2
        simp [hAₛ, hBₚ, hA_result]
    -- proof practically idential to above.
    next h0 =>
      split
      next h1 =>
        have : ¬ dvt_1.Dom := by simp [q0_1, hi, hla, hBₚ] at h1; exact h1
        simp (config := {zeta:=false}) [this, hAₚ, hBₚ]
      next h1 =>
        have : dvt_1.Dom := by simp [q0_1, hi, hla, hBₚ] at h1; exact h1
        simp (config := {zeta:=false}) [this]
        lift_lets; extract_lets; expose_names
        have hrf : evalp (K0 (λ_↦0)) rf_1 inp = rf_2 := by
          simp [rf_1, rf_2,q0_1]
          split
          next h2 => simp [hi]; congr
          next h2 =>
            simp [hi, hla, hBₚ] at h2
            simp [dvt_1, KP54.finite_ext, h2] at this
        have hBₛ : evalp (K0 (λ_↦0)) Bₛ inp = Bₛ_1 := by simp [Bₛ, Bₛ_1, hBₚ, hrf, -Denumerable.list_ofNat_succ]
        have hB_result : evalp (K0 (λ_↦0)) B_result inp = B_result_1 := by
          simp [B_result, B_result_1]
          split
          next h2 => simp [hBₛ, hi, hla]
          next h2 =>
            -- this case is a contradiction, as we know the evals must halt from "this".
            simp [dvt_1] at this
            simp [hBₛ, hi, hla] at h2
            have contra : (evals Bₛ_1 (n2c i_1) la_1).Dom := by
              have a0 := dovetail_ev_0 this
              simp [KP54.c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at a0
              exact a0
            simp [contra] at h2
        simp [hBₛ, hAₚ, hB_result]

section n2b
namespace Computability.Code
def c_n2b := c_sg
@[cp] theorem c_n2b_prim : code_prim c_n2b := by unfold c_n2b; apply_cp 10
@[simp] theorem c_n2b_evp:evalp O c_n2b = fun x => if n2b x = true then 1 else 0 := by
  simp [c_n2b]
  unfold Nat.sg; unfold n2b
  aesop
@[simp] theorem c_n2b_ev:eval O c_n2b = fun x => if n2b x = true then 1 else 0 := by rw [← evalp_eq_eval c_n2b_prim]; simp only [c_n2b_evp]; funext x; aesop
end Computability.Code
end n2b

theorem fzero_eq_χempty : (λ_↦0) = χ ∅ := by unfold χ; simp

def c_kp54_A := c_n2b.comp $ c_list_getI.comp₂ (left.comp $ c_kp54.comp succ) c_id
@[cp] theorem c_kp54_A_prim : code_prim c_kp54_A := by unfold c_kp54_A; apply_cp 10
@[simp] theorem c_kp54_A_evp : evalp (K0 (λ_↦0)) c_kp54_A = χ KP54.A := by
  funext x
  simp [c_kp54_A]; congr
  exact getI_eq_getElem
@[simp] theorem c_kp54_A_ev :eval (K0 (λ_↦0)) c_kp54_A = χ KP54.A := by simp [← evalp_eq_eval c_kp54_A_prim];
theorem A_le_J1_aux : (χ KP54.A) ≤ᵀᶠ K0 (λ_↦0) := exists_code.mpr ⟨c_kp54_A, c_kp54_A_ev⟩
theorem A_le_J1 : KP54.A ≤ᵀ ∅⌜ := by
  apply TR_Set_iff_Fn.mpr
  apply _root_.trans (A_le_J1_aux)
  rw [fzero_eq_χempty]
  exact (K0χ_eq_χSetK ∅).1
def c_kp54_B := c_n2b.comp $ c_list_getI.comp₂ (right.comp $ c_kp54.comp succ) c_id
@[cp] theorem c_kp54_B_prim : code_prim c_kp54_B := by unfold c_kp54_B; apply_cp 10
@[simp] theorem c_kp54_B_evp : evalp (K0 (λ_↦0)) c_kp54_B = χ KP54.B := by
  funext x
  simp [c_kp54_B]; congr
  exact getI_eq_getElem
@[simp] theorem c_kp54_B_ev :eval (K0 (λ_↦0)) c_kp54_B = χ KP54.B := by simp [← evalp_eq_eval c_kp54_B_prim];
theorem B_le_J1_aux : (χ KP54.B) ≤ᵀᶠ K0 (λ_↦0) := exists_code.mpr ⟨c_kp54_B, c_kp54_B_ev⟩
theorem B_le_J1 : KP54.B ≤ᵀ ∅⌜ := by
  apply TR_Set_iff_Fn.mpr
  apply _root_.trans (B_le_J1_aux)
  rw [fzero_eq_χempty]
  exact (K0χ_eq_χSetK ∅).1
end kp54


theorem ex_incomparable_sets_below_j1 : ∃ A B:Set ℕ, A≤ᵀ∅⌜ ∧ B≤ᵀ∅⌜ ∧ A|ᵀB := by
  use KP54.A
  use KP54.B
  constructor
  · exact A_le_J1
  constructor
  · exact B_le_J1
  constructor
  · change ¬SetTuringReducible KP54.A KP54.B
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    exact KP54.S c hc
  · change ¬SetTuringReducible KP54.B KP54.A
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    exact KP54.R c hc
