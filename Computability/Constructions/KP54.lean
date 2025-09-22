import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.KP54

open Nat.RecursiveIn.Code
open Computability

section kp54
-- namespace Nat.RecursiveIn.Code

-- def c_kp54 := zero

-- theorem c_kp54_ev : eval (K0 Nat.fzero) c_kp54 = KP54 := by sorry

def c_c_kp54_aux :=
  zero
@[simp] theorem c_c_kp54_aux_evp : eval_prim O c_c_kp54_aux (Nat.pair i n) = dovetail (KP54.c_kp54_aux i n) := by sorry
def c_c_evals :=
  zero
@[simp] theorem c_c_evals_evp : eval_prim O c_c_evals x = c_evals := by sorry

#check c_evals
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
      let rf := left.comp (c_pred.comp q0)
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
      let rf := left.comp (c_pred.comp q0)
      let Bₛ := c_list_append.comp₂ Bₚ (succ.comp rf)
      let B_result := c_pred.comp $ oracle.comp₂ c_c_evals (pair Bₛ (pair i la))
      pair (c_list_concat.comp₂ Aₚ (c_sg'.comp B_result)) Bₛ
    )
  )
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
  | succ s_1 ih =>
    unfold c_kp54
    simp
    have : (Nat.rec 0 (fun y IH ↦ eval_prim (K0 Nat.fzero) c_kp54_main (Nat.pair y IH)) s_1) = eval_prim (K0 Nat.fzero) c_kp54 s_1 := by
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

    have hs : eval_prim (K0 Nat.fzero) s inp = s_1 := by simp [s, inp]
    have hi : eval_prim (K0 Nat.fzero) i inp = i_1 := by simp [i, i_1, hs]
    have hKP54s : eval_prim (K0 Nat.fzero) KP54s inp = KP54.KP54 s_1 := by simp [KP54s, inp]
    have hAₚ : eval_prim (K0 Nat.fzero) Aₚ inp = Aₚ_1 := by simp [Aₚ, Aₚ_1, hKP54s]
    have hBₚ : eval_prim (K0 Nat.fzero) Bₚ inp = Bₚ_1 := by simp [Bₚ, Bₚ_1, hKP54s]
    have hla : eval_prim (K0 Nat.fzero) la inp = la_1 := by simp [la, la_1, hAₚ]
    have hlb : eval_prim (K0 Nat.fzero) lb inp = lb_1 := by simp [lb, lb_1, hBₚ]

    simp (config := {zeta:=false}) [←hinp]
    simp (config := {zeta:=false}) [hs]
    split
    next h0 =>
      split
      next h1 =>
        have : ¬ dvt.Dom := by simp [q0, hi, hlb, hAₚ] at h1; exact h1
        simp (config := {zeta:=false}) [this, hAₚ, hBₚ]
      next h1 =>
        have : dvt.Dom := by simp [q0, hi, hlb, hAₚ] at h1; exact h1
        simp (config := {zeta:=false}) [this]
        lift_lets; extract_lets; expose_names
        have hrf : eval_prim (K0 Nat.fzero) rf inp = rf_2 := by
          simp [rf, rf_2,q0]
          split
          next h2 => simp [hi, hlb, hAₚ]; congr
          next h2 =>
            simp [hi, hlb, hAₚ] at h2
            simp [dvt, h2] at this
        have hAₛ : eval_prim (K0 Nat.fzero) Aₛ inp = Aₛ_1 := by simp [Aₛ, Aₛ_1, hAₚ, hrf, -Denumerable.list_ofNat_succ]
        have hA_result : eval_prim (K0 Nat.fzero) A_result inp = A_result_1 := by
          simp [A_result, A_result_1]
          split
          next h2 => simp [hAₛ, hi, hlb]
          next h2 =>
            -- this case is a contradiction, as we know the evals must halt from "this".
            simp [dvt] at this
            simp [hAₛ, hi, hlb] at h2
            have contra : (evals Aₛ_1 (decodeCode i_1) lb_1).Dom := by
              have a0 := dovetail_ev_0' this
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
        have hrf : eval_prim (K0 Nat.fzero) rf_1 inp = rf_2 := by
          simp [rf_1, rf_2,q0_1]
          split
          next h2 => simp [hi]; congr
          next h2 =>
            simp [hi, hla, hBₚ] at h2
            simp [dvt_1, h2] at this
        have hBₛ : eval_prim (K0 Nat.fzero) Bₛ inp = Bₛ_1 := by simp [Bₛ, Bₛ_1, hBₚ, hrf, -Denumerable.list_ofNat_succ]
        have hB_result : eval_prim (K0 Nat.fzero) B_result inp = B_result_1 := by
          simp [B_result, B_result_1]
          split
          next h2 => simp [hBₛ, hi, hla]
          next h2 =>
            -- this case is a contradiction, as we know the evals must halt from "this".
            simp [dvt_1] at this
            simp [hBₛ, hi, hla] at h2
            have contra : (evals Bₛ_1 (decodeCode i_1) la_1).Dom := by
              have a0 := dovetail_ev_0' this
              simp [KP54.c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at a0
              exact a0
            simp [contra] at h2
        simp [hBₛ, hAₚ, hB_result]


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
