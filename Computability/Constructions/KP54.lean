import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.KP54

open Computability.Code
open Computability

section kp54

@[irreducible] def c_c_rfind := c_comp.comp₂ c_rfind' (c_pair.comp₂ (c_const c_id) (c_zero))
@[cp] theorem c_c_rfind_ev_pr : code_prim c_c_rfind := by
  unfold c_c_rfind
  apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_c_rfind_evp : eval_prim O c_c_rfind = fun x:ℕ => c2n (c_rfind x) := by simp [c_c_rfind, c_rfind]
def c_dovetail :=
  c_c_rfind.comp $
  c_comp₂.comp₃
  (c_const c_if_eq')
  (c_comp₃.comp₄ (c_const c_evaln) (c_pair.comp₂ c_left (c_comp.comp₂ c_left c_right)) (c_c_const) (c_comp.comp₂ c_right c_right))
  (c_const (c_const 1))
@[cp] theorem c_dovetail_ev_pr : code_prim c_dovetail := by
  unfold c_dovetail
  apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_dovetail_evp : eval_prim O c_dovetail = λ x ↦ c2n (dovetail $ n2c x) := by
  -- just doing simp [c_dovetail, dovetail] should work, but gives a kernel recursion error. why?
  -- this was fixed by moving simp from def of comp_n to the comp_n_evp theorems.
  simp [c_dovetail, dovetail]


def c_c_evals :=
  c_comp₃.comp₄
  (c_const c_evalo)
  (c_const c_c_evals_oracle)
  (c_const $ c_const c_evals_code)
  (c_const c_id)
@[cp] theorem c_c_evals_ev_pr : code_prim c_c_evals := by
  unfold c_c_evals
  apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_c_evals_evp : eval_prim O c_c_evals x = c_evals := by simp [c_c_evals, c_evals]
def c_c_ifdom :=
  c_comp₂.comp₃ (c_const c_add) (c_comp.comp₂ c_zero left) (right)
@[cp] theorem c_c_ifdom_ev_pr : code_prim c_c_ifdom := by
  unfold c_c_ifdom
  apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_c_ifdom_evp : eval_prim O c_c_ifdom = λ x ↦ c2n (c_ifdom x.l x.r) := by
  simp [c_c_ifdom, c_ifdom]
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
@[cp] theorem c_c_kp54_aux_ev_pr : code_prim c_c_kp54_aux := by
  unfold c_c_kp54_aux
  apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

@[simp] theorem c_c_kp54_aux_evp : eval_prim O c_c_kp54_aux = λ x:ℕ ↦ c2n (dovetail (KP54.c_kp54_aux x.l x.r)) := by
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
def c_kp54 :=
  (
    prec
    zero $
    c_kp54_main.comp right
  ).comp₂ zero c_id
-- theorem c_kp54_t : code_total O c_kp54 := by sorry

@[cp] theorem c_kp54_ev_pr : code_prim c_kp54 := by
  unfold c_kp54
  unfold c_kp54_main
  extract_lets
  expose_names

  have cp_s : code_prim s := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_KP54s : code_prim KP54s := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_i : code_prim i := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_Aₚ : code_prim Aₚ := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_Bₚ : code_prim Bₚ := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_lb : code_prim lb := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_la : code_prim la := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_q0 : code_prim q0 := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_rf : code_prim rf := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_Aₛ : code_prim Aₛ := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_A_result : code_prim A_result := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_q0_1 : code_prim q0_1 := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_rf_1 : code_prim rf_1 := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_Bₛ : code_prim Bₛ := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_B_result : code_prim B_result := by apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

  apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

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
        have : ¬ dvt.Dom := by
          simp [q0, hi, hlb, hAₚ] at h1;
          exact h1
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
            have contra : (evals Aₛ_1 (n2c i_1) lb_1).Dom := by
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
            have contra : (evals Bₛ_1 (n2c i_1) la_1).Dom := by
              have a0 := dovetail_ev_0' this
              simp [KP54.c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at a0
              exact a0
            simp [contra] at h2
        simp [hBₛ, hAₚ, hB_result]


-- theorem c_kp54_ev : (eval (∅⌜) c_kp54 x).get (c_kp54_t x) = KP54.KP54 x := by sorry

section n2b
namespace Computability.Code
def c_n2b := c_sg
@[cp] theorem c_n2b_ev_pr : code_prim c_n2b := by
  unfold c_n2b
  apply_rules (config := {maxDepth:=10, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_n2b_evp:eval_prim O c_n2b = fun x => if n2b x = true then 1 else 0 := by
  simp [c_n2b]
  unfold Nat.sg; unfold n2b
  aesop
@[simp] theorem c_n2b_ev:eval O c_n2b = fun x => if n2b x = true then 1 else 0 := by rw [← eval_prim_eq_eval c_n2b_ev_pr]; simp only [c_n2b_evp]; funext x; aesop
end Computability.Code
-- theorem Nat.PrimrecIn.n2b:Nat.PrimrecIn O Nat.n2b := by ...
-- theorem Nat.Primrec.n2b:Nat.Primrec Nat.n2b := by ...
end n2b

@[simp] theorem getI_eq_getElem {l:List ℕ} {h:i<l.length} : l.getI i = l[i] := by
  unfold List.getI
  simp [h]

theorem fzero_eq_χempty : Nat.fzero = χ ∅ := by unfold χ; simp

def c_kp54_A := c_n2b.comp $ c_list_getI.comp₂ (left.comp $ c_kp54.comp succ) c_id
@[cp] theorem c_kp54_A_ev_pr : code_prim c_kp54_A := by
  unfold c_kp54_A
  apply_rules (config := {maxDepth:=20, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_kp54_A_evp : eval_prim (K0 Nat.fzero) c_kp54_A = χ KP54.A := by
  funext x
  simp [c_kp54_A]; congr
  exact getI_eq_getElem
@[simp] theorem c_kp54_A_ev :eval (K0 Nat.fzero) c_kp54_A = χ KP54.A := by simp [← eval_prim_eq_eval c_kp54_A_ev_pr];
theorem A_le_J1_aux : (χ KP54.A) ≤ᵀᶠ K0 Nat.fzero := exists_code.mpr ⟨c_kp54_A, c_kp54_A_ev⟩
theorem A_le_J1 : KP54.A ≤ᵀ ∅⌜ := by
  apply TR_Set_iff_Fn.mpr
  apply _root_.trans (A_le_J1_aux)
  rw [fzero_eq_χempty]
  exact (K0χ_eq_χSetK ∅).1
def c_kp54_B := c_n2b.comp $ c_list_getI.comp₂ (right.comp $ c_kp54.comp succ) c_id
@[cp] theorem c_kp54_B_ev_pr : code_prim c_kp54_B := by
  unfold c_kp54_B
  apply_rules (config := {maxDepth:=20, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_kp54_B_evp : eval_prim (K0 Nat.fzero) c_kp54_B = χ KP54.B := by
  funext x
  simp [c_kp54_B]; congr
  exact getI_eq_getElem
@[simp] theorem c_kp54_B_ev :eval (K0 Nat.fzero) c_kp54_B = χ KP54.B := by simp [← eval_prim_eq_eval c_kp54_B_ev_pr];
theorem B_le_J1_aux : (χ KP54.B) ≤ᵀᶠ K0 Nat.fzero := exists_code.mpr ⟨c_kp54_B, c_kp54_B_ev⟩
theorem B_le_J1 : KP54.B ≤ᵀ ∅⌜ := by
  apply TR_Set_iff_Fn.mpr
  apply _root_.trans (B_le_J1_aux)
  rw [fzero_eq_χempty]
  exact (K0χ_eq_χSetK ∅).1

-- end Computability.Code
end kp54


theorem ex_incomparable_sets : ∃ A B:Set ℕ, A≤ᵀ∅⌜ ∧ B≤ᵀ∅⌜ ∧ A|ᵀB := by
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
    have contrad := KP54.S c
    exact contrad hc
  · change ¬SetTuringReducible KP54.B KP54.A
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    have contrad := KP54.R c
    exact contrad hc
