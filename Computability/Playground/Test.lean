import Computability.Constructions.EvalString
import Computability.SetOracles

namespace Nat.RecursiveIn.Code
open Classical
@[irreducible] noncomputable def c_kp54_aux (i n:ℕ) :=
  zero
  -- c_ifdom
  -- (c_evals.comp₃ (c_list_append.comp₂ left (succ.comp right)) (c_const i) (c_const n))
  -- zero

theorem c_kp54_aux_evp :
  eval Nat.fzero (c_kp54_aux i n) x
    =
  if (evals ((n2l x.l) ++ (n2l (x.r+1))) i n).Dom then Part.some 0 else Part.none
:= by
  sorry
theorem c_kp54_aux_2 (halts:(eval Nat.fzero (dovetail (c_kp54_aux i lb)) Aₚ).Dom) :
  let dvt := (eval Nat.fzero (dovetail (c_kp54_aux i lb)) Aₚ).get halts
  (evals ((n2l Aₚ) ++ (n2l (dvt.l+1))) i lb).Dom := by
    have := dovetail_ev_0' halts
    extract_lets at this ⊢
    expose_names
    simp only [c_kp54_aux_evp] at this
    contrapose this
    simp [-Denumerable.list_ofNat_succ]
    exact this

def dovetail2 (c:Code) : Code :=
  -- c_rfind $
  -- (pair c_evaln zero)
  c_evaln
  -- zero
  -- c_if_eq'.comp₂
  -- (c_evaln.comp₃ (zero) (zero) (zero))
  -- (c_evaln.comp (zero))
  -- (c_const 1)
@[irreducible] noncomputable def c_evaln2 : Code := c_evaln
open Nat List in
noncomputable def KP54 : ℕ→ℕ := λ s ↦
  if s=0 then Nat.pair 0 0 else

  -- let i  := (s-1).div2
  let Aₚ := (KP54 (s-1)).l
  -- let Bₚ := (KP54 (s-1)).r
  -- let lb := List.length (n2l Bₚ)
  -- let la := List.length (n2l Aₚ)

  -- let dvt := eval Nat.fzero (dovetail (c_kp54_aux i lb)) Aₚ
  let dvt := eval Nat.fzero ((c_evaln.comp $ c_evaln.comp $ c_evaln.comp $ c_evaln.comp $ c_evaln.comp $ c_evaln.comp $ c_add.comp $ c_add.comp c_add)) Aₚ
  
  if halts:dvt.Dom then
    let rf := (dvt.get halts).l -- rf is a natural such that (eval_string ((n2l A) ++ (n2l rf)) i n).Dom.
    rf
    -- 9
    -- rf
    -- let Aₛ := (n2l Aₚ) ++ (n2l (rf+1))
    -- l2n Aₛ
    -- let A_result := (evals Aₛ i lb).get (c_kp54_aux_2 halts)
    -- A_result
    -- Nat.pair Aₛ ((n2l Bₚ).concat (Nat.sg' A_result))
  else
    0
  -- if s%2=0 then -- then s=2i+2, and we will work on Rᵢ.
  -- else -- then s=2i+1, and we will work on Sᵢ.
  --   0
    -- let dvt := eval Nat.fzero (dovetail (c_kp54_aux i la)) Bₚ
    -- if halts:dvt.Dom then
    --   let rf := (dvt.get halts).l
    --   let Bₛ := (n2l Bₚ) ++ (n2l (rf+1))
    --   let B_result := (evals (Bₛ) i la).get (c_kp54_aux_2 halts)
    --   Nat.pair ((n2l Aₚ).concat (Nat.sg' B_result)) Bₛ
    -- else
    --   Nat.pair (l2n $ (n2l Aₚ).concat 0) (l2n $ (n2l Bₚ).concat 0)
#exit
set_option maxRecDepth 250 in
@[simp] theorem c_evaln_aux_ev_pr:code_prim (c_evaln_aux) := by
  unfold c_evaln_aux;
  lift_lets
  extract_lets
  expose_names
  
  have cp_code_s : code_prim code_s := by
    -- aesop
    aesop
  have cp_code : code_prim code := by aesop
  have cp_s : code_prim s := by aesop
  have cp_sM1 : code_prim sM1 := by aesop
  have cp_comp_hist : code_prim comp_hist := by aesop
  have cp_n : code_prim n := by aesop
  have cp_m : code_prim m := by aesop
  have cp_ml : code_prim ml := by aesop
  have cp_mr : code_prim mr := by aesop
  have cp_nMod4 : code_prim nMod4 := by aesop

  have cp_ele : code_prim ele := by aesop
  have cp_opt_zero : code_prim opt_zero := by aesop
  have cp_opt_succ : code_prim opt_succ := by aesop
  have cp_opt_left : code_prim opt_left := by aesop
  have cp_opt_right : code_prim opt_right := by aesop
  have cp_opt_oracle : code_prim opt_oracle := by aesop

  have cp_zero_mapped : code_prim zero_mapped := by aesop
  have cp_succ_mapped : code_prim succ_mapped := by aesop
  have cp_left_mapped : code_prim left_mapped := by aesop
  have cp_right_mapped : code_prim right_mapped := by aesop
  have cp_oracle_mapped : code_prim oracle_mapped := by aesop
  
  have cp_lookup {x' c' s'} (hx':code_prim x') (hc':code_prim c') (hs':code_prim s') : code_prim (lookup x' c' s') := by aesop
  
  -- set_option trace.aesop true in
  have cp_opt_pair : code_prim opt_pair := by aesop (config:={enableSimp := false})
  have cp_pair_mapped : code_prim pair_mapped := by aesop
  have cp_opt_comp : code_prim opt_comp := by aesop
  have cp_comp_mapped : code_prim comp_mapped := by aesop

  have cp_prec_x : code_prim prec_x := by aesop
  have cp_prec_i : code_prim prec_i := by aesop
  have cp_prec_iM1 : code_prim prec_iM1 := by aesop
  have cp_prec_base_case : code_prim prec_base_case := by aesop
  have cp_prec_prev_case : code_prim prec_prev_case := by aesop
  have cp_prec_inductive_case : code_prim prec_inductive_case := by aesop
  have cp_opt_prec : code_prim opt_prec := by aesop
  have cp_prec_mapped : code_prim prec_mapped := by aesop
  have cp_rfind'_base : code_prim rfind'_base := by aesop
  have cp_rfind'_indt : code_prim rfind'_indt := by aesop
  have cp_opt_rfind' : code_prim opt_rfind' := by aesop
  have cp_rfind'_mapped : code_prim rfind'_mapped := by aesop
  
  aesop
@[simp] theorem c_evaln_ev_pr:code_prim (c_evaln) := by
  unfold c_evaln;
  aesop
