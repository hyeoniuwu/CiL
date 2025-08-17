import Computability.Constructions.Eval

namespace Nat.RecursiveIn.Code

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
