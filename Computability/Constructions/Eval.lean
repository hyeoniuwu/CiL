import Computability.Constructions.CovRec
import Computability.Constructions.Eval_Aux

open List Nat

section evaln
namespace Computability.Code

/--
`eval c_evaln_aux (_, (c,s)) .last = [ [c]ₛ(0), [c]ₛ(1), ..., [c]ₛ(s) ]`
`eval c_evaln_aux (_, (c,s)).last` is the list of computations of code c for s steps on all inputs x=0 to s.
-/
def c_evaln_aux :=
  let code_s  := (succ.comp (left.comp right))
  let code      := left.comp code_s
  let s         := right.comp code_s
  let sM1       := c_pred.comp s
  let comp_hist := right.comp right
  let n         := c_sub.comp₂ code (c_const 5)
  let m         := c_div2.comp $ c_div2.comp n
  let ml        := left.comp m
  let mr        := right.comp m
  let nMod4     := c_mod.comp₂ n (c_const 4)


  let ele := left
-- the opt_* functions will be used with c_list_map'.
-- so, it will take inputs of the form (number in list, covrec_input).
  let opt_zero   := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (zero.comp     ele)
  let opt_succ   := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (succ.comp     ele)
  let opt_left   := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (left.comp     ele)
  let opt_right  := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (right.comp    ele)
  let opt_oracle := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (oracle.comp   ele)

  let zero_mapped := ((c_list_map' opt_zero).comp₂ (c_list_range.comp s) c_id)
  let succ_mapped := ((c_list_map' opt_succ).comp₂ (c_list_range.comp s) c_id)
  let left_mapped := ((c_list_map' opt_left).comp₂ (c_list_range.comp s) c_id)
  let right_mapped := ((c_list_map' opt_right).comp₂ (c_list_range.comp s) c_id)
  let oracle_mapped := ((c_list_map' opt_oracle).comp₂ (c_list_range.comp s) c_id)

  -- `=[c]ₛ(x)`
  let lookup (x' c' s') := c_list_getI.comp₂ (c_list_getI.comp₂ (comp_hist.comp right) (pair c' s')) x'

  let pc_ml_s (c') := lookup (c') (ml.comp right) (s.comp right) -- `[ml]ₛ(x)`
  let pc_mr_s (c') := lookup (c') (mr.comp right) (s.comp right) -- `[mr]ₛ(x)`
  let pc_m_s  (c') := lookup (c') (m.comp  right) (s.comp right) -- `[mr]ₛ(x)`

  -- pair
  let opt_pair := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ (pc_ml_s ele) (c_opt_none) $
    c_ifz.comp₃ (pc_mr_s ele) (c_opt_none) $
    succ.comp (pair (c_opt_iget.comp (pc_ml_s ele)) (c_opt_iget.comp (pc_mr_s ele)))
  let pair_mapped := ((c_list_map' opt_pair).comp₂ (c_list_range.comp s) c_id)

  -- comp: `[ml]ₛ ( [mr]ₛ(x) ) `
  let opt_comp := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ (pc_mr_s ele) (c_opt_none) $
    c_ifz.comp₃ (pc_ml_s $ c_pred.comp (pc_mr_s ele)) (c_opt_none) $
    (pc_ml_s $ c_pred.comp (pc_mr_s ele))
  let comp_mapped := ((c_list_map' opt_comp).comp₂ (c_list_range.comp s) c_id)

  -- prec: if `x.r=n+1`, then `[mr](x.l, (x.r-1, [code](x.l, x.r-1)))` else `[ml](x.l,0)`
  let pc_c_sM1 (c') := lookup (c') (code.comp right) (sM1.comp right) -- `[code]_{s-1}(x)`

  let prec_x   := left.comp ele
  let prec_i   := right.comp ele
  let prec_iM1 := c_pred.comp prec_i

  let prec_base_case      := pc_ml_s prec_x
  let prec_prev_case      := pc_c_sM1 (pair prec_x (prec_iM1))
  let prec_inductive_case := pc_mr_s (pair prec_x (pair prec_iM1 (c_pred.comp prec_prev_case)))

  let opt_prec := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ prec_i prec_base_case $
    c_ifz.comp₃ prec_prev_case (zero) prec_inductive_case
  let prec_mapped := ((c_list_map' opt_prec).comp₂ (c_list_range.comp s) c_id)

  -- rfind
  let rfind'_base := pc_m_s ele
  let rfind'_indt := pc_c_sM1 (pair (left.comp ele) (succ.comp (right.comp ele)))
  let opt_rfind' := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ rfind'_base zero $
    c_ifz.comp₃ (c_pred.comp rfind'_base) (succ.comp $ right.comp ele) rfind'_indt
  let rfind'_mapped := ((c_list_map' opt_rfind').comp₂ (c_list_range.comp s) c_id)


  c_cov_rec

  (c_list_singleton zero) $

  c_if_eq_te.comp₄ s     (c_const 0) (c_list_singleton zero)      $ -- if s=0, then diverge

  c_if_eq_te.comp₄ code  (c_const 0) zero_mapped   $
  c_if_eq_te.comp₄ code  (c_const 1) succ_mapped   $
  c_if_eq_te.comp₄ code  (c_const 2) left_mapped   $
  c_if_eq_te.comp₄ code  (c_const 3) right_mapped  $
  c_if_eq_te.comp₄ code  (c_const 4) oracle_mapped $

  c_if_eq_te.comp₄ nMod4 (c_const 0) pair_mapped   $
  c_if_eq_te.comp₄ nMod4 (c_const 1) comp_mapped   $
  c_if_eq_te.comp₄ nMod4 (c_const 2) prec_mapped   $
                                     rfind'_mapped

/-- api: `Nat.pair x (Nat.pair code s)` -/
def c_evaln :=
  c_list_getI.comp₂ (c_list_getLastI.comp $ c_evaln_aux.comp (pair (c_const 17) right)) left
theorem c_evaln_evp_aux_x_0_0 : eval_prim O (c_evaln) (Nat.pair x (Nat.pair 0 0)) = o2n (evaln O 0 0 x) := by
  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names
  rw [show Nat.pair 0 0 = 0 from rfl]
  simp [getI, evaln] -- doing this simp after cases blows up memory. why?
  cases x with
  | zero => simp
  | succ n => simp

theorem c_evaln_evp_aux_0_np1 : eval_prim O (c_evaln) (Nat.pair x (Nat.pair (n+1) 0)) = o2n (evaln O 0 (n+1:ℕ) x) := by
  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names

  let k:=((Nat.pair (n+1) 0))-1
  have kP1_gt_0 : (Nat.pair (n+1) 0)>0 := by
    apply pair_l_gt0
    exact zero_lt_succ n
  have hkP1: k+1=((Nat.pair (n+1) 0)) := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]

  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k)))
  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k))) = covrec_inp := rfl


  simp
  have stupidrewrite :
  (eval_prim O
  (zero.c_list_singleton.c_cov_rec
  (c_if_eq_te.comp₄ s (c_const 0) zero.c_list_singleton
  (c_if_eq_te.comp₄ code (c_const 0) zero_mapped
  (c_if_eq_te.comp₄ code (c_const 1) succ_mapped
  (c_if_eq_te.comp₄ code (c_const 2) left_mapped
  (c_if_eq_te.comp₄ code (c_const 3) right_mapped
  (c_if_eq_te.comp₄ code (c_const 4) oracle_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 0) pair_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 1) comp_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 2) prec_mapped rfind'_mapped))))))))))
  (Nat.pair 17 k))
  = (eval_prim O c_evaln_aux (Nat.pair 17 k)) := rfl
  simp [stupidrewrite,covrec_inp_simp]

  have hs : eval_prim O s covrec_inp = 0 := by simp [s,code_s,covrec_inp,hkP1]
  simp [hs, getI, evaln]
  cases x <;> simp

theorem c_evaln_evp_aux (hcode_val:code≤4) :
  eval_prim O (c_evaln) (Nat.pair x (Nat.pair code (s+1)))
    =
  o2n (evaln O (s+1) (code:ℕ) x)
  := by

  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names
  simp

  let k:=((Nat.pair code (s + 1)))-1
  have kP1_gt_0 : (Nat.pair code (s + 1))>0 := by
    apply pair_r_gt0
    exact zero_lt_succ s
  have hkP1: k+1=((Nat.pair code (s + 1))) := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]

  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k)))
  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k))) = covrec_inp := rfl

  have stupidrewrite :
  (eval_prim O
  (zero.c_list_singleton.c_cov_rec
  (c_if_eq_te.comp₄ s_1 (c_const 0) zero.c_list_singleton
  (c_if_eq_te.comp₄ code_1 (c_const 0) zero_mapped
  (c_if_eq_te.comp₄ code_1 (c_const 1) succ_mapped
  (c_if_eq_te.comp₄ code_1 (c_const 2) left_mapped
  (c_if_eq_te.comp₄ code_1 (c_const 3) right_mapped
  (c_if_eq_te.comp₄ code_1 (c_const 4) oracle_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 0) pair_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 1) comp_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 2) prec_mapped rfind'_mapped))))))))))
  (Nat.pair 17 k))
  = (eval_prim O c_evaln_aux (Nat.pair 17 k)) := by exact rfl
  simp [stupidrewrite,covrec_inp_simp]

  have hcode_s : eval_prim O code_s covrec_inp = (Nat.pair code (s + 1)) := by simp [code_s,covrec_inp,hkP1]
  have hs      : eval_prim O s_1 covrec_inp = s+1 := by simp [s_1,hcode_s]
  have hsM1    : eval_prim O sM1 covrec_inp = s := by simp [sM1,hs]
  have hcode   : eval_prim O code_1 covrec_inp = code := by simp [code_1,hcode_s]
  have hopt_zero :
    (fun ele => eval_prim O opt_zero (Nat.pair ele covrec_inp))
      =
    (o2n ∘ evaln O (s+1) zero) := by
      funext elem
      simp [opt_zero]
      simp [hsM1,ele]
      simp [evaln]
      cases Classical.em (elem≤s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hopt_succ :
    (fun ele => eval_prim O opt_succ (Nat.pair ele covrec_inp))
      =
    (o2n ∘ evaln O (s+1) succ) := by
      funext elem
      simp [opt_succ]
      simp [hsM1,ele]
      simp [evaln]
      cases Classical.em (elem≤s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hopt_left :
    (fun ele => eval_prim O opt_left (Nat.pair ele covrec_inp))
      =
    (o2n ∘ evaln O (s+1) left) := by
      funext elem
      simp [opt_left]
      simp [hsM1,ele]
      simp [evaln]
      cases Classical.em (elem≤s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hopt_right :
    (fun ele => eval_prim O opt_right (Nat.pair ele covrec_inp))
      =
    (o2n ∘ evaln O (s+1) right) := by
      funext elem
      simp [opt_right]
      simp [hsM1,ele]
      simp [evaln]
      cases Classical.em (elem≤s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hopt_oracle :
    (fun ele => eval_prim O opt_oracle (Nat.pair ele covrec_inp))
      =
    (o2n ∘ evaln O (s+1) oracle) := by
      funext elem
      simp [opt_oracle]
      simp [hsM1,ele]
      simp [evaln]
      cases Classical.em (elem≤s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hzero_mapped:eval_prim O zero_mapped covrec_inp = (map (o2n ∘ evaln O (s+1) zero) (range (s+1))) := by simp [zero_mapped, hs,hopt_zero]
  have hsucc_mapped:eval_prim O succ_mapped covrec_inp = (map (o2n ∘ evaln O (s+1) succ) (range (s+1))) := by simp [succ_mapped, hs,hopt_succ]
  have hleft_mapped:eval_prim O left_mapped covrec_inp = (map (o2n ∘ evaln O (s+1) left) (range (s+1))) := by simp [left_mapped, hs,hopt_left]
  have hright_mapped:eval_prim O right_mapped covrec_inp = (map (o2n ∘ evaln O (s+1) right) (range (s+1))) := by simp [right_mapped, hs,hopt_right]
  have horacle_mapped:eval_prim O oracle_mapped covrec_inp = (map (o2n ∘ evaln O (s+1) oracle) (range (s+1))) := by simp [oracle_mapped, hs,hopt_oracle]

  simp [hs,hcode]

  match code with
  | 0 =>
    simp [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, evaln, le_of_lt_succ h]
    | inr h => simp [h, n2c, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 1 =>
    simp [hsucc_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, evaln, le_of_lt_succ h]
    | inr h => simp [h, n2c, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 2 =>
    simp [hleft_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, evaln, le_of_lt_succ h]
    | inr h => simp [h, n2c, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 3 =>
    simp [hright_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, evaln, le_of_lt_succ h]
    | inr h => simp [h, n2c, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 4 =>
    simp [horacle_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, evaln, le_of_lt_succ h]
    | inr h => simp [h, n2c, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | n+5 => simp at hcode_val

theorem unpair_right_le' (n:ℕ) : n.r ≤ n := by unfold r; exact unpair_right_le n
-- lemma c_evaln_bounds_01 {n:ℕ} : n.div2.div2 ≤ n := by
--   simp only [Nat.div2_val]
--   apply (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
lemma c_evaln_bounds_0 : n.div2.div2 < n+5 := by
  simp only [Nat.div2_val]
  exact lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)) (Nat.succ_le_succ (Nat.le_add_right _ _))
lemma c_evaln_bounds_aux : Nat.pair (n + 4 + 1) (s+1) ≥ 1 := by exact pair_nonzero_right_pos
lemma c_evaln_bounds_left : Nat.pair n.div2.div2.l (s + 1) ≤ Nat.pair (n + 4 + 1) (s + 1) - 1 := by
  apply le_of_lt_succ
  simp [Nat.sub_add_cancel c_evaln_bounds_aux]
  apply pair_lt_pair_left _ (lt_of_le_of_lt (n.div2.div2).unpair_left_le c_evaln_bounds_0)
lemma c_evaln_bounds_right : Nat.pair n.div2.div2.r (s + 1) ≤ Nat.pair (n + 4 + 1) (s + 1) - 1 := by
  apply le_of_lt_succ
  simp [Nat.sub_add_cancel c_evaln_bounds_aux]
  apply pair_lt_pair_left _ (lt_of_le_of_lt (n.div2.div2).unpair_right_le c_evaln_bounds_0)
lemma c_evaln_bounds_3 : Nat.pair n.div2.div2 (s + 1) ≤ Nat.pair (n + 4 + 1) (s + 1) - 1 := by
  apply le_of_lt_succ
  simp [Nat.sub_add_cancel c_evaln_bounds_aux]
  apply pair_lt_pair_left
  apply lt_add_one_of_le
  simp [div2_val]
  exact c_replace_oracle_evp_aux_nMod4_bounds3
lemma c_evaln_bounds_4 : Nat.pair (n + 4 + 1) s ≤ Nat.pair (n + 4 + 1) (s + 1) - 1 := by
  apply le_of_lt_succ
  simp [Nat.sub_add_cancel c_evaln_bounds_aux]
  apply pair_lt_pair_right
  exact lt_add_one s

theorem c_evaln_evp_aux_nMod4 :
  eval_prim O (c_evaln) (Nat.pair x (Nat.pair ((n+4)+1) (s+1)))
    =
  let m := n.div2.div2
  let ml        := m.l
  let mr        := m.r

  let k:=(Nat.pair ((n+4)+1) (s+1))-1
  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k)))

  let pc_ml_s (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair ml (s+1)))
  let pc_mr_s (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair mr (s+1)))
  let pc_m_s  (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair m  (s+1)))
  let pc_c_sM1 (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair ((n+4)+1) s))

  let opt_pair (elem) := o2n (do guard (elem≤s); Nat.pair<$>n2o (pc_ml_s left elem)<*>n2o (pc_mr_s left elem))
  let opt_comp (elem) := o2n (do guard (elem≤s); let intermediate ← (n2o (pc_mr_s left elem)); n2o (pc_ml_s left intermediate))

  let opt_prec (elem) :=
  o2n (
    do
    guard (elem ≤ s)
    (Nat.rec
      (n2o (pc_ml_s left elem.l))
      (fun _ _ ↦
        do
          let i ← n2o (pc_c_sM1 (left) (Nat.pair elem.l (elem.r-1)))
          n2o (pc_mr_s (left) (Nat.pair elem.l (Nat.pair (elem.r-1) i)))
      )
    elem.r:Option ℕ)
    )

  let opt_rfind' (elem) :=
  o2n (do
    guard (elem ≤ s)
    (unpaired fun a m => do
      let x ← n2o $ pc_m_s left elem
      if x = 0 then pure m
      else n2o (pc_c_sM1 left (Nat.pair a (m + 1))))
      elem : Option ℕ
    )

       if n%4=0 then opt_pair x
  else if n%4=1 then opt_comp x
  else if n%4=2 then opt_prec x
  else if n%4=3 then opt_rfind' x
  else 0

    := by

  lift_lets
  extract_lets
  expose_names

  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names
  simp


  have kP1_gt_0 : Nat.pair ((n+4)+1) (s+1)>0 := pair_nonzero_right_pos
  have hkP1: k+1=(Nat.pair ((n+4)+1) (s+1)) := by
    exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]

  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k))) = covrec_inp := rfl
  simp [-comp₄_evp]
  have stupidrewrite :
  (eval_prim O
  (zero.c_list_singleton.c_cov_rec
  (c_if_eq_te.comp₄ s_1 (c_const 0) zero.c_list_singleton
  (c_if_eq_te.comp₄ code (c_const 0) zero_mapped
  (c_if_eq_te.comp₄ code (c_const 1) succ_mapped
  (c_if_eq_te.comp₄ code (c_const 2) left_mapped
  (c_if_eq_te.comp₄ code (c_const 3) right_mapped
  (c_if_eq_te.comp₄ code (c_const 4) oracle_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 0) pair_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 1) comp_mapped
  (c_if_eq_te.comp₄ nMod4 (c_const 2) prec_mapped rfind'_mapped))))))))))
  (Nat.pair 17 k))
  = (eval_prim O c_evaln_aux (Nat.pair 17 k)) := by exact rfl
  simp [stupidrewrite,covrec_inp_simp]

  have hcode_s : eval_prim O code_s covrec_inp = (Nat.pair ((n+4)+1) (s+1)) := by simp [code_s,covrec_inp,hkP1]
  have hs      : eval_prim O s_1 covrec_inp    = s+1     := by simp [s_1,hcode_s]
  have hsM1    : eval_prim O sM1 covrec_inp    = s       := by simp [sM1,hs]
  have hcode   : eval_prim O code covrec_inp   = (n+4)+1 := by simp [code,hcode_s]
  have hn      : eval_prim O n_1 covrec_inp    = n       := by simp [n_1,hcode]
  have hm      : eval_prim O m_1 covrec_inp    = m       := by simp [m_1,hn,m,div2_val]
  have hml     : eval_prim O ml_1 covrec_inp   = ml      := by simp [ml_1,hm,ml]
  have hmr     : eval_prim O mr_1 covrec_inp   = mr      := by simp [mr_1,hm,mr]
  have hnMod4  : eval_prim O nMod4 covrec_inp  = n%4     := by simp [nMod4,hn]

  have hlookup {x' c' s'} (elem:ℕ)
  (hcs'': Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (eval_prim O s' (Nat.pair elem covrec_inp)) ≤ k)
  :
  eval_prim O (lookup x' c' s') (Nat.pair elem covrec_inp)
    =
  let x'':=eval_prim O x' (Nat.pair elem covrec_inp)
  let c'':=eval_prim O c' (Nat.pair elem covrec_inp)
  let s'':=eval_prim O s' (Nat.pair elem covrec_inp)
  eval_prim O c_evaln (Nat.pair x'' (Nat.pair c'' s''))
    := by
    lift_lets
    extract_lets
    expose_names

    have aux1 : eval_prim O x' (Nat.pair elem covrec_inp) = x'' := by simp [x'']
    have aux2 : eval_prim O c' (Nat.pair elem covrec_inp) = c'' := by simp [c'']
    have aux3 : eval_prim O s' (Nat.pair elem covrec_inp) = s'' := by simp [s'']

    simp [lookup]
    simp [aux1,aux2,aux3] at *

    simp [comp_hist]
    simp [covrec_inp]
    unfold c_evaln
    unfold c_evaln_aux
    lift_lets
    simp [hcs'']

  have bounds_left {elem:ℕ} : Nat.pair (eval_prim O (ml_1.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (s_1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hml,hs]
    exact c_evaln_bounds_left
  have bounds_right {elem:ℕ} : Nat.pair (eval_prim O (mr_1.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (s_1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hmr,hs]
    exact c_evaln_bounds_right
  have bounds_m {elem:ℕ} : Nat.pair (eval_prim O (m_1.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (s_1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hm,hs]
    exact c_evaln_bounds_3
  have bounds_pc_c_sM1 {elem:ℕ} : Nat.pair (eval_prim O (code.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (sM1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hcode,hsM1]
    exact c_evaln_bounds_4

  have hpc_ml_s (c') (elem:ℕ): (eval_prim O (pc_ml_s_1 c') (Nat.pair elem covrec_inp)) = pc_ml_s c' elem := by
    simp [pc_ml_s_1]
    simp [hlookup elem bounds_left]
    unfold pc_ml_s
    simp [hs,hml,covrec_inp]
  have hpc_mr_s (c') (elem:ℕ): eval_prim O (pc_mr_s_1 c') (Nat.pair elem covrec_inp) = pc_mr_s c' elem := by
    simp [pc_mr_s_1]
    simp [hlookup elem bounds_right]
    unfold pc_mr_s
    simp [hs,hmr,covrec_inp]
  have hpc_m_s (c') (elem:ℕ): eval_prim O (pc_m_s_1 c') (Nat.pair elem covrec_inp) = pc_m_s c' elem := by
    simp [pc_m_s_1]
    simp [hlookup elem bounds_m]
    unfold pc_m_s
    simp [hs,hm,covrec_inp]
  have hpc_c_sM1 (c') (elem:ℕ): eval_prim O (pc_c_sM1_1 c') (Nat.pair elem covrec_inp) = pc_c_sM1 c' elem := by
    simp [pc_c_sM1_1]
    simp [hlookup elem bounds_pc_c_sM1]
    unfold pc_c_sM1
    simp [hsM1,hcode,covrec_inp]

  have hopt_pair :
    (fun ele => eval_prim O opt_pair_1 (Nat.pair ele covrec_inp))
      =
    opt_pair
    := by
      funext elem
      simp [opt_pair_1,hsM1]
      unfold ele
      simp [hpc_ml_s, hpc_mr_s]
      simp [opt_pair]
      cases Classical.em (elem≤s) with
      | inl h =>
        simp [h, Nat.not_lt_of_le h]
        cases Classical.em (pc_ml_s left elem=o2n Option.none) with
        | inl hh => simp [hh, hnat_to_opt_0, Seq.seq]
        | inr hh =>
          simp [not_none_imp_not_zero hh]
          cases Classical.em (pc_mr_s left elem=o2n Option.none) with
          | inl hhh => simp [hhh, hnat_to_opt_0, Seq.seq]
          | inr hhh =>
            simp [not_none_imp_not_zero hhh]
            simp [hnat_to_opt_2 hh, hnat_to_opt_2 hhh]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hpair_mapped:eval_prim O pair_mapped covrec_inp = (map (opt_pair) (range (s+1))) := by simp [pair_mapped, hs,hopt_pair]

  have hopt_comp :
    (fun ele => eval_prim O opt_comp_1 (Nat.pair ele covrec_inp))
      =
    opt_comp
    := by
      funext elem
      simp [opt_comp_1]
      simp [hsM1,hpc_mr_s,ele]
      simp [opt_comp]
      cases Classical.em (elem≤s) with
      | inl h =>
        simp [h, Nat.not_lt_of_le h]
        cases Classical.em (pc_mr_s left elem=o2n Option.none) with
        | inl hh => simp [hh, hnat_to_opt_0]
        | inr hh =>
          simp [hpc_ml_s]
          simp [hnat_to_opt_2 hh]
          simp [not_none_imp_not_zero hh]
          cases Classical.em (pc_ml_s (c_pred.comp (pc_mr_s_1 left)) elem=o2n Option.none) with
          | inl hhh =>
            simp [hhh]
            simp [pc_ml_s] at hhh
            simp [hpc_mr_s] at hhh
            simp [pc_ml_s]
            exact hhh.symm
          | inr hhh =>
            simp [not_none_imp_not_zero hhh]
            simp [pc_ml_s]
            simp [hpc_mr_s]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hcomp_mapped:eval_prim O comp_mapped covrec_inp = (map (opt_comp) (range (s+1))) := by simp [comp_mapped, hs,hopt_comp]
  have hprec_x (elem) : eval_prim O prec_x (Nat.pair elem covrec_inp) = elem.l := by simp [prec_x,ele]
  have hprec_i (elem) : eval_prim O prec_i (Nat.pair elem covrec_inp) = elem.r := by simp [prec_i,ele]
  have hprec_iM1 (elem) : eval_prim O prec_iM1 (Nat.pair elem covrec_inp) = elem.r-1 := by simp [prec_iM1,hprec_i]
  have hopt_prec :
    (fun ele => eval_prim O opt_prec_1 (Nat.pair ele covrec_inp))
      =
    opt_prec
    := by
      funext elem
      simp [opt_prec_1]
      simp [hsM1,ele]
      simp
      [
        prec_base_case,
        prec_inductive_case,
        prec_prev_case,
      ]
      simp [hpc_ml_s]
      simp [hpc_mr_s]

      simp [opt_prec]
      cases Classical.em (elem≤s) with
      | inl h =>
        simp [h, Nat.not_lt_of_le h]
        cases helemr:elem.r with
        | zero =>
          simp [pc_ml_s]
          simp [hprec_x,hprec_i,helemr]
        | succ nn =>
          simp [hprec_i,helemr]
          simp [hpc_c_sM1]

          simp [pc_c_sM1]

          have rw_elemr : nn = elem.r-1 := by simp [helemr]
          rw [rw_elemr]

          simp [hprec_x, hprec_iM1]


          cases Classical.em ((eval_prim O c_evaln (Nat.pair (Nat.pair elem.l (elem.r - 1)) (Nat.pair (n + 4 + 1) s))) = o2n Option.none) with
          | inl hh => simp [hh, hnat_to_opt_0]
          | inr hh =>
            simp [not_none_imp_not_zero hh]
            rw [hnat_to_opt_2 hh]
            simp [Option.bind]
            simp [pc_mr_s]
            simp [hprec_x, hprec_iM1]
            simp [hpc_c_sM1]
            simp [pc_c_sM1]
            simp [hprec_x, hprec_iM1]

      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hprec_mapped:eval_prim O prec_mapped covrec_inp = (map (opt_prec) (range (s+1))) := by simp [prec_mapped, hs,hopt_prec]

  have hopt_rfind' :
    (fun ele => eval_prim O opt_rfind'_1 (Nat.pair ele covrec_inp))
      =
    opt_rfind'
    := by
      funext elem
      simp [opt_rfind'_1]
      simp [hsM1,ele]


      simp
      [
        rfind'_base,
        rfind'_indt,
      ]
      simp [ele]
      simp [hpc_m_s]

      simp [opt_rfind']
      cases Classical.em (elem≤s) with
      | inl h =>
        simp [h, Nat.not_lt_of_le h]
        simp [pc_m_s]
        cases Classical.em (eval_prim O c_evaln (Nat.pair elem (Nat.pair m (s + 1)))=o2n Option.none) with
        | inl hh =>
          simp [hh,hnat_to_opt_0]
        | inr hh =>
          simp [not_none_imp_not_zero hh]
          simp [hnat_to_opt_2 hh]
          simp [hpc_c_sM1]
          simp [pc_c_sM1]

          cases Classical.em (eval_prim O c_evaln (Nat.pair elem (Nat.pair m (s + 1))) - 1 = 0) with
          | inl hhh => simp [hhh]
          | inr hhh => simp [hhh]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hrfind'_mapped:eval_prim O rfind'_mapped covrec_inp = (map (opt_rfind') (range (s+1))) := by simp [rfind'_mapped, hs,hopt_rfind']


  simp [hs,hcode,hnMod4]
  match h:n%4 with
  | 0 =>
    simp [hpair_mapped]
    unfold opt_pair
    intro hh
    simp [Nat.not_le_of_lt hh]
    simp [Option.bind]
  | 1 =>
    simp [hcomp_mapped]
    unfold opt_comp
    intro hh
    simp [Nat.not_le_of_lt hh]
    simp [Option.bind]
  | 2 =>
    simp [hprec_mapped]
    unfold opt_prec
    intro hh
    simp [Nat.not_le_of_lt hh]
    simp [Option.bind]
  | 3 =>
    simp [hrfind'_mapped]
    unfold opt_rfind'
    intro hh
    simp [Nat.not_le_of_lt hh]
    simp [Option.bind]
  | x+4 =>
    have contrad : n%4<4 := by
      apply Nat.mod_lt
      decide
    rw [h] at contrad
    rw [show x.succ.succ.succ.succ=x+4 from rfl] at contrad
    simp at contrad

@[simp] theorem c_evaln_evp: eval_prim O (c_evaln) (Nat.pair x (Nat.pair code s)) =
  o2n (evaln O s code x) := by

  let code_s:=Nat.pair code s
  rw [show Nat.pair code s = code_s by rfl]
  rw [show code = code_s.l by simp [code_s]]
  rw [show s = code_s.r by simp [code_s]]

  induction code_s using Nat.strong_induction_on generalizing x with
  | _ code_s ih =>

  let code:=code_s.l
  let s:=code_s.r
  rw [show code_s = (Nat.pair code s) from by simp [code,s]]
  simp only [pair_r, pair_l]

  match hs_val:s,hcode_val:code with
  | 0,    0    => exact c_evaln_evp_aux_x_0_0
  | 0,    n+1  => exact c_evaln_evp_aux_0_np1
  | sM1+1, 0   => apply c_evaln_evp_aux; decide
  | sM1+1, 1   => apply c_evaln_evp_aux; decide
  | sM1+1, 2   => apply c_evaln_evp_aux; decide
  | sM1+1, 3   => apply c_evaln_evp_aux; decide
  | sM1+1, 4   => apply c_evaln_evp_aux; decide
  | sM1+1, n+5 =>

  rw [show n.succ.succ.succ.succ.succ=n+5 by rfl] at hcode_val
  rw [succ_eq_add_one] at hs_val


  let m := n.div2.div2
  have hm : m < n + 5 := c_evaln_bounds_0
  have _m1 : m.l < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
  have _m2 : m.r < n + 5 := lt_of_le_of_lt m.unpair_right_le hm

  have hcode_s : code_s=Nat.pair (n+5) (sM1+1) := by
    rw [←hs_val]
    rw [←hcode_val]
    simp only [code,s]
    simp only [pair_lr]
  let ml_s     := Nat.pair m.l (sM1+1)
  let mr_s     := Nat.pair m.r (sM1+1)
  let m_s      := Nat.pair m (sM1+1)
  let c_sM1    := Nat.pair (n+4+1) sM1
  have ml_s_lt_cs  : ml_s  < code_s := by unfold ml_s;  rw [hcode_s]; exact pair_lt_pair_left  (sM1+1) _m1
  have mr_s_lt_cs  : mr_s  < code_s := by unfold mr_s;  rw [hcode_s]; exact pair_lt_pair_left  (sM1+1) _m2
  have m_s_lt_cs   : m_s   < code_s := by unfold m_s;   rw [hcode_s]; exact pair_lt_pair_left  (sM1+1) hm
  have c_sM1_lt_cs : c_sM1 < code_s := by unfold c_sM1; rw [hcode_s]; exact pair_lt_pair_right (n+4+1) (lt_add_one sM1)

  rw [show n+5=(n+4)+1 from rfl]


  cases hno:n.bodd with
  | false => cases hn2o:n.div2.bodd with

    -- pair
    | false =>
      have h0: n%4=0 := nMod4_eq_0 hno hn2o
      -- simplify the rhs
      simp [n2c]
      simp [evaln,hno, hn2o]

      rw [c_evaln_evp_aux_nMod4]
      simp [h0]

      rw [ih mr_s mr_s_lt_cs];
      rw [ih ml_s ml_s_lt_cs];
      simp [ml_s, mr_s, m]

    -- prec
    | true =>
      have h0: n%4=2 := nMod4_eq_2 hno hn2o

      -- simplify the rhs
      simp [n2c]
      simp only [hno, hn2o, evaln]

      rw [c_evaln_evp_aux_nMod4]
      simp [h0]

      rw [ih ml_s ml_s_lt_cs]
      rw [ih c_sM1 c_sM1_lt_cs]
      have ih_i {i} : (eval_prim O c_evaln (Nat.pair (Nat.pair x.l (Nat.pair (x.r - 1) i)) (Nat.pair n.div2.div2.r (sM1 + 1)))) = (o2n (evaln O mr_s.r (n2c mr_s.l) (Nat.pair x.l (Nat.pair (x.r - 1) i)))) := by
        rw [ih mr_s mr_s_lt_cs];
      simp [ih_i]

      cases Classical.em (x≤sM1) with
      | inr h => simp [h,Option.bind]
      | inl h =>
        simp [h, ml_s, mr_s, c_sM1, m]
        cases x.r with
        | zero => rfl
        | succ xxx =>
          simp
          have rw3_aux : c2n (((n2c n.div2.div2.l).prec (n2c n.div2.div2.r))) = (n + 4 + 1) := by
            simp [c2n]
            apply codes_aux_2 hno hn2o

          have rw3 : ((n2c n.div2.div2.l).prec (n2c n.div2.div2.r)) = (n2c (n + 4 + 1)) := by
            rw [←(n2c_c2n (n2c (n + 4 + 1)))]
            rw [←(n2c_c2n (((n2c n.div2.div2.l).prec (n2c n.div2.div2.r))))]
            simp [rw3_aux]
          rw [rw3]


  | true => cases hn2o:n.div2.bodd with
    -- comp
    | false =>
      have h0: n%4=1 := nMod4_eq_1 hno hn2o

      -- simplify the rhs
      -- simp
      simp [n2c]
      simp [evaln,hno, hn2o]

      rw [c_evaln_evp_aux_nMod4]
      simp [h0]

      rw [ih mr_s mr_s_lt_cs];
      simp [mr_s, m]

      cases Classical.em (x≤sM1) with
      | inl h =>
        simp [h]
        cases Classical.em (evaln O (sM1 + 1) (n2c n.div2.div2.r) x=Option.none) with
        | inl hh => simp [hh]
        | inr hh =>
          have optval := Option.eq_none_or_eq_some (evaln O (sM1 + 1) (n2c n.div2.div2.r) x)
          simp [hh] at optval
          rcases optval with ⟨inter, hinter⟩
          simp [hinter]
          rw [ih ml_s ml_s_lt_cs];
          simp [ml_s, m]

      | inr h =>
        simp [h,Option.bind]

    -- rfind
    | true =>
      have h0: n%4=3 := nMod4_eq_3 hno hn2o
      simp [n2c]
      simp [evaln,hno, hn2o]

      rw [c_evaln_evp_aux_nMod4]
      simp [h0]

      rw [ih m_s m_s_lt_cs];
      rw [ih c_sM1 c_sM1_lt_cs]

      cases Classical.em (x≤sM1) with
      | inl h =>
        simp [h]
        simp [m_s]
        simp [m]
        simp [c_sM1]

        have rw0_aux : c2n ((n2c n.div2.div2).rfind') = n + 4 + 1 := by
          simp [c2n]
          exact codes_aux_3 hno hn2o
        have rw0 : (n2c (n + 4 + 1)) = (n2c n.div2.div2).rfind' := by
          rw [←(n2c_c2n (n2c (n + 4 + 1)))]
          rw [←n2c_c2n ((n2c n.div2.div2).rfind')]
          simp [rw0_aux]
        rw [rw0]

      | inr h => simp [h,Option.bind]

@[cp] theorem c_evaln_aux_ev_pr : code_prim (c_evaln_aux) := by
  unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names

  have cp_code_s : code_prim code_s := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_code : code_prim code := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_s : code_prim s := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_sM1 : code_prim sM1 := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_comp_hist : code_prim comp_hist := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_n : code_prim n := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_m : code_prim m := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_ml : code_prim ml := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_mr : code_prim mr := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_nMod4 : code_prim nMod4 := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_ele : code_prim ele := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_zero : code_prim opt_zero := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_succ : code_prim opt_succ := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_left : code_prim opt_left := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_right : code_prim opt_right := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_oracle : code_prim opt_oracle := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_zero_mapped : code_prim zero_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_succ_mapped : code_prim succ_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_left_mapped : code_prim left_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_right_mapped : code_prim right_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_oracle_mapped : code_prim oracle_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_lookup {x' c' s'} (hx':code_prim x') (hc':code_prim c') (hs':code_prim s') : code_prim (lookup x' c' s') := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_pc_ml_s {c'} (hc':code_prim c') : code_prim (pc_ml_s c') := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_pc_mr_s {c'} (hc':code_prim c') : code_prim (pc_mr_s c') := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_pc_m_s  {c'} (hc':code_prim c') : code_prim (pc_m_s c') := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_pair : code_prim opt_pair := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_pair_mapped : code_prim pair_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_comp : code_prim opt_comp := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_comp_mapped : code_prim comp_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_pc_c_sM1 {c'} (hc':code_prim c') : code_prim (pc_c_sM1 c') := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_prec_x : code_prim prec_x := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_prec_i : code_prim prec_i := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_prec_iM1 : code_prim prec_iM1 := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_prec_base_case : code_prim prec_base_case := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_prec_prev_case : code_prim prec_prev_case := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_prec_inductive_case : code_prim prec_inductive_case := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_prec : code_prim opt_prec := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_prec_mapped : code_prim prec_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_rfind'_base : code_prim rfind'_base := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_rfind'_indt : code_prim rfind'_indt := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_opt_rfind' : code_prim opt_rfind' := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  have cp_rfind'_mapped : code_prim rfind'_mapped := by apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

  apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

@[cp] theorem c_evaln_ev_pr : code_prim (c_evaln) := by
  unfold c_evaln
  apply_rules (config := {maxDepth:=30, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

@[simp] theorem c_evaln_ev: eval O c_evaln (Nat.pair x (Nat.pair code s)) = o2n (evaln O s code x) := by
  rw [← eval_prim_eq_eval c_evaln_ev_pr];
  simp only [PFun.coe_val, c_evaln_evp, Part.coe_some]

@[simp] theorem c_evaln_evp': eval_prim O (c_evaln) = fun x => o2n $ evaln O x.r.r x.r.l x.l := by
  funext x
  have : x = (Nat.pair x.l (Nat.pair x.r.l x.r.r)) := by simp
  rw (config:={occs:=.pos [1]}) [this]
  exact c_evaln_evp
-- theorem Nat.PrimrecIn.evaln:Nat.PrimrecIn O (fun x => o2n $ evaln O x.r.r x.r.l x.l) := by

--   rw [← c_evaln_evp]; apply code_prim_prop c_evaln_ev_pr
end Computability.Code
-- theorem Nat.Primrec.evaln:Nat.Primrec (unpaired evaln) := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.evaln
end evaln

section eval
namespace Computability.Code
def c_eval := (c_rfindOpt (c_evaln.comp₃ (right.comp left) (left.comp left) right))
@[simp] theorem c_eval_ev: eval O c_eval (Nat.pair c x) = eval O c x := by
  simp only [c_eval, comp₃, comp₂]
  have : code_total O ((c_evaln.comp ((right.comp left).pair ((left.comp left).pair right)))) := by
    apply prim_total
    apply_rules (config := {maxDepth:=30, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
  simp [c_rfindOpt_ev this]
  rw [eval_eq_rfindOpt]
  simp [eval,Seq.seq]
theorem Computability.eval:Nat.RecursiveIn O (fun ex => eval O ex.l ex.r) := by
  apply exists_code.mpr
  use c_eval
  funext x
  rw (config:={occs:=.pos [1]}) [←(@pair_lr x)]
  exact c_eval_ev

end Computability.Code
-- theorem Nat.Primrec.eval:Nat.Primrec Nat.eval := by ...
end eval
