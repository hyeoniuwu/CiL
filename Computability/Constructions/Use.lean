import Computability.Constructions.Eval
import Computability.Use
-- import Computability.Constructions.Eval_Aux

open List

-- set_option profiler true

section usen
namespace Nat.RecursiveIn.Code

/--
`eval c_usen_aux (_, (c,s)) .last = [ [c]ₛ(0), [c]ₛ(1), ..., [c]ₛ(s) ]`
`eval c_usen_aux (_, (c,s)).last` is the list of computations of code c for s steps on all inputs x=0 to s.
-/
def c_usen_aux :=
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
  let opt_zero   := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (zero.comp   ele)
  -- let opt_zero   := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (zero.comp   ele)
  -- let opt_zero   := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (zero.comp   ele)
  -- let opt_zero  := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (zero.comp   ele)
  let opt_oracle := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) $ succ.comp (succ.comp   ele)

  let zero_mapped := ((c_list_map' opt_zero).comp₂ (c_list_range.comp s) c_id)
  -- let zero_mapped := ((c_list_map' opt_zero).comp₂ (c_list_range.comp s) c_id)
  -- let zero_mapped := ((c_list_map' opt_zero).comp₂ (c_list_range.comp s) c_id)
  -- let zero_mapped := ((c_list_map' opt_zero).comp₂ (c_list_range.comp s) c_id)
  let oracle_mapped := ((c_list_map' opt_oracle).comp₂ (c_list_range.comp s) c_id)

  -- `=[c]ₛ(x)`
  let lookup (x' c' s') := c_list_getI.comp₂ (c_list_getI.comp₂ (comp_hist.comp right) (pair c' s')) x'

  let pc_ml_s (c') := lookup (c') (ml.comp right) (s.comp right)         -- `[ml]ₛ(x)`
  let pc_mr_s (c') := lookup (c') (mr.comp right) (s.comp right)         -- `[mr]ₛ(x)`
  let pc_m_s  (c') := lookup (c') (m.comp  right) (s.comp right)         -- `[mr]ₛ(x)`
  let pc_c_sM1 (c') := lookup (c') (code.comp right) (sM1.comp right) -- `[code]_{s-1}(x)`

  -- pair
  let opt_pair := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ (pc_ml_s ele) (c_opt_none) $
    c_ifz.comp₃ (pc_mr_s ele) (c_opt_none) $
    succ.comp (c_max.comp₂ (c_opt_iget.comp (pc_ml_s ele)) (c_opt_iget.comp (pc_mr_s ele)))
  let pair_mapped := ((c_list_map' opt_pair).comp₂ (c_list_range.comp s) c_id)

  -- comp: `[ml]ₛ ( [mr]ₛ(x) ) `
  let comp_usen_cg := pc_mr_s ele
  let comp_evaln_cg := c_evaln.comp₃ ele (mr.comp right) (s.comp right)
  let comp_usen_cf := pc_ml_s $ c_pred.comp (comp_evaln_cg)
  let opt_comp := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ comp_usen_cg  c_opt_none $
    c_ifz.comp₃ comp_evaln_cg c_opt_none $
    c_ifz.comp₃ comp_usen_cf  c_opt_none $
    c_max.comp₂ comp_usen_cf comp_usen_cg
  let comp_mapped := ((c_list_map' opt_comp).comp₂ (c_list_range.comp s) c_id)

  -- prec: if `x.r=n+1`, then `[mr](x.l, (x.r-1, [code](x.l, x.r-1)))` else `[ml](x.l,0)`

  let prec_x   := left.comp ele
  let prec_i   := right.comp ele
  let prec_iM1 := c_pred.comp prec_i

  -- let prec_base_case      := pc_ml_s prec_x
  -- let prec_prev_case      := pc_c_sM1 (pair prec_x (prec_iM1))
  -- let prec_inductive_case := pc_mr_s (pair prec_x (pair prec_iM1 (c_pred.comp prec_prev_case)))
  let prec_usen_base  := pc_ml_s prec_x
  let prec_usen_prev  := pc_c_sM1 (pair prec_x (prec_iM1))
  let prec_evaln_prev := c_evaln.comp₃ (pair prec_x (prec_iM1)) (code.comp right) (sM1.comp right)
  let prec_usen_indt  := pc_mr_s (pair prec_x (pair prec_iM1 (c_pred.comp prec_evaln_prev)))
  -- let prec_usen_indt  := pc_mr_s (pair (prec_x.comp left) (pair (prec_iM1.comp left) (c_pred.comp right)))

  let opt_prec := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ prec_i          prec_usen_base $
    c_ifz.comp₃ prec_usen_prev  c_opt_none $
    c_ifz.comp₃ prec_evaln_prev c_opt_none $
    c_ifz.comp₃ prec_usen_indt  c_opt_none $
    succ.comp $ c_max.comp₂ (c_opt_iget.comp prec_usen_prev) (c_opt_iget.comp prec_usen_indt)
  -- let opt_prec := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
  --   c_ifz.comp₃ prec_i          prec_usen_base $
  --   c_opt_bind' prec_usen_prev  $
  --   c_opt_bind'  prec_evaln_prev $
  --   c_opt_bind'  prec_usen_indt  $
  --   succ.comp $ c_max.comp₂ (c_opt_iget.comp prec_usen_prev) (c_opt_iget.comp prec_usen_indt)
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
  c_if_eq_te.comp₄ code  (c_const 1) zero_mapped   $
  c_if_eq_te.comp₄ code  (c_const 2) zero_mapped   $
  c_if_eq_te.comp₄ code  (c_const 3) zero_mapped  $
  c_if_eq_te.comp₄ code  (c_const 4) oracle_mapped $

  c_if_eq_te.comp₄ nMod4 (c_const 0) pair_mapped   $
  c_if_eq_te.comp₄ nMod4 (c_const 1) comp_mapped   $
  c_if_eq_te.comp₄ nMod4 (c_const 2) prec_mapped   $
                                     rfind'_mapped

/-- api: `Nat.pair x (Nat.pair code s)` -/
def c_usen :=
  -- let code_s := right
  -- let x := left
  c_list_getI.comp₂ (c_list_getLastI.comp $ c_usen_aux.comp (pair (c_const 17) right)) left

-- set_option maxHeartbeats 3 in
-- set_option maxRecDepth 600 in
-- @[simp] theorem c_usen_ev_pr:code_prim (c_usen) := by
--   unfold c_usen;
--   -- repeat (first|assumption|simp|constructor)
--   first|assumption|simp|constructor
-- #exit
theorem c_usen_evp_aux_x_0_0 : eval_prim O (c_usen) (Nat.pair x (Nat.pair 0 0)) = o2n (usen O 0 0 x) := by
  unfold c_usen; unfold c_usen_aux
  lift_lets
  extract_lets
  expose_names
  rw [show Nat.pair 0 0 = 0 from rfl]
  simp [getI, usen] -- doing this simp after cases blows up memory. why?
  cases x with
  | zero => simp
  | succ n => simp

theorem c_usen_evp_aux_0_np1 : eval_prim O (c_usen) (Nat.pair x (Nat.pair (n+1) 0)) = o2n (usen O (n+1:ℕ) 0 x) := by
  unfold c_usen; unfold c_usen_aux
  lift_lets
  extract_lets
  expose_names

  let k:=((Nat.pair (n+1) 0))-1
  have kP1_gt_0 : (Nat.pair (n+1) 0)>0 := by
    apply pair_l_gt0
    exact zero_lt_succ n
  have hkP1: k+1=((Nat.pair (n+1) 0)) := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]

  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_usen_aux (Nat.pair 17 k)))
  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_usen_aux (Nat.pair 17 k))) = covrec_inp := rfl

  have stupidrewrite :
  (eval_prim O
  (zero.c_list_singleton.c_cov_rec
  (c_if_eq_te.comp ((s.pair (c_const 0)).pair (zero.c_list_singleton.pair
  (c_if_eq_te.comp ((code.pair (c_const 0)).pair (zero_mapped.pair
  (c_if_eq_te.comp ((code.pair (c_const 1)).pair (zero_mapped.pair
  (c_if_eq_te.comp ((code.pair (c_const 2)).pair (zero_mapped.pair
  (c_if_eq_te.comp ((code.pair (c_const 3)).pair (zero_mapped.pair
  (c_if_eq_te.comp ((code.pair (c_const 4)).pair (oracle_mapped.pair
  (c_if_eq_te.comp ((nMod4.pair (c_const 0)).pair (pair_mapped.pair
  (c_if_eq_te.comp ((nMod4.pair (c_const 1)).pair (comp_mapped.pair
  (c_if_eq_te.comp ((nMod4.pair (c_const 2)).pair (prec_mapped.pair
  rfind'_mapped)))))))))))))))))))))))))))) (Nat.pair 17 k))
  = (eval_prim O c_usen_aux (Nat.pair 17 k)) := rfl
  simp [stupidrewrite,covrec_inp_simp]

  have hs : eval_prim O s covrec_inp = 0 := by simp [s,code_s,covrec_inp,hkP1]
  simp [hs, getI, usen]
  cases x <;> simp

theorem c_usen_evp_aux (hcode_val:code≤4) :
  eval_prim O (c_usen) (Nat.pair x (Nat.pair code (s+1)))
    =
  o2n (usen O (code:ℕ) (s+1) x)
  := by

  unfold c_usen; unfold c_usen_aux
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

  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_usen_aux (Nat.pair 17 k)))
  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_usen_aux (Nat.pair 17 k))) = covrec_inp := rfl

  have stupidrewrite :
  (eval_prim O
  (zero.c_list_singleton.c_cov_rec (c_if_eq_te.comp ((s_1.pair (c_const 0)).pair
  (zero.c_list_singleton.pair (c_if_eq_te.comp ((code_1.pair (c_const 0)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code_1.pair (c_const 1)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code_1.pair (c_const 2)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code_1.pair (c_const 3)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code_1.pair (c_const 4)).pair
  (oracle_mapped.pair (c_if_eq_te.comp ((nMod4.pair (c_const 0)).pair
  (pair_mapped.pair (c_if_eq_te.comp ((nMod4.pair (c_const 1)).pair
  (comp_mapped.pair (c_if_eq_te.comp ((nMod4.pair (c_const 2)).pair
  (prec_mapped.pair rfind'_mapped))))))))))))))))))))))))))))
  (Nat.pair 17 k))
  = (eval_prim O c_usen_aux (Nat.pair 17 k)) := by exact rfl
  simp [stupidrewrite,covrec_inp_simp]

  have hcode_s : eval_prim O code_s covrec_inp = (Nat.pair code (s + 1)) := by simp [code_s,covrec_inp,hkP1]
  have hs      : eval_prim O s_1 covrec_inp = s+1 := by simp [s_1,hcode_s]
  have hsM1    : eval_prim O sM1 covrec_inp = s := by simp [sM1,hs]
  have hcode   : eval_prim O code_1 covrec_inp = code := by simp [code_1,hcode_s]
  have hopt_zero :
    (fun ele => eval_prim O opt_zero (Nat.pair ele covrec_inp))
      =
    (o2n ∘ usen O zero (s+1)) := by
      funext elem
      simp [opt_zero]
      simp [hsM1,ele]
      simp [usen]
      cases Classical.em (elem≤s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hopt_oracle :
    (fun ele => eval_prim O opt_oracle (Nat.pair ele covrec_inp))
      =
    (o2n ∘ usen O oracle (s+1)) := by
      funext elem
      simp [opt_oracle]
      simp [hsM1,ele]
      simp [usen]
      cases Classical.em (elem≤s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hzero_mapped:eval_prim O zero_mapped covrec_inp = (map (o2n ∘ usen O zero (s+1)) (range (s+1))) := by simp [zero_mapped, hs,hopt_zero]
  have horacle_mapped:eval_prim O oracle_mapped covrec_inp = (map (o2n ∘ usen O oracle (s+1)) (range (s+1))) := by simp [oracle_mapped, hs,hopt_oracle]

  simp [hs,hcode]

  match code with
  | 0 =>
    simp [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, usen, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, usen, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 1 =>
    simp [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, usen, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, usen, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 2 =>
    simp [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, usen, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, usen, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 3 =>
    simp [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, usen, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, usen, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 4 =>
    simp [horacle_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, usen, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, usen, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | n+5 => simp at hcode_val


theorem c_usen_evp_aux_nMod4 :
  eval_prim O (c_usen) (Nat.pair x (Nat.pair ((n+4)+1) (s+1)))
    =
  let m := n.div2.div2
  let ml        := m.l
  let mr        := m.r

  let k:=(Nat.pair ((n+4)+1) (s+1))-1
  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_usen_aux (Nat.pair 17 k)))

  let pc_ml_s  c' elem := eval_prim O (c_usen) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair ml (s+1)))
  let pc_mr_s  c' elem := eval_prim O (c_usen) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair mr (s+1)))
  let pc_m_s   c' elem := eval_prim O (c_usen) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair m  (s+1)))
  let pc_c_sM1 c' elem := eval_prim O (c_usen) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair ((n+4)+1) s))

  -- let opt_pair (elem) := Encodable.encode (do guard (elem≤s); Nat.max<$>n2o (pc_ml_s left elem)<*>n2o (pc_mr_s left elem))
  let opt_pair elem := o2n do
    guard (elem≤s)
    let usen_cf ← n2o (pc_ml_s left elem)
    let usen_cg ← n2o (pc_mr_s left elem)
    return Nat.max usen_cf usen_cg

  let opt_comp elem := o2n do
    guard (elem≤s);
    let usen_cg ← n2o (pc_mr_s left elem)
    let evaln_cg ← evaln O (s+1) mr elem
    let usen_cf  ← n2o (pc_ml_s left evaln_cg)
    Nat.max usen_cf usen_cg

  let opt_prec x := o2n do
    guard (x≤s)
    let (xl, i) := Nat.unpair x
    (i.casesOn
    (n2o (pc_ml_s left xl))
    fun iM1 =>
    do
      -- let usen_prev  ← usen  O (prec cf cg) s (Nat.pair xl iM1)
      let usen_prev  ← n2o $ pc_c_sM1 left (Nat.pair xl iM1)
      -- let evaln_prev ← evaln O s (prec cf cg) (Nat.pair xl iM1)
      let evaln_prev ← evaln O s (decodeCode (n+4+1)) (Nat.pair xl iM1)
      -- let usen_indt  ← usen  O cg (s+1) (Nat.pair xl (Nat.pair iM1 evaln_prev))
      let usen_indt  ← n2o $ pc_mr_s left (Nat.pair xl (Nat.pair iM1 evaln_prev))
      return Nat.max usen_prev usen_indt)

  --   do
  -- guard (x≤s);
  -- let (xl, i) := Nat.unpair x
  -- (i.casesOn
  -- (usen O cf (s+1) xl)
  -- fun iM1 =>
  -- do
  --   let usen_prev  ← usen  O (prec cf cg) s (Nat.pair xl iM1)
  --   let evaln_prev ← evaln O s (prec cf cg) (Nat.pair xl iM1)
  --   let usen_indt  ← usen  O cg (s+1) (Nat.pair xl (Nat.pair iM1 evaln_prev))
  --   return Nat.max usen_prev usen_indt)

  -- Encodable.encode (
  --   do
  --   guard (elem ≤ s)
  --   (Nat.rec
  --     (n2o (pc_ml_s left elem.l))
  --     (fun n_2 n_ih ↦
  --       do
  --         let i ← n2o (pc_c_sM1 (left) (Nat.pair elem.l (elem.r-1)))
  --         n2o (pc_mr_s (left) (Nat.pair elem.l (Nat.pair (elem.r-1) i)))
  --     )
  --   elem.r:Option ℕ)
  --   )

  let opt_rfind' elem :=
  Encodable.encode (do
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

  unfold c_usen; unfold c_usen_aux
  lift_lets
  extract_lets
  expose_names
  simp


  have kP1_gt_0 : Nat.pair ((n+4)+1) (s+1)>0 := pair_nonzero_right_pos
  have hkP1: k+1=(Nat.pair ((n+4)+1) (s+1)) := by
    exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]

  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_usen_aux (Nat.pair 17 k))) = covrec_inp := rfl

  have stupidrewrite :
  (eval_prim O
  (zero.c_list_singleton.c_cov_rec (c_if_eq_te.comp ((s_1.pair (c_const 0)).pair
  (zero.c_list_singleton.pair (c_if_eq_te.comp ((code.pair (c_const 0)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code.pair (c_const 1)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code.pair (c_const 2)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code.pair (c_const 3)).pair
  (zero_mapped.pair (c_if_eq_te.comp ((code.pair (c_const 4)).pair
  (oracle_mapped.pair (c_if_eq_te.comp ((nMod4.pair (c_const 0)).pair
  (pair_mapped.pair (c_if_eq_te.comp ((nMod4.pair (c_const 1)).pair
  (comp_mapped.pair (c_if_eq_te.comp ((nMod4.pair (c_const 2)).pair
  (prec_mapped.pair rfind'_mapped)))))))))))))))))))))))))))) (Nat.pair 17 k))
  = (eval_prim O c_usen_aux (Nat.pair 17 k)) := by exact rfl
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
  eval_prim O c_usen (Nat.pair x'' (Nat.pair c'' s''))
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
    unfold c_usen
    unfold c_usen_aux
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

  have hcomp_usen_cg elem : eval_prim O comp_usen_cg (Nat.pair elem covrec_inp) = pc_mr_s left elem := by
    simp [comp_usen_cg]
    simp [hpc_mr_s]
    simp [ele]
  have hcomp_evaln_cg elem : eval_prim O comp_evaln_cg (Nat.pair elem covrec_inp) = o2n (evaln O (s+1) (decodeCode mr) elem) := by
    simp [comp_evaln_cg]
    simp [hs,hmr,ele]
  have hcomp_usen_cf elem : eval_prim O comp_usen_cf (Nat.pair elem covrec_inp) = pc_ml_s (c_pred.comp comp_evaln_cg) elem := by
    simp [comp_usen_cf]
    simp [hpc_ml_s]

  have hopt_comp :
    (fun ele => eval_prim O opt_comp_1 (Nat.pair ele covrec_inp))
      =
    opt_comp
    := by
      funext elem
      simp [opt_comp_1]
      simp [hsM1,hpc_mr_s,ele]
      -- unfold opt_comp
      simp [opt_comp]
      cases Classical.em (elem≤s) with
      | inr h => simp [h, gt_of_not_le h, Option.bind]
      | inl h =>
        simp [h, Nat.not_lt_of_le h]
        simp [hcomp_usen_cg]
        cases Classical.em (pc_mr_s left elem=o2n Option.none) with
        | inl hh => simp [hh, hnat_to_opt_0]
        | inr hh =>
          -- simp [hpc_ml_s]
          simp [hnat_to_opt_2 hh]
          -- simp [hpc_mlmr_s_lookup]
          simp [not_none_imp_not_zero hh]
          simp [hcomp_evaln_cg]
          -- rw [hnat_to_opt_1 hh]
          -- simp [Option.bind]
          cases Classical.em ((evaln O (s + 1) (decodeCode mr) elem)=Option.none) with
          | inl hhh => simp [hhh, hnat_to_opt_0]
          | inr hhh =>
          simp [hnat_1 hhh]
          simp [isSome.bind (Option.isSome_iff_ne_none.mpr hhh)]
          simp [hcomp_usen_cf]
          have :  pc_ml_s (c_pred.comp comp_evaln_cg) elem = (pc_ml_s left ((evaln O (s + 1) (decodeCode mr) elem).get (Option.isSome_iff_ne_none.mpr hhh))) := by
            unfold pc_ml_s
            simp
            simp [hcomp_evaln_cg]
            simp [hnat_2 (Option.isSome_iff_ne_none.mpr hhh)]
          rw [this]

          cases Classical.em (pc_ml_s left ((evaln O (s + 1) (decodeCode mr) elem).get (Option.isSome_iff_ne_none.mpr hhh)) = 0) with
          | inl hhhh =>
            simp [hhhh];
            simp [hnat_3]
          | inr hhhh =>
            simp [not_none_imp_not_zero hhhh]
            simp [hnat_to_opt_2 hhhh]
            simp [hnat_5 hhhh]
            -- simp [pc_ml_s]
            -- simp [hpc_mr_s]
  have hcomp_mapped:eval_prim O comp_mapped covrec_inp = (map (opt_comp) (range (s+1))) := by simp [comp_mapped, hs,hopt_comp]

  have hprec_x elem : eval_prim O prec_x (Nat.pair elem covrec_inp) = elem.l := by simp [prec_x,ele]
  have hprec_i elem : eval_prim O prec_i (Nat.pair elem covrec_inp) = elem.r := by simp [prec_i,ele]
  have hprec_iM1 elem : eval_prim O prec_iM1 (Nat.pair elem covrec_inp) = elem.r-1 := by simp [prec_iM1,hprec_i]
  have hprec_usen_base elem : eval_prim O prec_usen_base (Nat.pair elem covrec_inp) = ((pc_ml_s left elem.l)) := by
    simp [prec_usen_base, hpc_ml_s];
    simp [pc_ml_s, hprec_x]
  have hprec_usen_prev elem : (eval_prim O prec_usen_prev (Nat.pair elem covrec_inp)) = (pc_c_sM1 left (Nat.pair elem.l (elem.r-1))) := by
    simp [prec_usen_prev]
    simp [hpc_c_sM1]
    simp [pc_c_sM1]
    simp [hprec_x]
    simp [hprec_iM1]
  have hprec_evaln_prev elem: (eval_prim O prec_evaln_prev (Nat.pair elem covrec_inp)) = o2n (evaln O s (decodeCode (n+4+1)) (Nat.pair elem.l (elem.r - 1))) := by
    simp [prec_evaln_prev]
    simp [hsM1]
    simp [hcode]
    simp [hprec_x,hprec_iM1]
  have hprec_usen_indt elem asd: (eval_prim O prec_usen_indt (Nat.pair elem covrec_inp)) = ((pc_mr_s left
          (Nat.pair elem.l
            (Nat.pair (elem.r - 1) ((evaln O s (decodeCode (n + 4 + 1)) (Nat.pair elem.l (elem.r - 1))).get (asd)))))) := by
    simp [prec_usen_indt]
    simp [hpc_mr_s]
    simp [pc_mr_s]
    simp [hprec_x, hprec_iM1]
    simp [hprec_evaln_prev]
    apply congrArg
    apply congrFun
    apply congrArg
    apply congrArg
    apply congrArg
    exact hnat_9.symm
  have hopt_prec :
    (fun ele => eval_prim O opt_prec_1 (Nat.pair ele covrec_inp))
      =
    opt_prec
    := by
      funext elem
      simp [opt_prec_1]
      simp [hsM1,ele]
      simp [hprec_i]
      simp [hprec_usen_base]

      simp [opt_prec]


      -- simp
      -- [
      --   prec_base_case,
      --   prec_inductive_case,
      --   prec_prev_case,
      -- ]
      -- simp [hpc_ml_s]
      -- simp [hpc_mr_s]

      -- simp [opt_prec]
      cases Classical.em (elem≤s) with
      | inr h => simp [h, gt_of_not_le h, Option.bind]
      | inl h =>
        simp [h, Nat.not_lt_of_le h]
        simp [pc_ml_s]
        cases helemr:elem.r with
        | zero =>
          simp [pc_ml_s]
          -- simp [hprec_x,hprec_i,helemr]
        | succ elemrM1 =>
          have rm1rw : elemrM1 = elem.r -1 := Nat.eq_sub_of_add_eq (_root_.id (Eq.symm helemr))
          rw [rm1rw]

          -- simp [prec_i,ele,helemr]

          simp [hprec_usen_prev]
          simp [hprec_evaln_prev]
          -- apply congrArg
          -- funext a_0
          cases Classical.em ((evaln O s (decodeCode (n + 4 + 1)) (Nat.pair elem.l (elem.r - 1)))=Option.none) with
          | inl hh => simp [hh]
          | inr hh =>
            simp [hnat_1 hh]
            simp [isSome.bind $ isSome_iff_not_none.mp hh]
            simp [hprec_usen_indt elem (isSome_iff_not_none.mp hh )]
            cases Classical.em (
      (pc_mr_s left
        (Nat.pair elem.l
          (Nat.pair (elem.r - 1) ((evaln O s (decodeCode (n + 4 + 1)) (Nat.pair elem.l (elem.r - 1))).get (isSome_iff_not_none.mp hh ))))) = o2n Option.none ) with
            | inl hhh => simp [hhh, hnat_3]
            | inr hhh =>
              simp [not_none_imp_not_zero hhh]
              simp [hnat_to_opt_2 hhh]
              -- simp [isSome.bind $ isSome_iff_not_none.mp hhh]
              -- simp [hhh]
              cases Classical.em (pc_c_sM1 left (Nat.pair elem.l (elem.r - 1)) = o2n Option.none )  with
              | inl hhhh => simp [hhhh, hnat_3]
              | inr hhhh =>
                simp [not_none_imp_not_zero hhhh]
                simp [hnat_to_opt_2 hhhh]
                -- simp [isSome.bind $ isSome_iff_not_none.mp hhhh]
                -- simp [iget_eq_get $ isSome_iff_not_none.mp hhh]
                -- simp [iget_eq_get $ isSome_iff_not_none.mp hhhh]

                -- have := not_none_imp_not_zero hhhh
                sorry
                -- rfl
            -- simp [prec_usen_indt]
            -- simp [hpc_mr_s]
            sorry
          -- apply congrArg
          -- funext a_1


          sorry
          -- simp [pc_c_sM1]

          simp [hpc_c_sM1 ((prec_x.pair prec_iM1)) elem]
          have rw_elemr : nn = elem.r-1 := by simp [helemr]
          rw [rw_elemr]

          simp [pc_c_sM1]
          simp [hprec_x, hprec_iM1]


          cases Classical.em ((eval_prim O c_usen (Nat.pair (Nat.pair elem.l (elem.r - 1)) (Nat.pair (n + 4 + 1) s))) = o2n Option.none) with
          | inl hh =>
            simp [hh, hnat_to_opt_0]
          | inr hh =>
            simp [not_none_imp_not_zero hh]
            rw [hnat_to_opt_2 hh]
            simp [Option.bind]
            simp [pc_mr_s]
            simp [hprec_x, hprec_iM1]
            simp [hpc_c_sM1]
            simp [pc_c_sM1]
            simp [hprec_x, hprec_iM1]

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
        cases Classical.em (eval_prim O c_usen (Nat.pair elem (Nat.pair m (s + 1)))=o2n Option.none) with
        | inl hh =>
          simp [hh,hnat_to_opt_0]
        | inr hh =>
          simp [not_none_imp_not_zero hh]
          simp [hnat_to_opt_2 hh]
          simp [hpc_c_sM1]
          simp [pc_c_sM1]

          cases Classical.em (eval_prim O c_usen (Nat.pair elem (Nat.pair m (s + 1))) - 1 = 0) with
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


@[simp] theorem c_usen_evp: eval_prim O (c_usen) (Nat.pair x (Nat.pair code s)) =
  Encodable.encode (usen O code s x) := by

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
  | 0,    0    => exact c_usen_evp_aux_x_0_0
  | 0,    n+1  => exact c_usen_evp_aux_0_np1
  | sM1+1, 0   => apply c_usen_evp_aux; decide
  | sM1+1, 1   => apply c_usen_evp_aux; decide
  | sM1+1, 2   => apply c_usen_evp_aux; decide
  | sM1+1, 3   => apply c_usen_evp_aux; decide
  | sM1+1, 4   => apply c_usen_evp_aux; decide
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
      simp [decodeCode]
      simp [usen,hno, hn2o]

      rw [c_usen_evp_aux_nMod4]
      simp [h0]

      rw [ih mr_s mr_s_lt_cs];
      rw [ih ml_s ml_s_lt_cs];
      simp [ml_s, mr_s, m]

    -- prec
    | true =>
      have h0: n%4=2 := nMod4_eq_2 hno hn2o

      -- simplify the rhs
      simp [decodeCode]
      simp only [hno, hn2o, usen]

      rw [c_usen_evp_aux_nMod4]
      simp [h0]

      rw [ih ml_s ml_s_lt_cs]
      simp
      -- rw [show Nat.pair (n+4+1) sM1 = c_sM1 from rfl]
      unfold ml_s
      unfold m
      simp
      apply congrArg
      funext _0
      apply congrFun
      apply congrArg
      funext _1 _2

      rw [ih c_sM1 c_sM1_lt_cs]
      simp
      have rw3_aux : encodeCode (((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r))) = (n + 4 + 1) := by
            simp [encodeCode]
            apply codes_aux_2 hno hn2o

      have rw3 : ((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r)) = (decodeCode (n + 4 + 1)) := by
        rw [←(decodeCode_encodeCode (decodeCode (n + 4 + 1)))]
        rw [←(decodeCode_encodeCode (((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r))))]
        simp [rw3_aux]
      rw [rw3]
      unfold c_sM1
      simp
      apply congrArg
      funext _3
      apply congrArg
      funext _4
      rw [ih mr_s mr_s_lt_cs]
      simp
      unfold mr_s; unfold m; simp


  | true => cases hn2o:n.div2.bodd with
    -- comp
    | false =>
      have h0: n%4=1 := nMod4_eq_1 hno hn2o

      -- simplify the rhs
      -- simp
      simp [decodeCode]
      simp [usen,hno, hn2o]

      rw [c_usen_evp_aux_nMod4]
      simp [h0]

      rw [ih mr_s mr_s_lt_cs];
      simp [mr_s, m]
      apply congrArg
      funext xx
      apply congrArg
      funext xxx
      apply congrArg
      funext xxxx
      rw [ih ml_s ml_s_lt_cs];
      simp [ml_s, m]

    -- rfind
    | true =>
      have h0: n%4=3 := nMod4_eq_3 hno hn2o
      simp [decodeCode]
      simp [usen,hno, hn2o]

      rw [c_usen_evp_aux_nMod4]
      simp [h0]

      rw [ih m_s m_s_lt_cs];
      rw [ih c_sM1 c_sM1_lt_cs]

      cases Classical.em (x≤sM1) with
      | inl h =>
        simp [h]
        simp [m_s]
        simp [m]
        simp [c_sM1]

        have rw0_aux : encodeCode ((decodeCode n.div2.div2).rfind') = n + 4 + 1 := by
          simp [encodeCode]
          exact codes_aux_3 hno hn2o
        have rw0 : (decodeCode (n + 4 + 1)) = (decodeCode n.div2.div2).rfind' := by
          rw [←(decodeCode_encodeCode (decodeCode (n + 4 + 1)))]
          rw [←decodeCode_encodeCode ((decodeCode n.div2.div2).rfind')]
          simp [rw0_aux]
        rw [rw0]

      | inr h => simp [h,Option.bind]

@[simp] theorem c_usen_ev_pr:code_prim (c_usen) := by
  -- unfold c_usen_aux;+
  sorry
@[simp] theorem c_usen_ev: eval O c_usen (Nat.pair x (Nat.pair code s)) = o2n (usen O s code x) := by
  rw [← eval_prim_eq_eval c_usen_ev_pr];
  simp only [PFun.coe_val, c_usen_evp, Part.coe_some]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.usen:Nat.PrimrecIn O (unpaired usen) := by rw [← c_usen_evp]; apply code_prim_prop c_usen_ev_pr
-- theorem Nat.Primrec.usen:Nat.Primrec (unpaired usen) := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.usen
end usen


section eval
namespace Nat.RecursiveIn.Code
def c_eval := (c_rfindOpt (c_usen.comp₃ (right.comp left) (left.comp left) right))
@[simp] theorem c_eval_ev: eval O c_eval (Nat.pair c x) = eval O c x := by
  simp only [c_eval, comp₃, comp₂]
  have : code_total O ((c_usen.comp ((right.comp left).pair ((left.comp left).pair right)))) := by
    apply prim_total
    repeat (first|assumption|simp|constructor)
  simp [c_rfindOpt_ev this]
  rw [eval_eq_rfindOpt]
  simp [eval,Seq.seq]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.eval:Nat.PrimrecIn O Nat.eval := by ...
-- theorem Nat.Primrec.eval:Nat.Primrec Nat.eval := by ...
end eval
