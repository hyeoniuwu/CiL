/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Eval
import Computability.Use.Principle

/-!
# Use.lean

This file constructs codes for `usen` and `use`, almost identically in structure to
Computability/Constructions/Eval.lean, which we refer readers to for more documentation.

## Main declarations
- `c_usen`: code for `usen`.
- `c_usen_evp`: asserts that `c_usen` implements the `usen` function.
- `c_use`: code for `use`.
- `c_use_ev`: asserts that `c_use` implements the `use` function.

## Notation/quirks

 - Where `x`, `y` are naturals, `⟪x, y⟫ = Nat.pair x y`.

-/

open List Nat

section usen
namespace Oracle.Single.Code

/--
`eval c_usen_aux (_, (c,s)) .last = [ [c]ₛ(0), [c]ₛ(1), ..., [c]ₛ(s) ]`
`eval c_usen_aux (_, (c,s)).last` is the list of computations of code c for s steps on all inputs
x=0 to s.
-/
def c_usen_aux :=
  let code_s   := succ.comp (left.comp right)
  let code     := left.comp code_s
  let s        := right.comp code_s
  let sM1      := c_pred.comp s
  let comp_hist := right.comp right
  let n        := c_sub.comp₂ code (c_const 5)
  let m        := c_div2.comp <| c_div2.comp n
  let ml       := left.comp m
  let mr       := right.comp m
  let nMod4    := c_mod.comp₂ n (c_const 4)
  let ele := left
-- the opt_* functions will be used with c_list_map'.
-- so, it will take inputs of the form (number in list, criut).
  let opt_zero  := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) <| succ.comp (zero.comp   ele)
  let opt_oracle := c_if_gt_te.comp₄ ele (sM1.comp right) (c_const 0) <| succ.comp (succ.comp   ele)
  let zero_mapped := (c_list_map' opt_zero).comp₂ (c_list_range.comp s) c_id
  let oracle_mapped := (c_list_map' opt_oracle).comp₂ (c_list_range.comp s) c_id
  -- lookup returns `[c]ₛ(x)`
  let lookup (x' c' s') :=
    c_list_getI.comp₂ (c_list_getI.comp₂ (comp_hist.comp right) (pair c' s')) x'
  let pc_ml_s c' := lookup c' (ml.comp right)   (s.comp right)   -- `[ml]ₛ(x)`
  let pc_mr_s c' := lookup c' (mr.comp right)   (s.comp right)   -- `[mr]ₛ(x)`
  let pc_m_s  c' := lookup c' (m.comp  right)   (s.comp right)   -- `[mr]ₛ(x)`
  let pc_c_sM1 c' := lookup c' (code.comp right) (sM1.comp right) -- `[code]_{s-1}(x)`
  let opt_pair := c_if_gt_te.comp₄ ele (sM1.comp right) c_opt_none <|
    c_ifz.comp₃ (pc_ml_s ele) c_opt_none <|
    c_ifz.comp₃ (pc_mr_s ele) c_opt_none <|
    succ.comp (c_max.comp₂ (c_opt_iget.comp (pc_ml_s ele)) (c_opt_iget.comp (pc_mr_s ele)))
  let comp_usen_cg := pc_mr_s ele
  let comp_evaln_cg := c_evaln.comp₃ ele (mr.comp right) (s.comp right)
  let comp_usen_cf := pc_ml_s <| c_pred.comp comp_evaln_cg
  let opt_comp := c_if_gt_te.comp₄ ele (sM1.comp right) c_opt_none <|
    c_ifz.comp₃ comp_usen_cg  c_opt_none <|
    c_ifz.comp₃ comp_evaln_cg c_opt_none <|
    c_ifz.comp₃ comp_usen_cf  c_opt_none <|
    c_max.comp₂ comp_usen_cf comp_usen_cg
  let prec_x         := left.comp ele
  let prec_i         := right.comp ele
  let prec_iM1       := c_pred.comp prec_i
  let prec_usen_base := pc_ml_s prec_x
  let prec_usen_prev := pc_c_sM1 (pair prec_x (prec_iM1))
  let prec_evaln_prev := c_evaln.comp₃ (pair prec_x (prec_iM1)) (code.comp right) (sM1.comp right)
  let prec_usen_indt := pc_mr_s (pair prec_x (pair prec_iM1 (c_pred.comp prec_evaln_prev)))
  let opt_prec := c_if_gt_te.comp₄ ele (sM1.comp right) c_opt_none <|
    c_ifz.comp₃ prec_i          prec_usen_base <|
    c_ifz.comp₃ prec_usen_prev  c_opt_none <|
    c_ifz.comp₃ prec_evaln_prev c_opt_none <|
    c_ifz.comp₃ prec_usen_indt  c_opt_none <|
    succ.comp <| c_max.comp₂ (c_opt_iget.comp prec_usen_prev) (c_opt_iget.comp prec_usen_indt)
  let rfind'_usen_base := pc_m_s ele
  let rfind'_evaln_base := c_evaln.comp₃ ele (m.comp right) (s.comp right)
  let rfind'_usen_indt := pc_c_sM1 (pair (left.comp ele) (succ.comp (right.comp ele)))
  let opt_rfind' := c_if_gt_te.comp₄ ele (sM1.comp right) c_opt_none <|
    c_ifz.comp₃ rfind'_usen_base c_opt_none <|
    c_ifz.comp₃ rfind'_evaln_base c_opt_none <|
    c_ifz.comp₃ (c_opt_iget.comp rfind'_evaln_base) rfind'_usen_base <|
    c_ifz.comp₃ rfind'_usen_indt c_opt_none <|
    succ.comp <| c_max.comp₂ (c_opt_iget.comp rfind'_usen_base) (c_opt_iget.comp rfind'_usen_indt)
  let comp_mapped  := (c_list_map' opt_comp).comp₂   (c_list_range.comp s) c_id
  let pair_mapped  := (c_list_map' opt_pair).comp₂   (c_list_range.comp s) c_id
  let prec_mapped  := (c_list_map' opt_prec).comp₂   (c_list_range.comp s) c_id
  let rfind'_mapped := (c_list_map' opt_rfind').comp₂ (c_list_range.comp s) c_id
  c_cov_rec
  (c_list_singleton zero) <|
  c_if_eq_te.comp₄ s     (c_const 0) (c_list_singleton zero) <| -- if s=0, then diverge
  c_if_eq_te.comp₄ code  (c_const 0) zero_mapped   <|
  c_if_eq_te.comp₄ code  (c_const 1) zero_mapped   <|
  c_if_eq_te.comp₄ code  (c_const 2) zero_mapped   <|
  c_if_eq_te.comp₄ code  (c_const 3) zero_mapped   <|
  c_if_eq_te.comp₄ code  (c_const 4) oracle_mapped <|
  c_if_eq_te.comp₄ nMod4 (c_const 0) pair_mapped   <|
  c_if_eq_te.comp₄ nMod4 (c_const 1) comp_mapped   <|
  c_if_eq_te.comp₄ nMod4 (c_const 2) prec_mapped   <|
                                     rfind'_mapped

/-- api: `Nat.pair x (Nat.pair code s)` -/
def c_usen :=
  c_list_getI.comp₂ (c_list_getLastI.comp <| c_usen_aux.comp (pair (c_const 17) right)) left

theorem c_usen_evp_aux_x_0_0 {O x} : evalp O c_usen ⟪x, 0, 0⟫ = o2n (usen O 0 0 x) := by
  unfold c_usen; unfold c_usen_aux
  lift_lets; extract_lets; expose_names
  rw [show Nat.pair 0 0 = 0 from rfl]
  simp [getI, usen]

theorem c_usen_evp_aux_0_np1 {O x n} : evalp O c_usen ⟪x, n+1, 0⟫ = o2n (usen O (n+1).n2c 0 x) := by
  unfold c_usen; unfold c_usen_aux
  lift_lets; extract_lets; expose_names
  let k := ⟪n+1, 0⟫-1
  have kP1_gt_0 : ⟪n+1, 0⟫>0 := by
    apply pair_l_gt0
    exact zero_lt_succ n
  have hkP1: k+1 = ⟪n+1, 0⟫ := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]
  let (eq := hinp) inp := (evalp O c_usen_aux ⟪17, k⟫)
  unfold c_usen_aux at hinp; lift_lets at hinp
  let (eq := hcri) cri := ⟪17, k, inp⟫
  simp [-comp₄_evp]
  simp [←hinp, ←hcri]
  have hs : evalp O s cri = 0 := by simp [s,code_s,cri,hkP1]
  simp [hs, getI, usen]

theorem c_usen_evp_aux {O code x s} (hcode_val : code ≤ 4) :
    evalp O c_usen (Nat.pair x (Nat.pair code (s+1))) =
    o2n (usen O code.n2c (s+1) x) := by
  unfold c_usen; unfold c_usen_aux
  lift_lets; extract_lets; expose_names
  let k := ⟪code, s+1⟫-1
  have kP1_gt_0 : ⟪code, s+1⟫>0 := by
    apply pair_r_gt0
    exact zero_lt_succ s
  have hkP1: k+1 = ⟪code, s+1⟫ := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]
  let (eq := hinp) inp := (evalp O c_usen_aux ⟪17, k⟫)
  unfold c_usen_aux at hinp; lift_lets at hinp
  let (eq := hcri) cri := ⟪17, k, inp⟫
  simp only [evp_simps, ← hinp, ←hcri]
  have hcode_s : evalp O code_s cri = ⟪code, s+1⟫ := by simp [code_s,cri,hkP1]
  have hs     : evalp O s_1 cri = s+1 := by simp [s_1,hcode_s]
  have hsM1   : evalp O sM1 cri = s := by simp [sM1,hs]
  have hcode  : evalp O code_1 cri = code := by simp [code_1,hcode_s]
  have hopt_zero :
      (fun ele => evalp O opt_zero ⟪ele, cri⟫) =
      (o2n ∘ usen O zero (s+1)) := by
    funext elem
    simp only [evp_simps, opt_zero, hsM1,ele, usen]
    cases Classical.em (elem ≤ s) with
    | inl h => simp [h, Nat.not_lt_of_le h]
    | inr h => simp [h, gt_of_not_le h]
  have hopt_oracle :
      (fun ele => evalp O opt_oracle ⟪ele, cri⟫) =
      (o2n ∘ usen O oracle (s+1)) := by
      funext elem
      simp only [evp_simps, opt_oracle, hsM1, ele, usen]
      cases Classical.em (elem ≤ s) with
      | inl h => simp [h, Nat.not_lt_of_le h]
      | inr h => simp [h, gt_of_not_le h]
  have hzero_mapped :
      evalp O zero_mapped cri = (map (o2n ∘ usen O zero (s+1)) (range (s+1))) := by
    simp [zero_mapped, hs,hopt_zero]
  have horacle_mapped :
      evalp O oracle_mapped cri = (map (o2n ∘ usen O oracle (s+1)) (range (s+1))) := by
    simp [oracle_mapped, hs,hopt_oracle]
  simp only [hs,hcode]
  match code with
  | 0 =>
    simp only [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, usen, le_of_lt_succ h]
    | inr h => simp [h, n2c, usen, Nat.not_le_of_lt (not_lt.mp h)]
  | 1 =>
    simp only [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, usen, le_of_lt_succ h]
    | inr h => simp [h, n2c, usen, Nat.not_le_of_lt (not_lt.mp h)]
  | 2 =>
    simp only [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, usen, le_of_lt_succ h]
    | inr h => simp [h, n2c, usen, Nat.not_le_of_lt (not_lt.mp h)]
  | 3 =>
    simp only [hzero_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, usen, le_of_lt_succ h]
    | inr h => simp [h, n2c, usen, Nat.not_le_of_lt (not_lt.mp h)]
  | 4 =>
    simp only [horacle_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, n2c, usen, le_of_lt_succ h]
    | inr h => simp [h, n2c, usen, Nat.not_le_of_lt (not_lt.mp h)]
  | n+5 => simp at hcode_val

private lemma hnat_5 {a b} (h : a ≠ 0) : ((a-1).max (b-1))+1 = a.max b := by
  grind only [= max_def]
theorem c_usen_evp_aux_nMod4 {O x n s} :
    evalp O c_usen ⟪x, (n+4)+1, s+1⟫ =
    let m := n.div2.div2
    let ml := m.l
    let mr := m.r
    let k := ⟪(n+4)+1, s+1⟫-1
    let inp := (evalp O c_usen_aux ⟪17, k⟫)
    let cri := ⟪17, k, inp⟫
    let pc_ml_s  c' elem := evalp O c_usen ⟪evalp O c' ⟪elem, cri⟫, ml,      s+1⟫
    let pc_mr_s  c' elem := evalp O c_usen ⟪evalp O c' ⟪elem, cri⟫, mr,      s+1⟫
    let pc_m_s   c' elem := evalp O c_usen ⟪evalp O c' ⟪elem, cri⟫, m,       s+1⟫
    let pc_c_sM1 c' elem := evalp O c_usen ⟪evalp O c' ⟪elem, cri⟫, (n+4)+1, s⟫
    let opt_pair elem := o2n do
      guard (elem ≤ s)
      let usen_cf ← n2o (pc_ml_s left elem)
      let usen_cg ← n2o (pc_mr_s left elem)
      return Nat.max usen_cf usen_cg
    let opt_comp elem := o2n do
      guard (elem ≤ s);
      let usen_cg ← n2o (pc_mr_s left elem)
      let evaln_cg ← evaln O (s+1) mr.n2c elem
      let usen_cf  ← n2o (pc_ml_s left evaln_cg)
      Nat.max usen_cf usen_cg
    let opt_prec x := o2n do
      guard (x ≤ s)
      let (xl, i) := Nat.unpair x
      (i.casesOn
      (n2o (pc_ml_s left xl))
      fun iM1 =>
      do
        let usen_prev  ← n2o <| pc_c_sM1 left (Nat.pair xl iM1)
        let evaln_prev ← evaln O s (n2c (n+4+1)) (Nat.pair xl iM1)
        let usen_indt  ← n2o <| pc_mr_s left (Nat.pair xl (Nat.pair iM1 evaln_prev))
        return Nat.max usen_prev usen_indt)
    let opt_rfind' x := (o2n do
      guard (x ≤ s);
      let usen_base  ← n2o <| pc_m_s left x
      let evaln_base ← evaln O (s+1) m.n2c x
      if evaln_base=0 then usen_base else
      let usen_indt  ← n2o <| pc_c_sM1 left (Nat.pair x.l (x.r+1))
      return Nat.max usen_base usen_indt)
        if n%4=0 then opt_pair x
    else if n%4=1 then opt_comp x
    else if n%4=2 then opt_prec x
    else if n%4=3 then opt_rfind' x
    else 0 := by
  lift_lets; extract_lets; expose_names
  unfold c_usen; unfold c_usen_aux
  lift_lets; extract_lets; expose_names
  simp only [evp_simps]
  have kP1_gt_0 : Nat.pair ((n+4)+1) (s+1)>0 := pair_nonzero_right_pos
  have hkP1: k+1=⟪(n+4)+1, s+1⟫ := by
    exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]
  have hinp : inp = (evalp O c_usen_aux ⟪17, k⟫) := rfl
  unfold c_usen_aux at hinp; lift_lets at hinp
  have hcri : ⟪17, k, inp⟫ = cri := rfl
  simp only [evp_simps, ← hinp, hcri]
  -- show that the code let-bindings correspond to our let-bindings
  have hcode_s : evalp O code_s cri = ⟪(n+4)+1, s+1⟫ := by simp [code_s,cri,hkP1]
  have hs     : evalp O s_1 cri    = s+1    := by simp [s_1,hcode_s]
  have hsM1   : evalp O sM1 cri    = s      := by simp [sM1,hs]
  have hcode  : evalp O code cri   = (n+4)+1 := by simp [code,hcode_s]
  have hn     : evalp O n_1 cri    = n      := by simp [n_1,hcode]
  have hm     : evalp O m_1 cri    = m      := by simp [m_1,hn,m,div2_val]
  have hml    : evalp O ml_1 cri   = ml     := by simp [ml_1,hm,ml]
  have hmr    : evalp O mr_1 cri   = mr     := by simp [mr_1,hm,mr]
  have hnMod4 : evalp O nMod4 cri  = n%4    := by simp [nMod4,hn]
  have hlookup {x' c' s'} (elem : ℕ)
      (hcs'': Nat.pair (evalp O c' ⟪elem, cri⟫) (evalp O s' ⟪elem, cri⟫) ≤ k) :
      evalp O (lookup x' c' s') ⟪elem, cri⟫ =
      let x'' := evalp O x' ⟪elem, cri⟫
      let c'' := evalp O c' ⟪elem, cri⟫
      let s'' := evalp O s' ⟪elem, cri⟫
      evalp O c_usen (Nat.pair x'' (Nat.pair c'' s'')) := by
    lift_lets; extract_lets; expose_names
    have aux1 : evalp O x' ⟪elem, cri⟫ = x'' := by simp [x'']
    have aux2 : evalp O c' ⟪elem, cri⟫ = c'' := by simp [c'']
    have aux3 : evalp O s' ⟪elem, cri⟫ = s'' := by simp [s'']
    simp only [lookup]
    simp [aux1,aux2,aux3] at hcs'' ⊢
    simp [comp_hist, cri, inp, c_usen, c_usen_aux, hcs'']
  have bounds_left {elem : ℕ} :
      Nat.pair
        (evalp O (ml_1.comp right) ⟪elem, cri⟫)
        (evalp O (s_1.comp right) ⟪elem, cri⟫) ≤ k := by
    simpa [hml,hs] using c_evaln_bounds_left
  have bounds_right {elem : ℕ} :
      Nat.pair
        (evalp O (mr_1.comp right) ⟪elem, cri⟫)
        (evalp O (s_1.comp right) ⟪elem, cri⟫) ≤ k := by
    simpa [hmr,hs] using c_evaln_bounds_right
  have bounds_m {elem : ℕ} :
      Nat.pair
        (evalp O (m_1.comp right) ⟪elem, cri⟫)
        (evalp O (s_1.comp right) ⟪elem, cri⟫) ≤ k := by
    simpa [hm,hs] using c_evaln_bounds_3
  have bounds_pc_c_sM1 {elem : ℕ} :
      Nat.pair
        (evalp O (code.comp right) ⟪elem, cri⟫)
        (evalp O (sM1.comp right) ⟪elem, cri⟫) ≤ k := by
    simpa [hcode,hsM1] using c_evaln_bounds_4
  have hpc_ml_s c' (elem : ℕ): (evalp O (pc_ml_s_1 c') ⟪elem, cri⟫) = pc_ml_s c' elem := by
    simp [pc_ml_s_1, hlookup elem bounds_left, pc_ml_s, hs,hml,cri]
  have hpc_mr_s c' (elem : ℕ): evalp O (pc_mr_s_1 c') ⟪elem, cri⟫ = pc_mr_s c' elem := by
    simp [pc_mr_s_1, hlookup elem bounds_right, pc_mr_s, hs,hmr,cri]
  have hpc_m_s c' (elem : ℕ): evalp O (pc_m_s_1 c') ⟪elem, cri⟫ = pc_m_s c' elem := by
    simp [pc_m_s_1, hlookup elem bounds_m, pc_m_s, hs,hm,cri]
  have hpc_c_sM1 c' (elem : ℕ): evalp O (pc_c_sM1_1 c') ⟪elem, cri⟫ = pc_c_sM1 c' elem := by
    simp [pc_c_sM1_1, hlookup elem bounds_pc_c_sM1, pc_c_sM1, hsM1,hcode,cri]
  have hopt_pair :
      (fun ele => evalp O opt_pair_1 ⟪ele, cri⟫) =
      opt_pair := by
    funext elem
    simp only [evp_simps, opt_pair_1,hsM1, ele,hpc_ml_s, hpc_mr_s, opt_pair]
    cases Classical.em (elem ≤ s) with
    | inr h => simp [h, gt_of_not_le h]
    | inl h =>
      simp only [h, Nat.not_lt_of_le h]
      cases Classical.em (pc_ml_s left elem=o2n Option.none) with
      | inl hh => simp [hh, hnat_to_opt_0]
      | inr hh =>
        simp only [not_none_imp_not_zero hh, hnat_to_opt_2 hh]
        cases Classical.em (pc_mr_s left elem=o2n Option.none) with
        | inl hhh => simp [hhh, hnat_to_opt_0]
        | inr hhh => simp [not_none_imp_not_zero hhh, hnat_to_opt_2 hhh]
  have hpair_mapped :
      evalp O pair_mapped cri = (map (opt_pair) (range (s+1))) := by
    simp [pair_mapped, hs,hopt_pair]
  have hcomp_usen_cg elem :
      evalp O comp_usen_cg ⟪elem, cri⟫ = pc_mr_s left elem := by
    simp [comp_usen_cg, hpc_mr_s, ele]
  have hcomp_evaln_cg elem :
      evalp O comp_evaln_cg ⟪elem, cri⟫ = o2n (evaln O (s+1) (n2c mr) elem) := by
    simp [comp_evaln_cg, hs,hmr,ele]
  have hcomp_usen_cf elem :
      evalp O comp_usen_cf ⟪elem, cri⟫ = pc_ml_s (c_pred.comp comp_evaln_cg) elem := by
    simp [comp_usen_cf, hpc_ml_s]
  have hopt_comp :
      (fun ele => evalp O opt_comp_1 ⟪ele, cri⟫) =
      opt_comp := by
    funext elem
    simp only [evp_simps, opt_comp_1, hsM1,ele,opt_comp]
    cases Classical.em (elem ≤ s) with
    | inr h => simp [h, gt_of_not_le h]
    | inl h =>
      simp only [h, Nat.not_lt_of_le h]
      simp only [hcomp_usen_cg]
      cases Classical.em (pc_mr_s left elem=o2n Option.none) with
      | inl hh => simp [hh, hnat_to_opt_0]
      | inr hh =>
        simp only [not_none_imp_not_zero hh, hnat_to_opt_2 hh]
        simp only [hcomp_evaln_cg]
        cases Classical.em ((evaln O (s + 1) (n2c mr) elem)=Option.none) with
        | inl hhh => simp [hhh]
        | inr hhh =>
        simp only [hnat_1 hhh]
        simp? says
          simp only [↓reduceIte, Encodable.encode_none, unpaired2, pair_l, pair_r, guard_true,
            Option.pure_def, Nat.n2c, Option.bind_eq_bind, Option.bind_some]
        simp only [Option.isSome.bind (Option.isSome_iff_ne_none.mpr hhh)]
        simp only [hcomp_usen_cf]
        have :
            pc_ml_s (c_pred.comp comp_evaln_cg) elem =
            (pc_ml_s left ((evaln O (s + 1) (n2c mr) elem).get
            (Option.isSome_iff_ne_none.mpr hhh))) := by
          unfold pc_ml_s
          simp [hcomp_evaln_cg]
          simp [hnat_2 (Option.isSome_iff_ne_none.mpr hhh)]
        rw [this]
        cases Classical.em (
          pc_ml_s left
          ((evaln O (s + 1) (n2c mr) elem).get
            (Option.isSome_iff_ne_none.mpr hhh)) = 0) with
        | inl hhhh => simp [hhhh]
        | inr hhhh =>
          simp [not_none_imp_not_zero hhhh, hnat_to_opt_2 hhhh]
          simp [hnat_5 hhhh]
  have hcomp_mapped : evalp O comp_mapped cri = (map (opt_comp) (range (s+1))) := by
    simp [comp_mapped, hs,hopt_comp]
  have hprec_x elem : evalp O prec_x ⟪elem, cri⟫ = elem.l := by simp [prec_x,ele]
  have hprec_i elem : evalp O prec_i ⟪elem, cri⟫ = elem.r := by simp [prec_i,ele]
  have hprec_iM1 elem : evalp O prec_iM1 ⟪elem, cri⟫ = elem.r-1 := by simp [prec_iM1,hprec_i]
  have hprec_usen_base elem :
      evalp O prec_usen_base ⟪elem, cri⟫ = ((pc_ml_s left elem.l)) := by
    simp [prec_usen_base, hpc_ml_s];
    simp [pc_ml_s, hprec_x]
  have hprec_usen_prev elem :
      (evalp O prec_usen_prev ⟪elem, cri⟫) =
      (pc_c_sM1 left (Nat.pair elem.l (elem.r-1))) := by
    simp [prec_usen_prev,hpc_c_sM1,pc_c_sM1,hprec_x,hprec_iM1]
  have hprec_evaln_prev elem :
      (evalp O prec_evaln_prev ⟪elem, cri⟫) =
      o2n (evaln O s (n2c (n+4+1)) (Nat.pair elem.l (elem.r - 1))) := by
    simp [prec_evaln_prev,hsM1,hcode,hprec_x,hprec_iM1]
  have hprec_usen_indt elem hdom :
      (evalp O prec_usen_indt ⟪elem, cri⟫) =
      pc_mr_s left
        (Nat.pair elem.l
        (Nat.pair (elem.r - 1) ((evaln O s (n2c (n + 4 + 1))
        (Nat.pair elem.l (elem.r - 1))).get hdom))) := by
    simp only [prec_usen_indt,hpc_mr_s,pc_mr_s,hprec_x, hprec_iM1,hprec_evaln_prev, evp_simps]
    apply congrArg; apply congrFun; apply congrArg; apply congrArg; apply congrArg
    exact hnat_2 hdom
  have hopt_prec :
      (fun ele => evalp O opt_prec_1 ⟪ele, cri⟫) =
      opt_prec := by
    funext elem
    simp only [evp_simps,opt_prec_1,hsM1,ele,hprec_i,hprec_usen_base, opt_prec]
    cases Classical.em (elem ≤ s) with
    | inr h => simp [h, gt_of_not_le h]
    | inl h =>
      simp only [h, Nat.not_lt_of_le h]
      simp only [pc_ml_s]
      simp? says
        simp only [↓reduceIte, evalp, pair_l, Encodable.encode_none, unpaired2, pair_r,
          succ_eq_add_one, guard_true, Option.pure_def, unpair1_to_l, Option.bind_eq_bind,
          unpair2_to_r, Option.bind_some]
      cases helemr : elem.r with
      | zero => simp
      | succ elemrM1 =>
        have rm1rw : elemrM1 = elem.r -1 := Nat.eq_sub_of_add_eq (_root_.id (Eq.symm helemr))
        rw [rm1rw]
        simp only [hprec_usen_prev, hprec_evaln_prev]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        cases Classical.em (evaln O s (n2c (n + 4 + 1)) ⟪elem.l, elem.r - 1⟫ = Option.none) with
        | inl hh => simp [hh]
        | inr hh =>
        simp only [hnat_1 hh, ↓reduceIte]
        simp only [Option.isSome.bind <| Option.ne_none_iff_isSome.mp hh]
        simp only [hprec_usen_indt elem (Option.ne_none_iff_isSome.mp hh)]
        cases Classical.em ((pc_mr_s left ⟪elem.l, elem.r - 1,
            (evaln O s (n2c (n + 4 + 1)) (Nat.pair elem.l (elem.r - 1))).get
            (Option.ne_none_iff_isSome.mp hh)⟫) =
          o2n Option.none) with
        | inl hhh => simp [hhh]
        | inr hhh =>
          simp only [not_none_imp_not_zero hhh, hnat_to_opt_2 hhh]
          cases Classical.em (pc_c_sM1 left (Nat.pair elem.l (elem.r - 1)) = o2n Option.none)  with
          | inl hhhh => simp [hhhh]
          | inr hhhh => simp [not_none_imp_not_zero hhhh, hnat_to_opt_2 hhhh]
  have hprec_mapped : evalp O prec_mapped cri = (map (opt_prec) (range (s+1))) := by
    simp [prec_mapped, hs,hopt_prec]
  have hrfind'_use_base elem:
      evalp O rfind'_usen_base ⟪elem, cri⟫ = (pc_m_s left elem) := by
    simp [rfind'_usen_base,hpc_m_s,ele]
  have hrfind'_evaln_base elem :
      evalp O rfind'_evaln_base ⟪elem, cri⟫ = o2n (evaln O (s + 1) (n2c m) elem) := by
    simp [rfind'_evaln_base,hs,hm,ele]
  have hrfind'_usen_indt elem:
      evalp O rfind'_usen_indt ⟪elem, cri⟫ =
      (pc_c_sM1 left (Nat.pair elem.l (elem.r + 1))) := by
    simp [rfind'_usen_indt,hpc_c_sM1,ele,pc_c_sM1]
  have hopt_rfind' :
      (fun ele => evalp O opt_rfind'_1 ⟪ele, cri⟫) =
      opt_rfind' := by
    funext elem
    simp only [evp_simps, opt_rfind'_1, hsM1,ele, opt_rfind']
    cases Classical.em (elem ≤ s) with
    | inr h => simp [gt_of_not_le h, h];
    | inl h =>
      simp only [h, Nat.not_lt_of_le h]
      simp only [hrfind'_use_base]
      cases Classical.em ( pc_m_s left elem=o2n Option.none) with
      | inl hh => simp [hh,hnat_to_opt_0]
      | inr hh =>
        simp only [not_none_imp_not_zero hh, hnat_to_opt_2 hh]
        simp only [hrfind'_evaln_base]
        cases Classical.em ((evaln O (s + 1) (n2c m) elem) = Option.none) with
        | inl hhh => simp [hhh]
        | inr hhh =>
          simp only [hnat_1 hhh]
          simp only [↓reduceIte, Denumerable.ofNat_encode, Encodable.encode_none, unpaired2,
            Option.getD_some, pair_l, pair_r, succ_eq_add_one, guard_true, Option.pure_def, Nat.n2c,
            Option.bind_eq_bind, Option.bind_some]
          simp only [Option.isSome.bind <| Option.ne_none_iff_isSome.mp hhh]
          simp only [getD_eq_get <| Option.ne_none_iff_isSome.mp hhh]
          cases (evaln O (s + 1) (n2c m) elem).get (Option.ne_none_iff_isSome.mp hhh) with
          | zero => simpa using (succ_pred_eq_of_ne_zero (not_none_imp_not_zero hh)).symm
          | succ _ =>
            simp only [hrfind'_usen_indt]
            cases Classical.em ( pc_c_sM1 left (Nat.pair elem.l (elem.r + 1))=o2n Option.none) with
            | inl hhhh => simp [hhhh,hnat_to_opt_0]
            | inr hhhh => simp [not_none_imp_not_zero hhhh, hnat_to_opt_2 hhhh]
  have hrfind'_mapped : evalp O rfind'_mapped cri = (map (opt_rfind') (range (s+1))) := by
    simp [rfind'_mapped, hs,hopt_rfind']
  simp only [hs,hcode,hnMod4]
  match h : n%4 with
  | 0 => simpa [hpair_mapped, opt_pair] using fun hh => by simp [Nat.not_le_of_lt hh]
  | 1 => simpa [hcomp_mapped, opt_comp] using fun hh => by simp [Nat.not_le_of_lt hh]
  | 2 => simpa [hprec_mapped, opt_prec] using fun hh => by simp [Nat.not_le_of_lt hh]
  | 3 => simpa [hrfind'_mapped, opt_rfind'] using fun hh => by simp [Nat.not_le_of_lt hh]
  | x+4 =>
    have contrad : n%4<4 := by
      apply Nat.mod_lt
      decide
    rw [h] at contrad
    rw [show x.succ.succ.succ.succ=x+4 from rfl] at contrad
    simp at contrad

@[simp, evp_simps] theorem c_usen_evp {O x code s} :
    evalp O c_usen ⟪x, code, s⟫ =
    o2n (usen O code.n2c s x) := by
  let code_s := Nat.pair code s
  rw [show Nat.pair code s = code_s by rfl]
  rw [show code = code_s.l by simp [code_s]]
  rw [show s = code_s.r by simp [code_s]]
  induction code_s using Nat.strong_induction_on generalizing x with
  | _ code_s ih =>
  let code := code_s.l
  let s := code_s.r
  rw [show code_s = (Nat.pair code s) from by simp [code,s]]
  simp only [pair_r, pair_l]
  match hs_val : s,hcode_val : code with
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
  let ml_s  := ⟪m.l,   sM1+1⟫
  let mr_s  := ⟪m.r,   sM1+1⟫
  let m_s   := ⟪m,     sM1+1⟫
  let c_sM1 := ⟪n+4+1, sM1⟫
  have ml_s_lt_cs  : ml_s  < code_s := by rw [hcode_s]; exact pair_lt_pair_left  (sM1+1) _m1
  have mr_s_lt_cs  : mr_s  < code_s := by rw [hcode_s]; exact pair_lt_pair_left  (sM1+1) _m2
  have m_s_lt_cs   : m_s   < code_s := by rw [hcode_s]; exact pair_lt_pair_left  (sM1+1) hm
  have c_sM1_lt_cs : c_sM1 < code_s := by
    rw [hcode_s]; exact pair_lt_pair_right (n+4+1) (lt_add_one sM1)
  rw [show n+5=(n+4)+1 from rfl]
  cases hno : n.bodd with
  | false => cases hn2o : n.div2.bodd with
    | false => -- pair
      have h0: n%4=0 := nMod4_eq_0 hno hn2o
      simp [n2c, usen, hno, hn2o, c_usen_evp_aux_nMod4, h0, ih mr_s mr_s_lt_cs, ih ml_s ml_s_lt_cs,
        ml_s, mr_s, m]
    | true => -- prec
      have h0: n%4=2 := nMod4_eq_2 hno hn2o
      -- simplify the rhs
      simp only [n2c, hno, hn2o, usen]
      -- simplify the lhs
      rw [c_usen_evp_aux_nMod4]
      simp? [h0] says
        simp only [h0, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, evalp, unpair1_to_l,
          pair_l, Option.pure_def, Option.bind_eq_bind, unpair2_to_r, Encodable.encode_inj]
      -- use ih
      rw [ih ml_s ml_s_lt_cs]
      simp only [Nat.n2c, Denumerable.ofNat_encode, ml_s, m, pair_l, pair_r]
      apply congrArg; funext _0
      apply congrFun
      apply congrArg; funext _1 _2
      rw [ih c_sM1 c_sM1_lt_cs]
      simp only [Nat.n2c, Denumerable.ofNat_encode]
      have rw3_aux : c2n (((n2c n.div2.div2.l).prec (n2c n.div2.div2.r))) = (n + 4 + 1) := by
        simpa [c2n] using codes_aux_2 hno hn2o
      have rw3 : ((n2c n.div2.div2.l).prec (n2c n.div2.div2.r)) = (n2c (n + 4 + 1)) := by
        rw [←(n2c_c2n (n2c (n + 4 + 1)))]
        rw [←(n2c_c2n (((n2c n.div2.div2.l).prec (n2c n.div2.div2.r))))]
        simp [rw3_aux]
      rw [rw3]
      unfold c_sM1
      simp only [pair_l, pair_r]
      apply congrArg; funext _3
      apply congrArg; funext _4
      rw [ih mr_s mr_s_lt_cs]
      simp [mr_s, m]
  | true => cases hn2o : n.div2.bodd with
    | false => -- comp
      have h0: n%4=1 := nMod4_eq_1 hno hn2o
      -- simplify the rhs
      simp only [n2c, usen,hno, hn2o]
      -- simplify the lhs
      rw [c_usen_evp_aux_nMod4]
      simp? [h0] says
        simp only [h0, one_ne_zero, ↓reduceIte, evalp, pair_l, Nat.n2c, Option.bind_eq_bind,
          unpair2_to_r, unpair1_to_l, Option.pure_def, Encodable.encode_inj]
      rw [ih mr_s mr_s_lt_cs];
      simp only [Nat.n2c, pair_l, pair_r, Denumerable.ofNat_encode, mr_s, m]
      apply congrArg; funext _
      apply congrArg; funext _
      apply congrArg; funext _
      rw [ih ml_s ml_s_lt_cs];
      simp [ml_s, m]
    | true => -- rfind
      have h0: n%4=3 := nMod4_eq_3 hno hn2o
      -- simplify the rhs
      simp only [n2c, usen,hno, hn2o]
      -- simplify the lhs
      rw [c_usen_evp_aux_nMod4]
      simp? [h0] says
        simp only [h0, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.succ_ne_self, evalp,
          pair_l, Nat.n2c, Option.pure_def, Option.bind_eq_bind, Encodable.encode_inj]
      -- use ih
      rw [ih m_s m_s_lt_cs];
      rw [ih c_sM1 c_sM1_lt_cs]
      cases Classical.em (x ≤ sM1) with
      | inl h =>
        have rw0_aux : c2n ((n2c n.div2.div2).rfind') = n + 4 + 1 := by
          simpa [c2n] using codes_aux_3 hno hn2o
        have rw0 : (n2c (n + 4 + 1)) = (n2c n.div2.div2).rfind' := by
          rw [←(n2c_c2n (n2c (n + 4 + 1)))]
          rw [←n2c_c2n ((n2c n.div2.div2).rfind')]
          simp [rw0_aux]
        simp [h, m_s, m, c_sM1, rw0]
      | inr h => simp [h]

@[cp] theorem c_usen_prim : code_prim c_usen := by
  unfold c_usen
  unfold c_usen_aux
  extract_lets; expose_names
  -- show each let-binding is primrec
  have cp_code_s : code_prim code_s := by apply_cp
  have cp_code : code_prim code := by apply_cp
  have cp_s : code_prim s := by apply_cp
  have cp_sM1 : code_prim sM1 := by apply_cp
  have cp_comp_hist : code_prim comp_hist := by apply_cp
  have cp_n : code_prim n := by apply_cp
  have cp_m : code_prim m := by apply_cp
  have cp_ml : code_prim ml := by apply_cp
  have cp_mr : code_prim mr := by apply_cp
  have cp_nMod4 : code_prim nMod4 := by apply_cp
  have cp_ele : code_prim ele := by apply_cp
  have cp_opt_zero : code_prim opt_zero := by apply_cp
  have cp_opt_oracle : code_prim opt_oracle := by apply_cp
  have cp_zero_mapped : code_prim zero_mapped := by apply_cp
  have cp_oracle_mapped : code_prim oracle_mapped := by apply_cp
  have cp_lookup {x' c' s'} (hx' : code_prim x') (hc' : code_prim c') (hs' : code_prim s') :
    code_prim (lookup x' c' s') := by apply_cp
  have cp_pc_ml_s {c'} (hc' : code_prim c') : code_prim (pc_ml_s c') := by apply_cp
  have cp_pc_mr_s {c'} (hc' : code_prim c') : code_prim (pc_mr_s c') := by apply_cp
  have cp_pc_m_s  {c'} (hc' : code_prim c') : code_prim (pc_m_s c') := by apply_cp
  have cp_pc_c_sM1 {c'} (hc' : code_prim c') : code_prim (pc_c_sM1 c') := by apply_cp
  have cp_opt_pair : code_prim opt_pair := by apply_cp 60
  have cp_comp_usen_cg : code_prim comp_usen_cg := by apply_cp
  have cp_comp_evaln_cg : code_prim comp_evaln_cg := by apply_cp
  have cp_comp_usen_cf : code_prim comp_usen_cf := by apply_cp
  have cp_opt_comp : code_prim opt_comp := by apply_cp 60
  have cp_prec_x : code_prim prec_x := by apply_cp
  have cp_prec_i : code_prim prec_i := by apply_cp
  have cp_prec_iM1 : code_prim prec_iM1 := by apply_cp
  have cp_prec_usen_base : code_prim prec_usen_base := by apply_cp
  have cp_prec_usen_prev : code_prim prec_usen_prev := by apply_cp
  have cp_prec_evaln_prev : code_prim prec_evaln_prev := by apply_cp
  have cp_prec_usen_indt : code_prim prec_usen_indt := by apply_cp
  have cp_opt_prec : code_prim opt_prec := by apply_cp 90
  have cp_rfind'_usen_base : code_prim rfind'_usen_base := by apply_cp
  have cp_rfind'_evaln_base : code_prim rfind'_evaln_base := by apply_cp
  have cp_rfind'_usen_indt : code_prim rfind'_usen_indt := by apply_cp
  have cp_opt_rfind' : code_prim opt_rfind' := by apply_cp 90
  have cp_comp_mapped : code_prim comp_mapped := by apply_cp
  have cp_pair_mapped : code_prim pair_mapped := by apply_cp
  have cp_prec_mapped : code_prim prec_mapped := by apply_cp
  have cp_rfind'_mapped : code_prim rfind'_mapped := by apply_cp
  apply_cp 60

@[simp, ev_simps] theorem c_usen_ev {O x code s} :
    eval O c_usen ⟪x, code, s⟫ = o2n (usen O code.n2c s x) := by
  rw [← evalp_eq_eval c_usen_prim];
  simp only [PFun.coe_val, c_usen_evp, Part.coe_some]
end Oracle.Single.Code
end usen

section use
namespace Oracle.Single.Code
def c_use := (c_rfindOpt (c_usen.comp₃ (right.comp left) (left.comp left) right))
@[simp, ev_simps] theorem c_use_ev {O : ℕ → ℕ} {c : Code} {x : ℕ} : eval O c_use (Nat.pair c x) = use O c.n2c x := by
  simp only [c_use, comp₃, comp₂]
  have : code_total O ((c_usen.comp ((right.comp left).pair ((left.comp left).pair right)))) := by
    apply prim_total
    apply_cp
  simp only [c_rfindOpt_ev this]
  rw [use_eq_rfindOpt]
  simp [eval,Seq.seq]
end Oracle.Single.Code
end use
