import Computability.Constructions

section evaln
namespace Nat.RecursiveIn.Code

/--
we define the use `max(all naturals queried to the oracle)+1` 
use=0 when no queries are made.
use=none when the computation diverges.
-/
def use (O:ℕ→ℕ) (c:Code) (x:ℕ) : Part ℕ :=
match c with
| Code.zero        => 0
| Code.succ        => 0
| Code.left        => 0
| Code.right       => 0
| Code.oracle      => x+1
| Code.pair cf cg  => Nat.max <$> (use O cf x) <*> (use O cg x)
| Code.comp cf cg  => Nat.max <$> (use O cg x) <*> (eval O cg x >>= use O cf)
| Code.prec cf cg  =>
  let (n, i) := Nat.unpair x
  i.rec (use O cf n)
  fun y IH => do let IH_N ← IH; use O cg (Nat.pair n (Nat.pair y IH_N))
| Code.rfind' cf   => 1
-- actually, maybe we dont have to define it like the above.
-- theorem up_to_use

-- def eval_clamped (O:Set ℕ) (u:ℕ) (c:Code) : ℕ→.ℕ :=
def evaln_clamped (O:ℕ→ℕ) (use:ℕ) : ℕ→Code→ℕ→Option ℕ
  | 0, _ => fun _ => Option.none
  | k + 1, zero => fun n => do
    guard (n ≤ k)
    return 0
  | k + 1, succ => fun n => do
    guard (n ≤ k)
    return (Nat.succ n)
  | k + 1, left => fun n => do
    guard (n ≤ k)
    return n.unpair.1
  | k + 1, right => fun n => do
    guard (n ≤ k)
    pure n.unpair.2
  | k + 1, oracle => fun n => do
    guard (n ≤ k)
    guard (n ≤ use)
    pure (O n)
  | k + 1, pair cf cg => fun n => do
    guard (n ≤ k)
    Nat.pair <$> evaln O (k + 1) cf n <*> evaln O (k + 1) cg n
  | k + 1, comp cf cg => fun n => do
    guard (n ≤ k)
    let x ← evaln O (k + 1) cg n
    evaln O (k + 1) cf x
  | k + 1, prec cf cg => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln O (k + 1) cf a) fun y => do
        let i ← evaln O k (prec cf cg) (Nat.pair a y)
        evaln O (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evaln O (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln O k (rfind' cf) (Nat.pair a (m + 1))





/-- `eval c_evaln_aux (x,(code,s))` = `evaln s code x` -/
def c_evaln_aux :=
  let x         := left
  let code_s    := succ.comp (left.comp right)
  let code      := left.comp code_s
  let s         := right.comp code_s
  let comp_hist := right.comp right
  let n         := c_sub.comp₂ code (c_const 5)
  let m         := c_div2.comp $ c_div2.comp n

  let pcl := c_l_get.comp₂ comp_hist (pair (left.comp m)  (c_pred.comp s)) -- the previous computation corresponding to evaluating code m.l for s-1 steps.
  let pcr := c_l_get.comp₂ comp_hist (pair (right.comp m) (c_pred.comp s)) 
  let pc  := c_l_get.comp₂ comp_hist (pair m              (c_pred.comp s)) 
  let nMod4     := c_mod.comp₂ n (c_const 4)

  c_cov_rec

  (c_const 0) $

  c_if_eq_te.comp₄ s     (c_const 0) (c_const 0)     $ -- if s=0, then diverge

  c_if_eq_te.comp₄ code  (c_const 1) (succ.comp x)   $
  c_if_eq_te.comp₄ code  (c_const 2) (left.comp x)   $
  c_if_eq_te.comp₄ code  (c_const 3) (right.comp x)  $
  c_if_eq_te.comp₄ code  (c_const 4) (oracle.comp x) $
  c_if_eq_te.comp₄ nMod4 (c_const 0) (pair pcl pcr)    $
  c_if_eq_te.comp₄ nMod4 (c_const 1) (comp pcl pcr)    $
  c_if_eq_te.comp₄ nMod4 (c_const 2) (prec pcl pcr)    $
                                      rfind' pc
def c_evaln := c_l_get_last.comp c_evaln_aux

-- set_option maxRecDepth 5000 in
set_option maxHeartbeats 3 in
@[simp] theorem c_evaln_ev_pr:code_prim (c_evaln) := by
  unfold c_evaln;
  repeat (constructor; try simp)

theorem c_evaln_evp_aux_0 : eval_prim O (c_evaln) (Nat.pair o 0) = evaln o 0 := by
  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw (config := {occs := .pos [1]}) [c_evaln_aux]
  simp only [c_cov_rec_evp_4, l, c_const_evp]
  simp only [evaln, encodeCode_evaln, decodeCode]
theorem c_evaln_evp_aux_1 : eval_prim O (c_evaln) (Nat.pair o 1) = evaln o 1 := by
  sorry
  -- unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  -- rw (config := {occs := .pos [1]}) [c_evaln_aux]
  -- simp only [c_cov_rec_evp_0, comp₄_evp, eval_prim, l, r, unpair_pair, succ_eq_add_one, zero_add,
  --   c_const_evp, comp₂_evp, c_sub_evp, unpaired, sub_eq, reduceLeDiff, Nat.sub_eq_zero_of_le,
  --   c_mod_evp, zero_mod, c_div2_evp, Nat.zero_div, unpair_zero, Prod.fst_zero, c_l_get_evp,
  --   c_cov_rec_evp_size, zero_lt_one, le_refl, c_cov_rec_evp_2, c_cov_rec_evp_4, Prod.snd_zero,
  --   c_mul2_evp, c_add_evp, add_eq, zero_mul, one_mul, reduceAdd, c_if_eq_te_evp,
  --   OfNat.zero_ne_ofNat, ↓reduceIte, zero_ne_one, OfNat.one_ne_ofNat, list_get_last_append]
  -- simp only [evaln, encodeCode_evaln, decodeCode]
theorem c_evaln_evp_aux_2 : eval_prim O (c_evaln) (Nat.pair o 2) = evaln o 2 := by
  sorry
  -- unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  -- rw (config := {occs := .pos [1]}) [c_evaln_aux]
  -- simp [eval_prim]
  -- simp only [evaln, encodeCode_evaln, decodeCode]
theorem c_evaln_evp_aux_3 : eval_prim O (c_evaln) (Nat.pair o 3) = evaln o 3 := by
  sorry
  -- unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  -- rw (config := {occs := .pos [1]}) [c_evaln_aux]
  -- simp [eval_prim]
  -- simp only [evaln, encodeCode_evaln, decodeCode]
theorem c_evaln_evp_aux_4 : eval_prim O (c_evaln) (Nat.pair o 4) = evaln o 4 := by
  sorry
  -- unfold c_evaln
  -- unfold c_evaln_aux
  -- unfold evaln
  -- simp [encodeCode_evaln, decodeCode]
  -- simp [eval_prim]
set_option maxHeartbeats 3 in
theorem c_evaln_evp_aux_nMod4_0 (h:n%4=0):
  eval_prim O (c_evaln) (Nat.pair o ((n+4)+1))
    =
  let m:=n.div2.div2
  let ml := eval_prim O (c_evaln) (Nat.pair o m.l)
  let mr := eval_prim O (c_evaln) (Nat.pair o m.r)

  2*(2*(Nat.pair (ml) (mr))  )   + 5 := by

  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw (config := {occs := .pos [1]}) [c_evaln_aux]
  simp only [c_cov_rec_evp_3]
  rw [←c_evaln_aux] -- the key step to simplification. otherwise expression blows up
  simp [eval_prim, h]
  have h3 : (n/2/2).l≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have h4 : (n/2/2).r≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  unfold c_evaln_aux
  rw [c_cov_rec_evp_2 h3]
  rw [c_cov_rec_evp_2 h4]
  simp only [l, r, Nat.div2_val] -- removes local defns as well
  rw [mul_comm]
  simp? says simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  rw [mul_comm]
set_option maxHeartbeats 3 in
theorem c_evaln_evp_aux_nMod4_1 (h:n%4=1):
  eval_prim O (c_evaln) (Nat.pair o ((n+4)+1))
    =
  let m:=n.div2.div2
  let ml := eval_prim O (c_evaln) (Nat.pair o m.l)
  let mr := eval_prim O (c_evaln) (Nat.pair o m.r)

  2*(2*(Nat.pair (ml) (mr))  ) +1  + 5 := by

  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw (config := {occs := .pos [1]}) [c_evaln_aux]
  simp only [c_cov_rec_evp_3]
  rw [←c_evaln_aux] -- the key step to simplification. otherwise expression blows up
  simp [eval_prim, h]
  have h3 : (n/2/2).l≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have h4 : (n/2/2).r≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  unfold c_evaln_aux
  rw [c_cov_rec_evp_2 h3]
  rw [c_cov_rec_evp_2 h4]
  simp only [l, r, Nat.div2_val] -- removes local defns as well
  rw [mul_comm]
  simp? says simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  rw [mul_comm]
set_option maxHeartbeats 3 in
theorem c_evaln_evp_aux_nMod4_2 (h:n%4=2):
  eval_prim O (c_evaln) (Nat.pair o ((n+4)+1))
    =
  let m:=n.div2.div2
  let ml := eval_prim O (c_evaln) (Nat.pair o m.l)
  let mr := eval_prim O (c_evaln) (Nat.pair o m.r)

  2*(2*(Nat.pair (ml) (mr)) +1 )   + 5 := by

  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw (config := {occs := .pos [1]}) [c_evaln_aux]
  simp only [c_cov_rec_evp_3]
  rw [←c_evaln_aux] -- the key step to simplification. otherwise expression blows up
  simp [eval_prim, h]
  have h3 : (n/2/2).l≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have h4 : (n/2/2).r≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  unfold c_evaln_aux
  rw [c_cov_rec_evp_2 h3]
  rw [c_cov_rec_evp_2 h4]
  simp only [l, r, Nat.div2_val] -- removes local defns as well
  rw [mul_comm]
  simp? says simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  rw [mul_comm]
set_option maxHeartbeats 3 in
theorem c_evaln_evp_aux_nMod4_3 (h:n%4=3):
  eval_prim O (c_evaln) (Nat.pair o ((n+4)+1))
    =
  let m:=n.div2.div2
  -- let ml := eval_prim O (c_evaln) (Nat.pair o m.l)
  -- let mr := eval_prim O (c_evaln) (Nat.pair o m.r)
  let mprev := eval_prim O (c_evaln) (Nat.pair o m)
  -- 2*(2*(Nat.pair (ml) (mr))  +1)+1   + 5 := by
  2*(2*(mprev)  +1)+1   + 5 := by

  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw (config := {occs := .pos [1]}) [c_evaln_aux]
  simp only [c_cov_rec_evp_3]
  rw [←c_evaln_aux] -- the key step to simplification. otherwise expression blows up
  simp [eval_prim, h]
  
  -- have h3 : (n/2/2).l≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have hmp : (n/2/2)≤n+4 := by exact le_add_right_of_le (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
  -- have h4 : (n/2/2).r≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  unfold c_evaln_aux
  rw [c_cov_rec_evp_2 hmp]
  -- rw [c_cov_rec_evp_2 h4]
  simp only [l, r, Nat.div2_val] -- removes local defns as well

  
  rw [mul_comm]
  simp? says simp only [mul_eq_mul_left_iff, Nat.add_right_cancel_iff, OfNat.ofNat_ne_zero, or_false]
  rw [mul_comm]




theorem nMod4_eq_0 (h0:n.bodd=false) (h1:n.div2.bodd=false) : n%4=0 := by sorry
theorem nMod4_eq_1 (h0:n.bodd=true ) (h1:n.div2.bodd=false) : n%4=1 := by sorry
theorem nMod4_eq_2 (h0:n.bodd=false) (h1:n.div2.bodd=true ) : n%4=2 := by sorry
theorem nMod4_eq_3 (h0:n.bodd=true ) (h1:n.div2.bodd=true ) : n%4=3 := by sorry

-- set_option maxHeartbeats 10000000 in
-- set_option maxHeartbeats 1000000 in
-- set_option maxHeartbeats 3 in
-- set_option maxHeartbeats 3000 in
set_option maxHeartbeats 100000 in
@[simp] theorem c_evaln_evp: eval_prim O (c_evaln) =
  fun inp =>
  let x:=inp.l
  let c:=inp.r.l
  let s:=inp.r.r
  Encodable.encode (evaln O s c x) := by
  funext inp
  let x:=inp.l
  let cs:=inp.r
  let c:=cs.l
  let s:=cs.r
  rw [show inp = Nat.pair x (Nat.pair c s) from by simp [x,cs,c,s]]
  -- rw [show inp = Nat.pair x cs from by simp [x,cs]]
  -- rw [show cs = Nat.pair c s from by simp [c,s]]
  simp only [r, unpair_pair, l] -- simplify the rhs
    -- unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
    -- rw [c_evaln_aux]
    -- simp [eval_prim]

  induction cs using Nat.strong_induction_on with
  | _ cs ih =>
    match hcs:s,c with
    | 0,0=>
      simp [decodeCode, evaln] -- simp rhs

      rw [show Nat.pair 0 0 = 0 from rfl]
      unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
      rw [c_evaln_aux]
      simp only [c_cov_rec_evp_4, l, c_const_evp]
    | 0,n+1 =>
      simp [decodeCode, evaln] -- simp rhs

      have h0' : (Nat.pair (n + 1) 0) >0 := by exact zero_lt_succ (((n + 1) * (n + 1)).add n)
      let k:=(Nat.pair (n + 1) 0)-1
      have h0: k+1=(Nat.pair (n + 1) 0) := by exact Nat.sub_add_cancel h0'

      rw [←h0]

      unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
      rw [c_evaln_aux]
      simp only [c_cov_rec_evp_3]
      unfold k
      -- simp
      -- simp [eval_prim]
      -- simp only [c_cov_rec_evp_4, l, c_const_evp]
      -- simp [decodeCode, evaln]
      rw [←c_evaln_aux]
      simp only [comp₄_evp]
      simp only [eval_prim]
      simp only [c_const_evp]
      simp only [l,r,unpair_pair]
      simp only [succ_eq_add_one]
      rw [h0]
      simp only [unpair_pair]
      rw (config := {occs := .pos [1]}) [c_if_eq_te_evp]
      simp only [l]
      simp only [unpair_pair]
      -- simp only [r]
      unfold r
      rw [unpair_pair]
      simp only []
      simp only [↓reduceIte]
      rw [unpair_pair]
      rw [unpair_pair]
    | s'+1,0 =>
      simp [decodeCode]
      -- #check evaln.eq_2
      -- simp [evaln.eq_2]
      -- exact c_evaln_evp_aux_0
      sorry
    | s'+1,1 => exact c_evaln_evp_aux_1
    | s'+1,2 => exact c_evaln_evp_aux_2
    | s'+1,3 => exact c_evaln_evp_aux_3
    | s'+1,4 => exact c_evaln_evp_aux_4
    | s'+1,n + 5 =>
      let m := n.div2.div2
      have hm : m < n + 5 := by
        simp only [m, Nat.div2_val]
        exact lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)) (Nat.succ_le_succ (Nat.le_add_right _ _))
      have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
      have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm


      rw [show n+5=(n+4)+1 from rfl]


      cases hno:n.bodd with
      | false => cases hn2o:n.div2.bodd with
        | false =>
          have h0: n%4=0 := nMod4_eq_0 hno hn2o
          simp [evaln, encodeCode_evaln, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_evaln_evp_aux_nMod4_0 h0]
          simp
          constructor
          · rw [ih m.l _m1]; simp [evaln, m]
          · rw [ih m.r _m2]; simp [evaln, m]

        | true =>
          have h0: n%4=2 := nMod4_eq_2 hno hn2o
          simp [evaln, encodeCode_evaln, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_evaln_evp_aux_nMod4_2 h0]
          simp
          constructor
          · rw [ih m.l _m1]; simp [evaln, m]
          · rw [ih m.r _m2]; simp [evaln, m]

      | true => cases hn2o:n.div2.bodd with
        | false =>
          have h0: n%4=1 := nMod4_eq_1 hno hn2o
          simp [evaln, encodeCode_evaln, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_evaln_evp_aux_nMod4_1 h0]
          simp
          constructor
          · rw [ih m.l _m1]; simp [evaln, m]
          · rw [ih m.r _m2]; simp [evaln, m]

        | true =>
          have h0: n%4=3 := nMod4_eq_3 hno hn2o
          simp [evaln, encodeCode_evaln, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_evaln_evp_aux_nMod4_3 h0]
          simp
          rw [ih m hm]; simp [evaln, m]
          -- constructor
          -- · rw [ih m.l _m1]; simp [evaln, m]
          -- · rw [ih m.r _m2]; simp [evaln, m]

-- theorem test : n+5=(n+4)+1 := by exact?



@[simp] theorem c_evaln_ev:eval O (c_evaln) = unpaired evaln := by rw [← eval_prim_eq_eval c_evaln_ev_pr]; simp only [c_evaln_evp];
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.evaln:Nat.PrimrecIn O (unpaired evaln) := by rw [← c_evaln_evp]; apply code_prim_prop c_evaln_ev_pr
theorem Nat.Primrec.evaln:Nat.Primrec (unpaired evaln) := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.evaln
end evaln
