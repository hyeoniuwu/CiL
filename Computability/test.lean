import Computability.Constructions

section bind_opt
namespace Nat.RecursiveIn.Code
def c_bind_opt : Code→Code := fun c => c_ifz.comp₂ (c_id) (pair (c_const 0) (succ.comp (c.comp c_pred)))
@[simp] theorem c_bind_opt_ev_pr (hc:code_prim c):code_prim (c_bind_opt c) := by unfold c_bind_opt; repeat (first|assumption|simp|constructor)
-- @[simp] theorem c_bind_opt_evp : eval_prim O (c_bind_opt c) = 
-- @[simp] theorem c_bind_opt_ev:eval O c_bind_opt = unpaired Nat.bind_opt := by rw [← eval_prim_eq_eval c_bind_opt_ev_pr]; simp only [c_bind_opt_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.bind_opt:Nat.PrimrecIn O Nat.bind_opt := by ...
-- theorem Nat.Primrec.bind_opt:Nat.Primrec Nat.bind_opt := by ...
end bind_opt


section le_guard_aux
namespace Nat.RecursiveIn.Code
/-- `eval (c_le_guard_aux k) x = x if x≤k else 0` -/
def c_le_guard_aux (k:Code) := c_if_le_te.comp₄ c_id k succ (c_const 0)
@[simp] theorem c_le_guard_aux_ev_pr (h:code_prim k):code_prim (c_le_guard_aux k) := by unfold c_le_guard_aux; repeat (first|assumption|simp|constructor)
-- @[simp] theorem c_le_guard_aux_evp : eval_prim O (c_le_guard_aux k) = 
-- @[simp] theorem c_le_guard_aux_ev:eval O c_le_guard_aux = unpaired Nat.le_guard_aux := by rw [← eval_prim_eq_eval c_le_guard_aux_ev_pr]; simp only [c_le_guard_aux_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.le_guard_aux:Nat.PrimrecIn O Nat.le_guard_aux := by ...
-- theorem Nat.Primrec.le_guard_aux:Nat.Primrec Nat.le_guard_aux := by ...
end le_guard_aux


section le_guard
namespace Nat.RecursiveIn.Code
def c_le_guard (k:Code) (c:Code) := (c_bind_opt c).comp (c_le_guard_aux (k))
@[simp] theorem c_le_guard_ev_pr (hc:code_prim c) (hk:code_prim k):code_prim (c_le_guard k c) := by unfold c_le_guard; repeat (first|assumption|simp|constructor)
@[simp] theorem c_le_guard_evp:eval_prim O (c_le_guard k c) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (eval_prim O c n) :Option ℕ) := by
  simp only [Option.bind_eq_bind]
  simp [Encodable.encode]
  unfold c_le_guard
  unfold c_bind_opt
  unfold c_le_guard_aux
  simp [eval_prim]
  funext n;
  cases Classical.em (n≤(eval_prim O k n)) with
  | inl h => simp [h]
  | inr h => simp [h, gt_of_not_le h, Option.bind]

@[simp] theorem c_le_guard_ev (hc:code_prim c) (hk:code_prim k):eval O (c_le_guard k c) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (eval_prim O c n) : Option ℕ) := by
  rw [← eval_prim_eq_eval (c_le_guard_ev_pr hc hk)];
  simp only [c_le_guard_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.le_guard:Nat.PrimrecIn O Nat.le_guard := by ...
-- theorem Nat.Primrec.le_guard:Nat.Primrec Nat.le_guard := by ...
end le_guard

section zero_g
namespace Nat.RecursiveIn.Code
def c_zero_g (k:Code) := c_le_guard k zero
@[simp] theorem c_zero_g_ev_pr (hk:code_prim k):code_prim (c_zero_g k) := by exact c_le_guard_ev_pr code_prim.zero hk
@[simp] theorem c_zero_g_evp:eval_prim O (c_zero_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return 0 :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_zero_g_ev (hk:code_prim k):eval O (c_zero_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return 0 : Option ℕ) := by rw [← eval_prim_eq_eval (c_zero_g_ev_pr hk)]; simp only [c_zero_g_evp]
end Nat.RecursiveIn.Code
end zero_g
section succ_g
namespace Nat.RecursiveIn.Code
def c_succ_g (k:Code) := c_le_guard k succ
@[simp] theorem c_succ_g_ev_pr (hk:code_prim k):code_prim (c_succ_g k) := by exact c_le_guard_ev_pr code_prim.succ hk
@[simp] theorem c_succ_g_evp:eval_prim O (c_succ_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (n+1) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_succ_g_ev (hk:code_prim k):eval O (c_succ_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (n+1) : Option ℕ) := by rw [← eval_prim_eq_eval (c_succ_g_ev_pr hk)]; simp only [c_succ_g_evp]
end Nat.RecursiveIn.Code
end succ_g
section left_g
namespace Nat.RecursiveIn.Code
def c_left_g (k:Code) := c_le_guard k left
@[simp] theorem c_left_g_ev_pr (hk:code_prim k):code_prim (c_left_g k) := by exact c_le_guard_ev_pr code_prim.left hk
@[simp] theorem c_left_g_evp:eval_prim O (c_left_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (n.l) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_left_g_ev (hk:code_prim k):eval O (c_left_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (n.l) : Option ℕ) := by rw [← eval_prim_eq_eval (c_left_g_ev_pr hk)]; simp only [c_left_g_evp]
end Nat.RecursiveIn.Code
end left_g
section right_g
namespace Nat.RecursiveIn.Code
def c_right_g (k:Code) := c_le_guard k right
@[simp] theorem c_right_g_ev_pr (hk:code_prim k):code_prim (c_right_g k) := by exact c_le_guard_ev_pr code_prim.right hk
@[simp] theorem c_right_g_evp:eval_prim O (c_right_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (n.r) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_right_g_ev (hk:code_prim k):eval O (c_right_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (n.r) : Option ℕ) := by rw [← eval_prim_eq_eval (c_right_g_ev_pr hk)]; simp only [c_right_g_evp]
end Nat.RecursiveIn.Code
end right_g
section oracle_g
namespace Nat.RecursiveIn.Code
def c_oracle_g (k:Code) := c_le_guard k oracle
@[simp] theorem c_oracle_g_ev_pr (hk:code_prim k):code_prim (c_oracle_g k) := by exact c_le_guard_ev_pr code_prim.oracle hk
@[simp] theorem c_oracle_g_evp:eval_prim O (c_oracle_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (O n) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_oracle_g_ev (hk:code_prim k):eval O (c_oracle_g k) = fun n => Encodable.encode (do guard (n≤(eval_prim O k n)); return (O n) : Option ℕ) := by rw [← eval_prim_eq_eval (c_oracle_g_ev_pr hk)]; simp only [c_oracle_g_evp]
end Nat.RecursiveIn.Code
end oracle_g







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











theorem pair_nonzero_right_pos_aux : ¬ (Nat.pair x (s+1)=0) := by
  rw  [show 0=Nat.pair 0 0 from rfl]
  rw [pair_eq_pair]
  intro h
  have hr := h.right
  contradiction 
theorem pair_nonzero_right_pos : (Nat.pair x (s+1))>0 := by
  exact zero_lt_of_ne_zero pair_nonzero_right_pos_aux







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

  c_if_eq_te.comp₄ code  (c_const 0) ((c_zero_g s).comp x)   $
  c_if_eq_te.comp₄ code  (c_const 1) ((c_succ_g s).comp x)   $
  c_if_eq_te.comp₄ code  (c_const 2) ((c_left_g s).comp x)   $
  c_if_eq_te.comp₄ code  (c_const 3) ((c_right_g s).comp x)  $
  c_if_eq_te.comp₄ code  (c_const 4) ((c_oracle_g s).comp x) $
  c_if_eq_te.comp₄ nMod4 (c_const 0) (pair pcl pcr)          $
  c_if_eq_te.comp₄ nMod4 (c_const 1) (comp pcl pcr)          $
  c_if_eq_te.comp₄ nMod4 (c_const 2) (prec pcl pcr)          $
                                      rfind' pc
def c_evaln := c_l_get_last.comp c_evaln_aux

-- set_option maxRecDepth 5000 in
set_option maxHeartbeats 3 in
@[simp] theorem c_evaln_ev_pr:code_prim (c_evaln) := by
  unfold c_evaln;
  repeat (first|assumption|simp|constructor)



theorem c_evaln_evp_aux_0_0 : eval_prim O (c_evaln) (Nat.pair x (Nat.pair 0 0)) = Encodable.encode (evaln O 0 (0:ℕ) x) := by
  simp [decodeCode, evaln] -- simp rhs
  rw [show Nat.pair 0 0 = 0 from rfl]
  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw [c_evaln_aux]
  simp only [c_cov_rec_evp_4, l, c_const_evp]
theorem c_evaln_evp_aux_0_np1 : eval_prim O (c_evaln) (Nat.pair x (Nat.pair (n+1) 0)) = Encodable.encode (evaln O 0 (n+1:ℕ) x) := by
  simp [decodeCode, evaln] -- simp rhs

  have h0' : (Nat.pair (n + 1) 0)>0 := by exact zero_lt_succ (((n + 1) * (n + 1)).add n)
  let k:=(Nat.pair (n + 1) 0)-1
  have h0: k+1=(Nat.pair (n + 1) 0) := by exact Nat.sub_add_cancel h0'
  rw [←h0]

  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw [c_evaln_aux]
  simp only [c_cov_rec_evp_3]
  unfold k
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
  unfold r
  rw [unpair_pair]
  simp only []
  simp only [↓reduceIte]
  rw [unpair_pair]
  rw [unpair_pair]
theorem c_evaln_evp_aux_0 : eval_prim O (c_evaln) (Nat.pair x (Nat.pair 0 (s+1))) = Encodable.encode (evaln O (s+1) (0:ℕ) x) := by
  simp [decodeCode, evaln] -- simp rhs

  let k:=(Nat.pair 0 (s+1))-1
  have h0: k+1=(Nat.pair 0 (s+1)) := by exact Nat.sub_add_cancel pair_nonzero_right_pos
  rw [←h0]

  unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  rw [c_evaln_aux]
  simp only [c_cov_rec_evp_3]
  unfold k
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
  unfold r
  rw [unpair_pair]
  simp only [add_one_ne_zero]
  simp only [↓reduceIte]
  simp only [unpair_pair]

  rw (config := {occs := .pos [1]}) [c_if_eq_te_evp]
  simp only [l]
  simp only [unpair_pair]
  unfold r
  rw [unpair_pair]
  simp only [add_one_ne_zero]
  simp only [↓reduceIte]
  simp only [unpair_pair]

  simp

  sorry
  -- have h0' : (Nat.pair (n + 1) 0) >0 := by exact zero_lt_succ (((n + 1) * (n + 1)).add n)
  -- let k:=(Nat.pair (n + 1) 0)-1
  -- have h0: k+1=(Nat.pair (n + 1) 0) := by exact Nat.sub_add_cancel h0'

  -- rw [←h0]

  -- unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  -- rw [c_evaln_aux]
  -- simp only [c_cov_rec_evp_3]
  -- unfold k
  -- -- simp
  -- -- simp [eval_prim]
  -- -- simp only [c_cov_rec_evp_4, l, c_const_evp]
  -- -- simp [decodeCode, evaln]
  -- rw [←c_evaln_aux]
  -- simp only [comp₄_evp]
  -- simp only [eval_prim]
  -- simp only [c_const_evp]
  -- simp only [l,r,unpair_pair]
  -- simp only [succ_eq_add_one]
  -- rw [h0]
  -- simp only [unpair_pair]
  -- rw (config := {occs := .pos [1]}) [c_if_eq_te_evp]
  -- simp only [l]
  -- simp only [unpair_pair]
  -- -- simp only [r]
  -- unfold r
  -- rw [unpair_pair]
  -- simp only []
  -- simp only [↓reduceIte]
  -- rw [unpair_pair]
  -- rw [unpair_pair]

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
    | 0,0   => exact c_evaln_evp_aux_0_0
    | 0,n+1 => exact c_evaln_evp_aux_0_np1
    | s'+1,0 => exact c_evaln_evp_aux_0
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
