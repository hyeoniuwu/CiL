import Computability.Constructions

set_option profiler true

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


-- section le_guard_aux
-- namespace Nat.RecursiveIn.Code
-- /-- `eval (c_le_guard_aux k) x = x if x≤k else 0` -/
-- def c_le_guard_aux (k:Code) := c_if_le_te.comp₄ c_id k succ (c_const 0)
-- @[simp] theorem c_le_guard_aux_ev_pr (h:code_prim k):code_prim (c_le_guard_aux k) := by unfold c_le_guard_aux; repeat (first|assumption|simp|constructor)
-- -- @[simp] theorem c_le_guard_aux_evp : eval_prim O (c_le_guard_aux k) =
-- -- @[simp] theorem c_le_guard_aux_ev:eval O c_le_guard_aux = unpaired Nat.le_guard_aux := by rw [← eval_prim_eq_eval c_le_guard_aux_ev_pr]; simp only [c_le_guard_aux_evp]
-- end Nat.RecursiveIn.Code
-- -- theorem Nat.PrimrecIn.le_guard_aux:Nat.PrimrecIn O Nat.le_guard_aux := by ...
-- -- theorem Nat.Primrec.le_guard_aux:Nat.Primrec Nat.le_guard_aux := by ...
-- end le_guard_aux


section le_guard
namespace Nat.RecursiveIn.Code
/-- `eval (c_le_guard c) (s,x) = smth like eval c x if x≤s else 0 (not quite)` -/
def c_le_guard  (c:Code) := (c_bind_opt (c.comp right)).comp (c_if_le_te.comp₄ right left succ (c_const 0))
@[simp] theorem c_le_guard_ev_pr (hc:code_prim c) : code_prim (c_le_guard c) := by unfold c_le_guard; repeat (first|assumption|simp|constructor)
@[simp] theorem c_le_guard_evp:eval_prim O (c_le_guard c) = fun n => Encodable.encode (do guard (n.r≤n.l); return (eval_prim O c n.r) :Option ℕ) := by
  simp only [Option.bind_eq_bind]
  simp [Encodable.encode]
  unfold c_le_guard
  unfold c_bind_opt
  -- unfold c_le_guard_aux
  simp [eval_prim]
  funext n;
  cases Classical.em (n.r≤n.l) with
  | inl h => simp [h]
  | inr h => simp [h, gt_of_not_le h, Option.bind]

@[simp] theorem c_le_guard_ev (hc:code_prim c):eval O (c_le_guard c) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); return (eval_prim O c n.r) : Option ℕ) := by
  rw [← eval_prim_eq_eval (c_le_guard_ev_pr hc)];
  simp only [c_le_guard_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.le_guard:Nat.PrimrecIn O Nat.le_guard := by ...
-- theorem Nat.Primrec.le_guard:Nat.Primrec Nat.le_guard := by ...
end le_guard

section zero_g
namespace Nat.RecursiveIn.Code
def c_zero_g := c_le_guard zero
@[simp] theorem c_zero_g_ev_pr :code_prim (c_zero_g) := by exact c_le_guard_ev_pr code_prim.zero
@[simp] theorem c_zero_g_evp:eval_prim O (c_zero_g) = fun n => Encodable.encode (do guard (n.r≤n.l); return 0 :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_zero_g_ev :eval O (c_zero_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); return 0 : Option ℕ) := by rw [← eval_prim_eq_eval (c_zero_g_ev_pr)]; simp only [c_zero_g_evp]
end Nat.RecursiveIn.Code
end zero_g
section succ_g
namespace Nat.RecursiveIn.Code
def c_succ_g := c_le_guard succ
@[simp] theorem c_succ_g_ev_pr :code_prim (c_succ_g) := by exact c_le_guard_ev_pr code_prim.succ
@[simp] theorem c_succ_g_evp:eval_prim O (c_succ_g) = fun n => Encodable.encode (do guard (n.r≤n.l); return (n.r+1) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_succ_g_ev :eval O (c_succ_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); return (n.r+1) : Option ℕ) := by rw [← eval_prim_eq_eval (c_succ_g_ev_pr)]; simp only [c_succ_g_evp]
end Nat.RecursiveIn.Code
end succ_g
section left_g
namespace Nat.RecursiveIn.Code
def c_left_g := c_le_guard left
@[simp] theorem c_left_g_ev_pr :code_prim (c_left_g) := by exact c_le_guard_ev_pr code_prim.left
@[simp] theorem c_left_g_evp:eval_prim O (c_left_g) = fun n => Encodable.encode (do guard (n.r≤n.l); return (n.r.l) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_left_g_ev :eval O (c_left_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); return (n.r.l) : Option ℕ) := by rw [← eval_prim_eq_eval (c_left_g_ev_pr)]; simp only [c_left_g_evp]
end Nat.RecursiveIn.Code
end left_g
section right_g
namespace Nat.RecursiveIn.Code
def c_right_g := c_le_guard right
@[simp] theorem c_right_g_ev_pr :code_prim (c_right_g) := by exact c_le_guard_ev_pr code_prim.right
@[simp] theorem c_right_g_evp:eval_prim O (c_right_g) = fun n => Encodable.encode (do guard (n.r≤n.l); return (n.r.r) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_right_g_ev :eval O (c_right_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); return (n.r.r) : Option ℕ) := by rw [← eval_prim_eq_eval (c_right_g_ev_pr)]; simp only [c_right_g_evp]
end Nat.RecursiveIn.Code
end right_g
section oracle_g
namespace Nat.RecursiveIn.Code
def c_oracle_g := c_le_guard oracle
@[simp] theorem c_oracle_g_ev_pr :code_prim (c_oracle_g) := by exact c_le_guard_ev_pr code_prim.oracle
@[simp] theorem c_oracle_g_evp:eval_prim O (c_oracle_g) = fun n => Encodable.encode (do guard (n.r≤n.l); return (O n.r) :Option ℕ) := by exact c_le_guard_evp
@[simp] theorem c_oracle_g_ev :eval O (c_oracle_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); return (O n.r) : Option ℕ) := by rw [← eval_prim_eq_eval (c_oracle_g_ev_pr)]; simp only [c_oracle_g_evp]
end Nat.RecursiveIn.Code
end oracle_g



section bind_opt
namespace Nat.RecursiveIn.Code
-- if either left or right is zero, then 0 else the ting.
def c_bind_opt2 : (Code→Code→Code)→Code :=
  fun cp =>
    c_ifz.comp₂ (c_le_guard cf) $ pair (c_const 0) $
    c_ifz.comp₂ (c_le_guard cg) $ pair (c_const 0) $
    succ.comp (cf (pred.comp c_le_guard cf) (c_le_guard cg))
-- @[simp] theorem c_bind_opt2_ev_pr (hc:code_prim cf):code_prim (c_bind_opt2 cf) := by unfold c_bind_opt2; repeat (first|assumption|simp|constructor)
-- @[simp] theorem c_bind_opt2_evp : eval_prim O (c_bind_opt2 c) =
-- @[simp] theorem c_bind_opt2_ev:eval O c_bind_opt2 = unpaired Nat.bind_opt := by rw [← eval_prim_eq_eval c_bind_opt2_ev_pr]; simp only [c_bind_opt2_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.bind_opt:Nat.PrimrecIn O Nat.bind_opt := by ...
-- theorem Nat.Primrec.bind_opt:Nat.Primrec Nat.bind_opt := by ...
end bind_opt



def c_le_guard  (c:Code) := (c_bind_opt (c.comp right)).comp (c_if_le_te.comp₄ right left succ (c_const 0))
section pair_g
namespace Nat.RecursiveIn.Code
/-
the plan.
pair the two inputs normally,
then call
if cf or cg evaluates to 0, we want the whole thing to be 0.
-/
-- takes inputs of the form: (s,x)
-- first we want to check that x≤s.

/-
if everything goes well we want to return

-/
--
-- def c_pair_g : Code→Code→Code := fun cf cg => (c_bind_opt2 pair).comp (pair cf cg)
def c_pair_g : Code→Code→Code := fun cf cg =>
  let x         := left
  let code_s    := succ.comp (left.comp right)
  let code      := left.comp code_s
  let s         := right.comp code_s
  let sM1         := c_pred.comp s

  c_if_le_te.comp₄ x sM1

  (
    c_ifz.comp₂ ( cf.comp c_id) $ pair (c_const 0) $
    c_ifz.comp₂ ( cg.comp c_id) $ pair (c_const 0) $
    succ.comp (pair (c_pred.comp ( cf.comp c_id)) (c_pred.comp ( cg.comp c_id)))
  )

  (c_const 0)
-- pair (c_le_guard cf) (c_le_guard cg)
-- @[simp] theorem c_pair_g_ev_pr :code_prim (c_pair_g) := by exact c_le_guard_ev_pr code_prim.zero
-- @[simp] theorem c_pair_g_evp:eval_prim O (c_pair_g cf cg) = fun n => Encodable.encode (do guard (n.r≤n.l); Nat.pair <$> evaln O (k + 1) cf n <*> evaln O (k + 1) cg n :Option ℕ) := by
-- @[simp] theorem c_pair_g_evp:eval_prim O (c_pair_g cf cg) = fun n => Encodable.encode (do guard (n.r≤n.l); Nat.pair <$> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cf n.r)) <*> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cg n.r)) :Option ℕ) := by
-- k=smth like Nat.pair code (s+1)
-- @[simp] theorem c_pair_g_evp:eval_prim O (c_pair_g cf cg) (Nat.pair x (Nat.pair (Nat.pair code (s+1)) hist))= Encodable.encode (do guard (x≤s); Nat.pair <$> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cf (Nat.pair x (Nat.pair (Nat.pair code (s+1)) hist)))) <*> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cg (Nat.pair x (Nat.pair (Nat.pair code (s+1)) hist)))) :Option ℕ) := by
/-
inp = (x, ((code,s)-1, hist))
-/
@[simp] theorem c_pair_g_evp:eval_prim O (c_pair_g cf cg) inp =
  let x:=inp.l
  let succ_code_s := inp.r.l+1
  let s:=succ_code_s.r
  let sM1:=s-1
  Encodable.encode (do guard (x≤sM1); Nat.pair <$> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cf inp)) <*> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cg inp)) :Option ℕ) := by
  -- simp
  -- simp [Option.map]

  
  lift_lets
  extract_lets
  expose_names

  simp only [Option.bind_eq_bind]
  simp [Encodable.encode]
  simp [Seq.seq]

  unfold c_pair_g
  lift_lets
  extract_lets
  expose_names
  -- unfold c_bind_opt2
  simp [eval_prim]
  -- funext n
  have h0 : (Denumerable.ofNat (Option ℕ) 0) = Option.none := by exact rfl
  have h1 {x} (h2:¬x=0) : x=x-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h2)
  have h2 {x} (h3:¬x=0) : (Denumerable.ofNat (Option ℕ) x) = Option.some (x-1) := by
    rw (config := {occs := .pos [1]}) [h1 h3]
    exact rfl
  have hx : eval_prim O x_1 inp = x := by simp [x_1, x]
  have hs : eval_prim O s_1 inp = s := by
    simp [s_1]
    simp [code_s]
    simp [s]
    simp [succ_code_s]
  have hsM1 : eval_prim O sM1_1 inp = sM1 := by
    simp [sM1_1, sM1]
    simp [hs]
  

  cases Classical.em (x≤sM1) with
  | inl hl =>
    simp [hl]
    cases Classical.em ((eval_prim O cf inp)=0) with
    | inl hll => simp [hll, h0]
    | inr hlr =>
      simp [hlr, h2 hlr]
      cases Classical.em ((eval_prim O cg inp)=0) with
      | inl hlrl => simp [hlrl, h0]
      | inr hlrr =>
        simp [hlrr, h2 hlrr]
        simp [hx,hsM1]
        simp [hl]

  | inr hr =>
    simp [hr]
    cases Classical.em ((eval_prim O cf inp)=0) with
    | inl hrl => simp [hrl, h0]
    | inr hrr =>
      simp [hrr, h2 hrr]
      cases Classical.em ((eval_prim O cg inp)=0) with
      | inl hrrl => simp [hrrl, h0]
      | inr hrrr =>
        simp [hrrr, h2 hrrr]
        simp [Option.bind]
        simp [hx,hsM1]
        apply gt_of_not_le hr


-- @[simp] theorem c_pair_g_ev :eval O (c_pair_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); Nat.pair <$> evaln O (k + 1) cf n <*> evaln O (k + 1) cg n : Option ℕ) := by rw [← eval_prim_eq_eval (c_pair_g_ev_pr)]; simp only [c_pair_g_evp]
end Nat.RecursiveIn.Code
end pair_g





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
@[simp] theorem pair_nonzero_right_pos : (Nat.pair x (s+1))>0 := by
  exact zero_lt_of_ne_zero pair_nonzero_right_pos_aux







-- /-- `eval c_evaln_aux (x,(code,s))` = `evaln s code x` -/
/-- `eval c_evaln_aux (anything,(x,(code,s)))` = `evaln s code x` -/
def c_evaln_aux :=
  let x_code_s  := (succ.comp (left.comp right))
  let x         := left.comp x_code_s
  -- let code_s    := right.comp right
  let code      := left.comp (right.comp x_code_s)
  let s         := right.comp (right.comp x_code_s)
  let sM1       := c_pred.comp s
  let comp_hist := right.comp right
  let n         := c_sub.comp₂ code (c_const 5)
  let m         := c_div2.comp $ c_div2.comp n

  let pcl := c_l_get.comp₂ comp_hist (pair (left.comp m)  s) -- the previous computation corresponding to evaluating code m.l for s-1 steps.
  let pcr := c_l_get.comp₂ comp_hist (pair (right.comp m) s)
  let pc  := c_l_get.comp₂ comp_hist (pair m              s)
  let nMod4     := c_mod.comp₂ n (c_const 4)

  c_cov_rec

  (c_const 0) $

  c_if_eq_te.comp₄ s     (c_const 0) (c_const 0)              $ -- if s=0, then diverge
  c_if_eq_te.comp₄ code  (c_const 0) (c_zero_g.comp₂   sM1 x) $
  c_if_eq_te.comp₄ code  (c_const 1) (c_succ_g.comp₂   sM1 x) $
  c_if_eq_te.comp₄ code  (c_const 2) (c_left_g.comp₂   sM1 x) $
  c_if_eq_te.comp₄ code  (c_const 3) (c_right_g.comp₂  sM1 x) $
  c_if_eq_te.comp₄ code  (c_const 4) (c_oracle_g.comp₂ sM1 x) $
  -- c_if_eq_te.comp₄ nMod4 (c_const 0) ((c_pair_g pcl pcr).comp₂ sM1 x)  $
  c_if_eq_te.comp₄ nMod4 (c_const 0) (c_pair_g pcl pcr)  $
  c_if_eq_te.comp₄ nMod4 (c_const 1) (comp pcl pcr)           $
  c_if_eq_te.comp₄ nMod4 (c_const 2) (prec pcl pcr)           $
                                      rfind' pc
def c_evaln := c_l_get_last.comp (c_evaln_aux.comp (pair (c_const 0) c_id))



-- set_option maxRecDepth 5000 in
set_option maxHeartbeats 3 in
@[simp] theorem c_evaln_ev_pr:code_prim (c_evaln) := by
  unfold c_evaln;
  repeat (first|assumption|simp|constructor)


--asd

theorem pair_r_gt0 {x} : x>0→(Nat.pair y x)>0 := by
  contrapose
  simp
  intro h
  rw [show x=(Nat.pair y x).unpair.2 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
theorem pair_l_gt0 {x} : x>0→(Nat.pair x y)>0 := by
  contrapose
  simp
  intro h
  rw [show x=(Nat.pair x y).unpair.1 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]

theorem c_evaln_evp_aux_0_0_0 : eval_prim O (c_evaln) (Nat.pair 0 (Nat.pair 0 0)) = Encodable.encode (evaln O 0 (0:ℕ) 0) := by
  simp [decodeCode, evaln] -- simp rhs
  rw [show Nat.pair 0 0 = 0 from rfl]
  -- unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
  -- rw [c_evaln_aux]
  -- unfold c_evaln_aux

  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names

  simp
  rw [show Nat.pair 0 0 = 0 from rfl]
  simp

theorem c_evaln_evp_aux_x_0_0 : eval_prim O (c_evaln) (Nat.pair (x+1) (Nat.pair 0 0)) = Encodable.encode (evaln O 0 (0:ℕ) (x+1)) := by

  let k:=(Nat.pair (x+1) (Nat.pair 0 0))-1
  have kP1_gt_0 : Nat.pair (x+1) (Nat.pair 0 0)>0 := by
    apply pair_l_gt0
    exact zero_lt_succ x
  have h0: k+1=(Nat.pair (x+1) (Nat.pair 0 0)) := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←h0]

  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names
  have hs {anything hist} : eval_prim O s (Nat.pair anything (Nat.pair k hist)) = 0 := by
    simp [s]
    simp [x_code_s]
    simp [h0]
  -- have hsM1 {anything hist} : eval_prim O sM1 (Nat.pair anything (Nat.pair k hist)) = s := by
  --   simp [sM1]
  --   simp [hs]
  -- have hcode {anything hist} : eval_prim O code_1 (Nat.pair anything (Nat.pair k hist)) = code := by
  --   simp [code_1]
  --   simp [x_code_s]
  --   simp [h0]
  simp [hs]
  simp [decodeCode, evaln] -- simp rhs

  
theorem c_evaln_evp_aux_0_np1 : eval_prim O (c_evaln) (Nat.pair x (Nat.pair (n+1) 0)) = Encodable.encode (evaln O 0 (n+1:ℕ) x) := by
  simp [decodeCode, evaln] -- simp rhs


  have h0' : (Nat.pair x (Nat.pair (n + 1) 0))>0 := by
    apply pair_r_gt0
    apply pair_l_gt0
    exact zero_lt_succ n
  let k:=(Nat.pair x (Nat.pair (n + 1) 0))-1
  have h0: k+1=(Nat.pair x (Nat.pair (n + 1) 0)) := by exact Nat.sub_add_cancel h0'


  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names

  have hs {anything hist} : eval_prim O s (Nat.pair anything (Nat.pair k hist)) = 0 := by
    simp [s]
    simp [x_code_s]
    simp [h0]

  simp
  rw [←h0]
  simp [hs]



theorem c_evaln_evp_aux (hcode_val:code≤4) : eval_prim O (c_evaln) (Nat.pair x (Nat.pair code (s+1))) = Encodable.encode (evaln O (s+1) (code:ℕ) x) := by
  -- simp [decodeCode, evaln] -- simp rhs

  let k:=(Nat.pair x (Nat.pair code (s+1)))-1
  have kP1_gt_0 : Nat.pair x (Nat.pair code (s+1))>0 := by
    apply pair_r_gt0
    apply pair_r_gt0
    exact zero_lt_succ s
  have h0: k+1=(Nat.pair x (Nat.pair code (s+1))) := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←h0]

  unfold c_evaln; unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names

  have hx {anything hist} : eval_prim O x_1 (Nat.pair anything (Nat.pair k hist)) = x := by
    simp [x_1]
    simp [x_code_s]
    simp [h0]
  have hs {anything hist} : eval_prim O s_1 (Nat.pair anything (Nat.pair k hist)) = s+1 := by
    simp [s_1]
    simp [x_code_s]
    simp [h0]
  have hsM1 {anything hist} : eval_prim O sM1 (Nat.pair anything (Nat.pair k hist)) = s := by
    simp [sM1]
    simp [hs]
  have hcode {anything hist} : eval_prim O code_1 (Nat.pair anything (Nat.pair k hist)) = code := by
    simp [code_1]
    simp [x_code_s]
    simp [h0]
  match code with
  | 0 => simp [hs, hcode, hx, hsM1, decodeCode, evaln]
  | 1 => simp [hs, hcode, hx, hsM1, decodeCode, evaln]
  | 2 => simp [hs, hcode, hx, hsM1, decodeCode, evaln]
  | 3 => simp [hs, hcode, hx, hsM1, decodeCode, evaln]
  | 4 => simp [hs, hcode, hx, hsM1, decodeCode, evaln]
  | n+5 => simp at hcode_val


theorem c_evaln_evp_aux_nMod4_0 :
  -- eval_prim O (c_evaln) (Nat.pair o ((n+4)+1))
  eval_prim O (c_evaln) (Nat.pair x (Nat.pair ((n+4)+1) (s+1)))
    =
  let m := n.div2.div2
  let pcl := eval_prim O (c_evaln) (Nat.pair x (Nat.pair m.l (s+1)))
  let pcr := eval_prim O (c_evaln) (Nat.pair x (Nat.pair m.r (s+1)))

       if n%4=0 then Encodable.encode (do guard (x ≤ s); Nat.pair<$>(@Denumerable.ofNat (Option ℕ)) pcl<*>(@Denumerable.ofNat (Option ℕ)) pcr)
  else if n%4=1 then Encodable.encode (do guard (x ≤ s); let intermediate ← ((@Denumerable.ofNat (Option ℕ)) pcr); evaln O (s + 1) cf intermediate)
  else if n%4=2 then Encodable.encode (do guard (x ≤ s); Nat.pair<$>(@Denumerable.ofNat (Option ℕ)) pcl<*>(@Denumerable.ofNat (Option ℕ)) pcr)
  else if n%4=3 then Encodable.encode (do guard (x ≤ s); Nat.pair<$>(@Denumerable.ofNat (Option ℕ)) pcl<*>(@Denumerable.ofNat (Option ℕ)) pcr)
  else 0

  
    := by

  -- simp [decodeCode, evaln] -- simp rhs

  let k:=(Nat.pair ((n+4)+1) (s+1))-1
  have hk: k+1=(Nat.pair ((n+4)+1) (s+1)) := by exact Nat.sub_add_cancel pair_nonzero_right_pos
  rw [←hk]

  lift_lets
  extract_lets
  expose_names

  unfold c_evaln;
  unfold c_evaln_aux

  lift_lets
  extract_lets
  expose_names



  -- unfold c_evaln; unfold c_evaln_aux
  -- simp
  -- rw [h0]
  -- simp

  have hx : eval_prim O x_1 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = x := by
    simp [x_1]
  have hs : eval_prim O s_1 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = s+1 := by
    simp [s_1]
    simp [code_s]
    simp [hk]
  have hsM1 : eval_prim O sM1 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = s := by
    simp [sM1]
    simp [hs]
  have hcode : eval_prim O code (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = (n+4)+1 := by
    simp [code]
    simp [code_s]
    simp [hk]
  have hn : eval_prim O n_1 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = n := by
    simp [n_1]
    simp [hcode]
  have hm : eval_prim O m_1 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = m := by
    simp [m_1]
    simp [hn]
    simp [m]
    simp [div2_val]
  have hnMod4 : eval_prim O nMod4 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = n%4 := by
    simp [nMod4]
    simp [hn]

    
  have bounds_left_aux_1 : m.l<n+4+1 := by
    apply lt_add_one_of_le
    unfold m
    simp [div2_val]
    exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have bounds_aux : Nat.pair (n + 4 + 1) (s + 1) ≥ 1 := by
    rw [←hk]
    exact le_add_left 1 k
  have bounds_left_aux_2 : Nat.pair m.l (s + 1) < k+1 := by
    unfold k
    simp [Nat.sub_add_cancel bounds_aux]
    exact pair_lt_pair_left (s+1) bounds_left_aux_1
  have bounds_left : Nat.pair m.l (s + 1) ≤ k := by
    apply le_of_lt_succ bounds_left_aux_2

  have bounds_right_aux_1 : m.r<n+4+1 := by
    apply lt_add_one_of_le
    unfold m
    simp [div2_val]
    exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have bounds_right_aux_2 : Nat.pair m.r (s + 1) < k+1 := by
    unfold k
    simp [Nat.sub_add_cancel bounds_aux]
    exact pair_lt_pair_left (s+1) bounds_right_aux_1
  have bounds_right : Nat.pair m.r (s + 1) ≤ k := by
    apply le_of_lt_succ bounds_right_aux_2
      
  have hpcl : eval_prim O pcl_1 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = pcl := by
    simp [pcl_1]
    simp [comp_hist]
    unfold pcl
    simp [hm, hs]

    unfold c_evaln
    unfold c_evaln_aux
    lift_lets
    rw [c_cov_rec_evp_2 bounds_left]
    simp
  have hpcr : eval_prim O pcr_1 (Nat.pair x (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair x k)))) = pcr := by
    simp [pcr_1]
    simp [comp_hist]
    unfold pcr
    simp [hm, hs]

    unfold c_evaln
    unfold c_evaln_aux
    lift_lets
    rw [c_cov_rec_evp_2 bounds_right]
    simp



  have stupidrewrite : (eval_prim O
                ((c_const 0).c_cov_rec
                  (c_if_eq_te.comp
                    ((s_1.pair (c_const 0)).pair
                      ((c_const 0).pair
                        (c_if_eq_te.comp
                          ((code.pair (c_const 0)).pair
                            ((c_zero_g.comp (sM1.pair x_1)).pair
                              (c_if_eq_te.comp
                                ((code.pair (c_const 1)).pair
                                  ((c_succ_g.comp (sM1.pair x_1)).pair
                                    (c_if_eq_te.comp
                                      ((code.pair (c_const 2)).pair
                                        ((c_left_g.comp (sM1.pair x_1)).pair
                                          (c_if_eq_te.comp
                                            ((code.pair (c_const 3)).pair
                                              ((c_right_g.comp (sM1.pair x_1)).pair
                                                (c_if_eq_te.comp
                                                  ((code.pair (c_const 4)).pair
                                                    ((c_oracle_g.comp (sM1.pair x_1)).pair
                                                      (c_if_eq_te.comp
                                                        ((nMod4.pair (c_const 0)).pair
                                                          ((pcl_1.c_pair_g pcr_1).pair
                                                            (c_if_eq_te.comp
                                                              ((nMod4.pair (c_const 1)).pair
                                                                ((pcl_1.comp pcr_1).pair
                                                                  (c_if_eq_te.comp
                                                                    ((nMod4.pair (c_const 2)).pair
                                                                      ((pcl_1.prec pcr_1).pair
                                                                        pc.rfind'))))))))))))))))))))))))))))
                (Nat.pair x k))
                =eval_prim O c_evaln_aux (Nat.pair x k) := rfl


  simp [hs, hcode, hnMod4, hx, hsM1, stupidrewrite]

  match h:n%4 with
  | 0 => simp [hpcl, hpcr, hk]
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | x+4 =>
    have contrad : n%4<4 := by
      apply Nat.mod_lt
      decide
    rw [h] at contrad
    rw [show x.succ.succ.succ.succ=x+4 from rfl] at contrad
    simp at contrad


  simp [h]
  simp [hpcl, hpcr]
  simp [hk]



@[simp] theorem c_evaln_evp: eval_prim O (c_evaln) (Nat.pair x (Nat.pair code s)) =
  Encodable.encode (evaln O s code x) := by
  -- funext inp
  -- let x:=inp.l
  let code_s:=Nat.pair code s
  rw [show Nat.pair code s = code_s by rfl]
  rw [show code = code_s.l by simp [code_s]]
  rw [show s = code_s.r by simp [code_s]]
  -- let c:=cs.lcode
  -- let s:=cs.r
  -- rw [show inp = Nat.pair x (Nat.pair c s) from by simp [x,cs,c,s]]
  -- rw [show inp = Nat.pair x cs from by simp [x,cs]]
  -- rw [show cs = Nat.pair c s from by simp [c,s]]
  -- simp only [r, unpair_pair, l] -- simplify the rhs
    -- unfold c_evaln; simp only [eval_prim, c_l_get_last_evp]
    -- rw [c_evaln_aux]
    -- simp [eval_prim]

  induction code_s using Nat.strong_induction_on with
  | _ code_s ih =>

    let code:=code_s.l
    let s:=code_s.r
    rw [show code_s = Nat.pair code s from by simp [code,s]] 
    simp only [pair_r, pair_l]


    match hs_val:s,hcode_val:code with
    | 0,    0   => exact c_evaln_evp_aux_0_0
    | 0,    n+1 => exact c_evaln_evp_aux_0_np1
    | sM1+1, 0   => apply c_evaln_evp_aux; decide
    | sM1+1, 1   => apply c_evaln_evp_aux; decide
    | sM1+1, 2   => apply c_evaln_evp_aux; decide
    | sM1+1, 3   => apply c_evaln_evp_aux; decide
    | sM1+1, 4   => apply c_evaln_evp_aux; decide
    | sM1+1, n+5 =>
      let m := n.div2.div2
      have hm : m < n + 5 := by
        simp only [m, Nat.div2_val]
        exact lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)) (Nat.succ_le_succ (Nat.le_add_right _ _))
      have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
      have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm


      rw [show n.succ.succ.succ.succ.succ=n+5 by rfl] at hcode_val
      rw [succ_eq_add_one] at hs_val

      have h0 : code_s=Nat.pair (n+5) (sM1+1) := by
        
        rw [←hs_val]
        rw [←hcode_val]
        simp only [code,s]
        simp only [pair_lr]

      let pcl := Nat.pair m.l (sM1+1)
      have pcl_lt_cs : pcl < cs := by
        unfold pcl; rw [h0]
        exact pair_lt_pair_left (sM1 + 1) _m1
      let pcr := Nat.pair m.r (sM1+1)
      have pcr_lt_cs : pcr < cs := by
        unfold pcr; rw [h0]
        exact pair_lt_pair_left (sM1 + 1) _m2

      stop
      rw [show n+5=(n+4)+1 from rfl]


      cases hno:n.bodd with
      | false => cases hn2o:n.div2.bodd with
        | false =>
          have h0: n%4=0 := nMod4_eq_0 hno hn2o
          -- simplify the rhs
          -- simp
          simp [decodeCode]
          simp [evaln,hno, hn2o]


          rw [c_evaln_evp_aux_nMod4_0 h0]


          simp only []
          rw [ih pcr pcr_lt_cs];
          rw [ih pcl pcl_lt_cs];

          simp only [pcl, pcr, m]
          simp

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
