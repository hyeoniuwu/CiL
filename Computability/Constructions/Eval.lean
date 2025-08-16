-- import Computability.Constructions.Basic
import Computability.Constructions.CovRec

open List

-- set_option profiler true

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

-- input is of the form (s,x)
def c_pair_g : Code→Code→Code := fun cf cg =>
  let x         := right
  let s         := left

  c_if_le_te.comp₄ x s

  (
    c_ifz.comp₃ (cf.comp c_id) (c_const 0) $
    c_ifz.comp₃ (cg.comp c_id) (c_const 0) $
    succ.comp (pair (c_pred.comp (cf.comp c_id)) (c_pred.comp (cg.comp c_id)))
  )

  (c_const 0)
@[simp] theorem c_pair_g_ev_pr (hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_pair_g cf cg) := by
  unfold c_pair_g
  repeat (first|assumption|simp|constructor)
@[simp] theorem c_pair_g_evp:eval_prim O (c_pair_g cf cg) inp =
  let x         := inp.r
  let s         := inp.l
  Encodable.encode (do guard (x≤s); Nat.pair <$> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cf inp)) <*> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cg inp))) := by

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
  simp [eval_prim]
  have h0 : (Denumerable.ofNat (Option ℕ) 0) = Option.none := by exact rfl
  have h1 {x} (h2:¬x=0) : x=x-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h2)
  have h2 {x} (h3:¬x=0) : (Denumerable.ofNat (Option ℕ) x) = Option.some (x-1) := by
    rw (config := {occs := .pos [1]}) [h1 h3]
    exact rfl
  have hx : eval_prim O x_1 inp = x := by
    simp [x_1, x]
  have hs : eval_prim O s_1 inp = s := by
    simp [s_1, s]


  cases Classical.em (x≤s) with
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
        simp [hx,hs]
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
        simp [hx,hs]
        apply gt_of_not_le hr


-- @[simp] theorem c_pair_g_ev :eval O (c_pair_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); Nat.pair <$> evaln O (k + 1) cf n <*> evaln O (k + 1) cg n : Option ℕ) := by rw [← eval_prim_eq_eval (c_pair_g_ev_pr)]; simp only [c_pair_g_evp]
end Nat.RecursiveIn.Code
end pair_g

section comp_g
namespace Nat.RecursiveIn.Code

-- input is of the form (s,x)
def c_comp_g : Code→Code→Code := fun cf cg =>
  let x         := right
  let s         := left

  c_if_le_te.comp₄ x s

  (
    c_ifz.comp₃ (cg.comp c_id) (c_const 0) $
    c_ifz.comp₃ (cf.comp c_id) (c_const 0) $
    succ.comp (pair (c_pred.comp (cf.comp c_id)) (c_pred.comp (cg.comp c_id)))
  )

  (c_const 0)
@[simp] theorem c_comp_g_ev_pr (hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_comp_g cf cg) := by
  unfold c_comp_g
  repeat (first|assumption|simp|constructor)
@[simp] theorem c_comp_g_evp:eval_prim O (c_comp_g cf cg) inp =
  let x         := inp.r
  let s         := inp.l
  Encodable.encode (do guard (x≤s); Nat.pair <$> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cf inp)) <*> ((@Denumerable.ofNat (Option ℕ)) (eval_prim O cg inp))) := by

  lift_lets
  extract_lets
  expose_names

  simp only [Option.bind_eq_bind]
  simp [Encodable.encode]
  simp [Seq.seq]

  unfold c_comp_g
  lift_lets
  extract_lets
  expose_names
  simp [eval_prim]
  have h0 : (Denumerable.ofNat (Option ℕ) 0) = Option.none := by exact rfl
  have h1 {x} (h2:¬x=0) : x=x-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h2)
  have h2 {x} (h3:¬x=0) : (Denumerable.ofNat (Option ℕ) x) = Option.some (x-1) := by
    rw (config := {occs := .pos [1]}) [h1 h3]
    exact rfl
  have hx : eval_prim O x_1 inp = x := by
    simp [x_1, x]
  have hs : eval_prim O s_1 inp = s := by
    simp [s_1, s]


  cases Classical.em (x≤s) with
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
        simp [hx,hs]
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
        simp [hx,hs]
        apply gt_of_not_le hr


-- @[simp] theorem c_comp_g_ev :eval O (c_comp_g) = fun (n:ℕ) => Encodable.encode (do guard (n.r≤n.l); Nat.pair <$> evaln O (k + 1) cf n <*> evaln O (k + 1) cg n : Option ℕ) := by rw [← eval_prim_eq_eval (c_comp_g_ev_pr)]; simp only [c_comp_g_evp]
end Nat.RecursiveIn.Code
end comp_g





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






def evaln' (O:ℕ→ℕ) : ℕ → Code → ℕ → Option ℕ :=
  fun s code n => do
  guard (n ≤ s-1)
  match s, code with
  | 0, _ => Option.none
  | k + 1, zero => do
    return 0
  | k + 1, succ =>  do
    return (Nat.succ n)
  | k + 1, left => do
    return n.unpair.1
  | k + 1, right => do
    pure n.unpair.2
  | k + 1, oracle => do
    -- (O n).toOption
    -- umm. this is a contradiction. um.
    pure (O n)
  | k + 1, pair cf cg => do
    Nat.pair <$> evaln' O (k + 1) cf n <*> evaln' O (k + 1) cg n
  | k + 1, comp cf cg => do
    let x ← evaln' O (k + 1) cg n
    evaln' O (k + 1) cf x
  | k + 1, prec cf cg => do
    n.unpaired fun a n =>
      n.casesOn (evaln' O (k + 1) cf a) fun y => do
        let i ← evaln' O k (prec cf cg) (Nat.pair a y)
        evaln' O (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => do
    n.unpaired fun a m => do
      let x ← evaln' O (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln' O k (rfind' cf) (Nat.pair a (m + 1))


theorem evaln_eq_evaln' : evaln O s code x = evaln' O s code x := by
  match s with
  | 0 => unfold evaln; unfold evaln'; simp
  | k+1 =>
    induction code with
    | zero => unfold evaln; unfold evaln'; simp
    | succ => unfold evaln; unfold evaln'; simp
    | left => unfold evaln; unfold evaln'; simp
    | right => unfold evaln; unfold evaln'; simp
    | oracle => unfold evaln; unfold evaln'; simp
    | pair _ _ _ _ => expose_names; unfold evaln; unfold evaln'; simp [a_ih,a_ih_1]
    | comp _ _ _ _ =>
      expose_names; unfold evaln; unfold evaln';
      -- simp [←a_ih_1]
      simp [←a_ih]
    | prec _ _ _ _ => expose_names; unfold evaln; unfold evaln'; simp [a_ih,a_ih_1]
    | rfind' _ _ => expose_names; unfold evaln; unfold evaln'; simp [a_ih,a_ih_1]

  -- funext s code x
  -- unfold evaln
  -- unfold evaln'
  -- match s, code with
  -- | 0, _ => sorry
  -- | k+1, zero => sorry
  -- sorry



/- `[c_evaln_aux](0, (0,0)) .last = [ [0]₀(0) ] = [0]` -/
/-- `eval c_evaln_aux (_, (c,s)) .last = [ [c]ₛ(0), [c]ₛ(1), ..., [c]ₛ(s) ]` -/
-- we might not care about what it means to query (x,(code,s)) in comp_hist when x>s or smth.
def c_evaln_aux :=
  -- let x_code_s  := (succ.comp (left.comp right))
  let code_s  := (succ.comp (left.comp right))
  -- let x         := left.comp x_code_s
  let code      := left.comp code_s
  let s         := right.comp code_s
  let sM1       := c_pred.comp s
  let comp_hist := right.comp right
  let n         := c_sub.comp₂ code (c_const 5)
  let m         := c_div2.comp $ c_div2.comp n
  let ml        := left.comp m
  let mr        := right.comp m

  let ele := left
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

  -- pair
  let pc_ml_s (c') := lookup (c') (ml.comp right) (s.comp right) -- `[ml]ₛ(x)`
  let pc_mr_s (c') := lookup (c') (mr.comp right) (s.comp right) -- `[mr]ₛ(x)`
  let pc_m_s  (c') := lookup (c') (m.comp  right) (s.comp right) -- `[mr]ₛ(x)`

  let opt_pair := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_if_eq_te.comp₄ (pc_ml_s ele) (c_opt_none) (c_opt_none) $
    c_if_eq_te.comp₄ (pc_mr_s ele) (c_opt_none) (c_opt_none) $
    succ.comp (pair (c_opt_iget.comp (pc_ml_s ele)) (c_opt_iget.comp (pc_mr_s ele)))
  let pair_mapped := ((c_list_map' opt_pair).comp₂ (c_list_range.comp s) c_id)

  -- comp: `[ml]ₛ ( [mr]ₛ(x) ) `
  -- let pc_mr_xM1 := c_opt_iget.comp (pc_mr_s ele)
  -- let pc_ml (inp) := c_l_get_opt.comp₂ comp_hist (pair inp (pair mr s))
  -- let pc_mlmr_x_lookup := lookup pc_mr_xM1 (ml.comp right) (s.comp right)
  let opt_comp := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ (pc_mr_s ele) (c_opt_none) $
    c_ifz.comp₃ (pc_ml_s $ c_pred.comp (pc_mr_s ele)) (c_opt_none) $
    (pc_ml_s $ c_pred.comp (pc_mr_s ele))
  let comp_mapped := ((c_list_map' opt_comp).comp₂ (c_list_range.comp s) c_id)

  -- prec: if `x.r=n+1`, then `[mr](x.l, (x.r-1, [code](x.l, x.r-1)))` else `[ml](x.l,0)`
  let pc_code_sM1 (c') := lookup (c') (code.comp right) (sM1.comp right) -- `[code]_{s-1}(x)`

  let prec_x   := left.comp ele
  let prec_i   := right.comp ele
  let prec_iM1 := c_pred.comp prec_i

  let prec_base_case      := pc_ml_s prec_x
  let prec_prev_case      := pc_code_sM1 (pair prec_x (prec_iM1))
  let prec_inductive_case := pc_mr_s (pair prec_x (pair prec_iM1 (c_pred.comp prec_prev_case)))

  let opt_prec := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ prec_i prec_base_case $
    c_ifz.comp₃ prec_prev_case (zero) prec_inductive_case
  let prec_mapped := ((c_list_map' opt_prec).comp₂ (c_list_range.comp s) c_id)

  -- let rfind'_m := right.comp ele
  let rfind'_base := pc_m_s ele
  let rfind'_indt := pc_code_sM1 (pair (left.comp ele) (succ.comp (right.comp ele)))
  let opt_rfind' := c_if_gt_te.comp₄ ele (sM1.comp right) (c_opt_none) $
    c_ifz.comp₃ rfind'_base (zero) $
    c_ifz.comp₃ (c_pred.comp rfind'_base) (succ.comp $ right.comp ele) rfind'_indt
  let rfind'_mapped := ((c_list_map' opt_rfind').comp₂ (c_list_range.comp s) c_id)

/-
    -- c_l_get.comp₂ comp_hist (pair pc_mr_x (pair (left.comp m) s))
  let pc  := c_l_get.comp₂ comp_hist (pair x (pair m              s))
-/


  let nMod4     := c_mod.comp₂ n (c_const 4)

  c_cov_rec

  (c_list_singleton zero) $

  -- c_if_gt_te.comp₄ x     sM1           (c_const 0)              $ -- if ¬x≤s, then diverge
  c_if_eq_te.comp₄ s     (c_const 0) (c_list_singleton zero)                $ -- if s=0, then diverge
  -- c_if_eq_te.comp₄ code  (c_const 0) (c_zero_g.comp₂   sM1 x) $
  c_if_eq_te.comp₄ code  (c_const 0) zero_mapped   $
  c_if_eq_te.comp₄ code  (c_const 1) succ_mapped   $
  c_if_eq_te.comp₄ code  (c_const 2) left_mapped   $
  c_if_eq_te.comp₄ code  (c_const 3) right_mapped  $
  c_if_eq_te.comp₄ code  (c_const 4) oracle_mapped $
  -- c_if_eq_te.comp₄ nMod4 (c_const 0) ((c_pair_g pc_ml_x pc_mr_x).comp₂ sM1 x)  $
  c_if_eq_te.comp₄ nMod4 (c_const 0) pair_mapped   $
  c_if_eq_te.comp₄ nMod4 (c_const 1) comp_mapped   $
  c_if_eq_te.comp₄ nMod4 (c_const 2) prec_mapped   $
                                     rfind'_mapped
/-- api: `Nat.pair x (Nat.pair code s)` -/
def c_evaln :=
  -- let code_s := right
  -- let x := left
  c_list_getI.comp₂ (c_list_getLastI.comp $ c_evaln_aux.comp (pair (c_const 17) right)) left


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

theorem c_evaln_evp_aux_0_0_0 : eval_prim O (c_evaln) (Nat.pair 0 (Nat.pair 0 0)) = Encodable.encode (evaln' O 0 (0:ℕ) 0) := by
  simp [decodeCode, evaln'] -- simp rhs
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

theorem c_evaln_evp_aux_x_0_0 : eval_prim O (c_evaln) (Nat.pair (x+1) (Nat.pair 0 0)) = Encodable.encode (evaln' O 0 (0:ℕ) (x+1)) := by

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
  have hsM1 {anything hist} : eval_prim O sM1 (Nat.pair anything (Nat.pair k hist)) = s-1 := by
    simp [sM1]
    simp [hs]
  have hx {anything hist} : eval_prim O x_1 (Nat.pair anything (Nat.pair k hist)) = x := by
    simp [x_1]
    simp [x_code_s]
    simp [h0]
  have hcode {anything hist} : eval_prim O code (Nat.pair anything (Nat.pair k hist)) = 0 := by
    simp [code]
    simp [x_code_s]
    simp [h0]
  simp [hsM1, hx, hcode, hs]
  simp [decodeCode, evaln'] -- simp rhs

theorem c_evaln_evp_aux_0_np1 : eval_prim O (c_evaln) (Nat.pair x (Nat.pair (n+1) 0)) = Encodable.encode (evaln' O 0 (n+1:ℕ) x) := by
  simp [decodeCode, evaln'] -- simp rhs


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
  have hsM1 {anything hist} : eval_prim O sM1 (Nat.pair anything (Nat.pair k hist)) = 0 := by
    simp [sM1]
    simp [hs]
  have hcode {anything hist} : eval_prim O code (Nat.pair anything (Nat.pair k hist)) = (n+1) := by
    simp [code]
    simp [x_code_s]
    simp [h0]

  simp
  rw [←h0]
  simp [hsM1,hcode, hs]

theorem c_evaln_aux_evp_aux (hcode_val:code≤4) :
  eval_prim O (c_evaln_aux) (Nat.pair 17 (Nat.pair code (s+1)))
    =
  List.map (o2n ∘ evaln O (s+1) (code:ℕ)) (List.range (s+1))
  :=
  by
  -- let k:=(Nat.pair code (s+1))-1
  -- have kP1_gt_0 : Nat.pair code (s+1)>0 := by
  --   apply pair_r_gt0
  --   -- apply pair_r_gt0
  --   exact zero_lt_succ s
  -- have h0: k+1=(Nat.pair code (s+1)) := by exact Nat.sub_add_cancel kP1_gt_0
  -- rw [←h0]


  -- unfold c_evaln;
  unfold c_evaln_aux
  lift_lets
  extract_lets
  expose_names

  simp


  sorry

  have hx {xx} : eval_prim O x_1 (Nat.pair 17 (Nat.pair xx (eval_prim O c_evaln_aux (Nat.pair 17 k)))) = x := by
    simp [x_1]
    simp [h0]
  have hcode_s : eval_prim O code_s (k+1) = Nat.pair code (s+1) := by
    simp [code_s]
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
  | 0 =>
    simp
    -- simp [opt_zero]
    simp [hcode, hsM1, hs, hx, hcode_s, decodeCode, evaln]
    simp [Nat.pair]
    simp [o2n]
  stop
  sorry
@[simp] theorem map_getI : (List.map (f) (List.range (s + 1))).getI x = if x<s+1 then f x else 0 := by
  unfold List.getI
  cases Classical.em (x<s+1) with
  | inl h => simp [h]
  | inr h => simp [h]
theorem c_evaln_evp_aux (hcode_val:code≤4) :
  eval_prim O (c_evaln) (Nat.pair x (Nat.pair code (s+1)))
    =
  -- List.map (o2n ∘ evaln O (s+1) (code:ℕ)) (List.range (s+1))
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
    -- apply pair_r_gt0
    exact zero_lt_succ s
  have hkP1: k+1=((Nat.pair code (s + 1))) := by exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]

  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k)))
  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k))) = covrec_inp := rfl

  have stupidrewrite :
  (eval_prim O
  (zero.c_list_singleton.c_cov_rec
    (c_if_eq_te.comp
      ((s_1.pair (c_const 0)).pair
        (zero.c_list_singleton.pair
          (c_if_eq_te.comp
            ((code_1.pair (c_const 0)).pair
              (zero_mapped.pair
                (c_if_eq_te.comp
                  ((code_1.pair (c_const 1)).pair
                    (succ_mapped.pair
                      (c_if_eq_te.comp
                        ((code_1.pair (c_const 2)).pair
                          (left_mapped.pair
                            (c_if_eq_te.comp
                              ((code_1.pair (c_const 3)).pair
                                (right_mapped.pair
                                  (c_if_eq_te.comp
                                    ((code_1.pair (c_const 4)).pair
                                      (oracle_mapped.pair
                                        (c_if_eq_te.comp
                                          ((nMod4.pair (c_const 0)).pair
                                            (opt_pair_1.pair
                                              (c_if_eq_te.comp
                                                ((nMod4.pair (c_const 1)).pair
                                                  (opt_pair_1.pair
                                                    (c_if_eq_te.comp
                                                      ((nMod4.pair (c_const 2)).pair
                                                        ((c_const 0).pair
                                                          (c_const 1)))))))))))))))))))))))))))))
                    (Nat.pair 17 k))
                      = (eval_prim O c_evaln_aux (Nat.pair 17 k)) := by exact rfl
  simp [stupidrewrite,covrec_inp_simp]


  -- have hele : eval_prim O ele covrec_inp = x := by
  --   simp [ele]
  --   simp [covrec_inp]
  have hcode_s : eval_prim O code_s covrec_inp = (Nat.pair code (s + 1)) := by
    simp [code_s]
    simp [covrec_inp]
    simp [hkP1]
  have hs : eval_prim O s_1 covrec_inp = s+1 := by
    simp [s_1]
    simp [hcode_s]
  have hsM1 : eval_prim O sM1 covrec_inp = s := by
    simp [sM1]
    simp [hs]
  have hcode : eval_prim O code_1 covrec_inp = code := by
    simp [code_1]
    simp [hcode_s]
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
    | inl h => simp [h, decodeCode, evaln, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 1 =>
    simp [hsucc_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, evaln, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 2 =>
    simp [hleft_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, evaln, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 3 =>
    simp [hright_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, evaln, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | 4 =>
    simp [horacle_mapped]
    cases Classical.em (x<s+1) with
    | inl h => simp [h, decodeCode, evaln, le_of_lt_succ h]
    | inr h => simp [h, decodeCode, evaln, Nat.not_le_of_lt (not_lt.mp h), Option.bind]
  | n+5 => simp at hcode_val
-- set_option maxHeartbeats 15000


theorem c_evaln_evp_aux_nMod4_0 :
  eval_prim O (c_evaln) (Nat.pair x (Nat.pair ((n+4)+1) (s+1)))
    =
  let m := n.div2.div2
  let ml        := m.l
  let mr        := m.r
  -- pair
  -- let pc_ml_x := c_l_get.comp₂ comp_hist (x.pair (ml.pair s)) -- `[ml]ₛ(x)`
  -- let pc_mr_x := c_l_get.comp₂ comp_hist (x.pair (mr.pair s)) -- `[mr]ₛ(x)`
  let k:=(Nat.pair ((n+4)+1) (s+1))-1
  let covrec_inp := Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k)))

  let pc_ml_s (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair ml (s+1)))
  let pc_mr_s (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair mr (s+1)))
  let pc_m_s  (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair m  (s+1)))

  let pc_code_sM1 (c') (elem) := eval_prim O (c_evaln) (Nat.pair (eval_prim O c' (Nat.pair elem covrec_inp)) (Nat.pair ((n+4)+1) s))
  -- let pc_ml (inp) := if inp≤s+1 then eval_prim O (c_evaln) (Nat.pair inp (Nat.pair ml (s+1))) + 1 else 0

  -- c_if_gt_te.comp₄ x sM1 (c_const 0) $
  --   c_ifz.comp₃ pc_mr_x (c_const 0) $
  --   c_ifz.comp₃ pc_mlmr_x_lookup (c_const 0) $
  --   (c_pred.comp pc_mlmr_x_lookup)

  let opt_pair (elem) := Encodable.encode (do guard (elem≤s); Nat.pair<$>n2o (pc_ml_s left elem)<*>n2o (pc_mr_s left elem))
  let opt_comp (elem) := Encodable.encode (do guard (elem≤s); let intermediate ← (n2o (pc_mr_s left elem)); n2o (pc_ml_s left intermediate))
  -- let opt_prec (elem) := Encodable.encode (do guard (elem≤s); let intermediate ← ((n2o) (pc_mr_x elem)); (n2o) (pc_ml_x intermediate))

  -- let prec_base_case      := pc_ml_s prec_x
  -- let prec_prev_case      := pc_code_sM1 (pair prec_x (prec_iM1))
  -- let prec_inductive_case := pc_mr_s (pair prec_x (pair prec_iM1 prec_prev_case))

  let prec_x   := left.comp left
  let prec_i   := right.comp left
  let prec_iM1 := c_pred.comp prec_i

  let opt_prec (elem) :=
  Encodable.encode (
    do
    guard (elem ≤ s)
    
    (Nat.rec (n2o (pc_ml_s left elem.l))
          (fun n_2 n_ih ↦
            do
              let i ← n2o (pc_code_sM1 (left) (Nat.pair elem.l (elem.r-1)))
              n2o (pc_mr_s (left) (Nat.pair elem.l (Nat.pair (elem.r-1) i)))
          )
          elem.r:Option ℕ)
    )

  let opt_rfind' (elem) :=
  Encodable.encode ( do
    guard (elem ≤ s)
    (unpaired fun a m => do
      -- let x ← evaln O (s + 1) m (Nat.pair a m)
      let x ← n2o $ pc_m_s left elem
      if x = 0 then
        pure m
      else
        -- evaln O s (rfind' m) (Nat.pair a (m + 1)))
        n2o (pc_code_sM1 left (Nat.pair a (m + 1)))) 
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


  have kP1_gt_0 : Nat.pair ((n+4)+1) (s+1)>0 := by
    apply pair_r_gt0
    exact zero_lt_succ s
  have hkP1: k+1=(Nat.pair ((n+4)+1) (s+1)) := by
    exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]


  have covrec_inp_simp : Nat.pair 17 (Nat.pair k (eval_prim O c_evaln_aux (Nat.pair 17 k))) = covrec_inp := rfl

  have stupidrewrite :
  (eval_prim O
                      (zero.c_list_singleton.c_cov_rec
                        (c_if_eq_te.comp
                          ((s_1.pair (c_const 0)).pair
                            (zero.c_list_singleton.pair
                              (c_if_eq_te.comp
                                ((code.pair (c_const 0)).pair
                                  (zero_mapped.pair
                                    (c_if_eq_te.comp
                                      ((code.pair (c_const 1)).pair
                                        (succ_mapped.pair
                                          (c_if_eq_te.comp
                                            ((code.pair (c_const 2)).pair
                                              (left_mapped.pair
                                                (c_if_eq_te.comp
                                                  ((code.pair (c_const 3)).pair
                                                    (right_mapped.pair
                                                      (c_if_eq_te.comp
                                                        ((code.pair (c_const 4)).pair
                                                          (oracle_mapped.pair
                                                            (c_if_eq_te.comp
                                                              ((nMod4.pair (c_const 0)).pair
                                                                (pair_mapped.pair
                                                                  (c_if_eq_te.comp
                                                                    ((nMod4.pair (c_const 1)).pair
                                                                      (comp_mapped.pair
                                                                        (c_if_eq_te.comp
                                                                          ((nMod4.pair (c_const 2)).pair
                                                                            (prec_mapped.pair
                                                                              rfind'_mapped))))))))))))))))))))))))))))
                      (Nat.pair 17 k))
                      = (eval_prim O c_evaln_aux (Nat.pair 17 k)) := by exact rfl
  simp [stupidrewrite,covrec_inp_simp]




  -- unfold c_evaln; unfold c_evaln_aux
  -- simp
  -- rw [h0]
  -- simp
  have hcode_s : eval_prim O code_s covrec_inp = (Nat.pair ((n+4)+1) (s+1)) := by
    simp [code_s]
    simp [covrec_inp]
    simp [hkP1]
  have hs : eval_prim O s_1 covrec_inp = s+1 := by
    simp [s_1]
    simp [hcode_s]
  have hsM1 : eval_prim O sM1 covrec_inp = s := by
    simp [sM1]
    simp [hs]
  have hcode : eval_prim O code covrec_inp = (n+4)+1 := by
    simp [code]
    simp [hcode_s]
  have hn : eval_prim O n_1 covrec_inp = n := by
    simp [n_1]
    simp [hcode]
  have hm : eval_prim O m_1 covrec_inp = m := by
    simp [m_1]
    simp [hn]
    simp [m]
    simp [div2_val]
  have hml:eval_prim O ml_1 covrec_inp=ml:=by simp [ml_1,hm,ml]
  have hmr:eval_prim O mr_1 covrec_inp=mr:=by simp [mr_1,hm,mr]
  have hnMod4 : eval_prim O nMod4 covrec_inp = n%4 := by
    simp [nMod4]
    simp [hn]

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

  have bounds_left_aux_1 : ml<n+4+1 := by
    apply lt_add_one_of_le
    unfold ml
    unfold m
    simp [div2_val]
    exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have bounds_aux : Nat.pair (n + 4 + 1) (s+1) ≥ 1 := by
    apply pair_l_gt0
    exact zero_lt_succ (n + 4)
  have bounds_left_aux_2 : Nat.pair ml (s+1) < k+1 := by
    unfold k
    simp [Nat.sub_add_cancel bounds_aux]
    exact pair_lt_pair_left (s+1) bounds_left_aux_1
  have bounds_left_aux_3 : Nat.pair ml (s+1) ≤ k := by
    apply le_of_lt_succ bounds_left_aux_2
  have bounds_left {elem:ℕ} : Nat.pair (eval_prim O (ml_1.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (s_1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hml,hs]
    exact bounds_left_aux_3

  have bounds_right_aux_1 : mr<n+4+1 := by
    apply lt_add_one_of_le
    unfold mr
    unfold m
    simp [div2_val]
    exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have bounds_right_aux_2 : (Nat.pair mr (s+1)) < k+1 := by
    unfold k
    simp [Nat.sub_add_cancel bounds_aux]
    exact pair_lt_pair_left (s+1) bounds_right_aux_1
  have bounds_right_aux_3 : Nat.pair mr (s+1) ≤ k := by
    apply le_of_lt_succ bounds_right_aux_2
  have bounds_right {elem:ℕ} : Nat.pair (eval_prim O (mr_1.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (s_1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hmr,hs]
    exact bounds_right_aux_3

  have bounds_m_aux_1 : m<n+4+1 := by
    
    apply lt_add_one_of_le
    unfold m
    simp [div2_val]
    -- exact?
    exact le_add_right_of_le (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
  have bounds_m_aux_2 : (Nat.pair m (s+1)) < k+1 := by
    unfold k
    simp [Nat.sub_add_cancel bounds_aux]
    exact pair_lt_pair_left (s+1) bounds_m_aux_1
  have bounds_m_aux_3 : Nat.pair m (s+1) ≤ k := by
    apply le_of_lt_succ bounds_m_aux_2
  have bounds_m {elem:ℕ} : Nat.pair (eval_prim O (m_1.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (s_1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hm,hs]
    exact bounds_m_aux_3

  have bounds_pc_code_aux_2 : (Nat.pair (n+4+1) s) < k+1 := by
    unfold k
    simp [Nat.sub_add_cancel bounds_aux]
    apply pair_lt_pair_right
    exact lt_add_one s
  have bounds_pc_code_aux_3 : Nat.pair (n+4+1) s ≤ k := by
    apply le_of_lt_succ bounds_pc_code_aux_2
  have bounds_pc_code_sM1 {elem:ℕ} : Nat.pair (eval_prim O (code.comp right) (Nat.pair elem covrec_inp)) (eval_prim O (sM1.comp right) (Nat.pair elem covrec_inp)) ≤ k := by
    simp [hcode,hsM1]
    simp [k]
    exact bounds_pc_code_aux_3

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
  have hpc_code_sM1 (c') (elem:ℕ): eval_prim O (pc_code_sM1_1 c') (Nat.pair elem covrec_inp) = pc_code_sM1 c' elem := by
    simp [pc_code_sM1_1]
    simp [hlookup elem bounds_pc_code_sM1]
    unfold pc_code_sM1
    simp [hsM1,hcode,covrec_inp]

  have hnat_to_opt_0 : (Denumerable.ofNat (Option ℕ) 0) = Option.none := by exact rfl
  have hnat_to_opt_1_aux {x} (h2:¬x=0) : x=x-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h2)
  have hnat_to_opt_1 {x} (h3:¬x=0) : (Denumerable.ofNat (Option ℕ) x) = Option.some (x-1) := by
    rw (config := {occs := .pos [1]}) [hnat_to_opt_1_aux h3]
    exact rfl
  have hnat_to_opt_2 {x} (h3:¬x=o2n Option.none) : n2o x = (Option.some (x-1)) := by
    rw (config := {occs := .pos [1]}) [hnat_to_opt_1_aux h3]
    exact rfl
  have not_none_imp_not_zero {xx} (h:¬xx=o2n Option.none):¬xx=0:=by
    simp at h
    exact h
  -- have rw_ele : ele = left := rfl
  have hopt_pair :
    (fun ele => eval_prim O opt_pair_1 (Nat.pair ele covrec_inp))
      =
    -- (o2n ∘ evaln O (s+1) (pair ml mr))
    (opt_pair)
    := by
      funext elem
      simp [opt_pair_1]
      simp [hsM1]
      -- #check rw_ele
      -- rewrite (config:={occs:=.pos [2]}) [rw_ele]
      -- rewrite [rw_ele]
      -- simp only [rw_ele]

      unfold ele
      simp [hpc_ml_s, hpc_mr_s]
      simp [opt_pair]
      -- simp [evaln]
      cases Classical.em (elem≤s) with
      | inl h =>
        simp [h, Nat.not_lt_of_le h]
        -- unfold pc_ml_s
        -- cases Classical.em (pc_ml_s elem=0) with
        cases Classical.em (pc_ml_s left elem=o2n Option.none) with
        -- cases Classical.em (n2o (pc_ml_s elem)=Option.none) with
        | inl hh =>
          simp [hh, hnat_to_opt_0]
          simp [Seq.seq]
        | inr hh =>
          simp [not_none_imp_not_zero hh]
          cases Classical.em (pc_mr_s left elem=o2n Option.none) with
          | inl hhh =>
            simp [hhh, hnat_to_opt_0]
            simp [Seq.seq]
          | inr hhh =>
            simp [not_none_imp_not_zero hhh]
            simp [hnat_to_opt_2 hh, hnat_to_opt_2 hhh]
      | inr h => simp [h, gt_of_not_le h, Option.bind]
  have hpair_mapped:eval_prim O pair_mapped covrec_inp = (map (opt_pair) (range (s+1))) := by simp [pair_mapped, hs,hopt_pair]


  -- have hpc_mr_xM1 (elem:ℕ) : eval_prim O pc_mr_xM1 (Nat.pair elem covrec_inp) = (Option.iget (n2o (pc_mr_x elem))) := by
  --   simp [pc_mr_xM1]
  --   simp [hpc_mr_x]
  -- have hpc_mlmr_x_lookup (elem:ℕ) : eval_prim O pc_mlmr_x_lookup (Nat.pair elem covrec_inp) = (pc_ml_x (Option.iget (n2o (pc_mr_x elem)))) := by
  --   simp [pc_mlmr_x_lookup]
  --   simp [hlookup elem bounds_left]
  --   simp [hpc_mr_xM1,hml,hs]
  --   simp [pc_ml_x]
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
          -- simp [hpc_mlmr_s_lookup]
          simp [not_none_imp_not_zero hh]
          -- rw [hnat_to_opt_1 hh]
          -- simp [Option.bind]
          cases Classical.em (pc_ml_s (c_pred.comp (pc_mr_s_1 left)) elem=o2n Option.none) with
          | inl hhh =>
            simp [hhh];
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

  -- -- have hprec_i : eval_prim O hprec_i (Nat.pair ele covrec_inp)
  -- have hprec_base_case (elem:ℕ) : eval_prim O prec_base_case (Nat.pair elem covrec_inp) = pc_ml_x elem.l := by
  --   unfold prec_base_case
  --   simp [hlookup elem bounds_left]
  --   simp [prec_x,ele,hs,hml]
  --   simp [pc_ml_x]
  -- have hprec_prev_case (elem:ℕ) : eval_prim O prec_prev_case (Nat.pair elem covrec_inp) = pc_ml_x elem.l := by
  --   unfold prec_prev_case
  --   simp [hlookup elem bounds_left]
  --   simp [prec_x,ele,hs,hml]
  --   simp [pc_ml_x]

  have hprec_x (elem) : eval_prim O prec_x_1 (Nat.pair elem covrec_inp) = elem.l := by simp [prec_x_1,ele]
  have hprec_i (elem) : eval_prim O prec_i_1 (Nat.pair elem covrec_inp) = elem.r := by simp [prec_i_1,ele]
  have hprec_iM1 (elem) : eval_prim O prec_iM1_1 (Nat.pair elem covrec_inp) = elem.r-1 := by simp [prec_iM1_1,hprec_i]
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
          simp [prec_i_1,ele,helemr]

          simp [pc_code_sM1]

          simp [hpc_code_sM1 ((prec_x_1.pair prec_iM1_1)) elem]
          have rw_elemr : nn = elem.r-1 := by simp [helemr]
          rw [rw_elemr]

          simp [pc_code_sM1]
          simp [hprec_x, hprec_iM1]
          
          
          cases Classical.em ((eval_prim O c_evaln (Nat.pair (Nat.pair elem.l (elem.r - 1)) (Nat.pair (n + 4 + 1) s))) = o2n Option.none) with
          | inl hh =>
            simp [hh, hnat_to_opt_0]
          | inr hh =>
            simp [not_none_imp_not_zero hh]
            rw [hnat_to_opt_2 hh]
            simp [Option.bind]
            simp [pc_mr_s]
            simp [hprec_x, hprec_iM1]
            simp [hpc_code_sM1]
            simp [pc_code_sM1]
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
      #check hpc_mr_s
      #check hpc_m_s
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
          simp [hpc_code_sM1]
          simp [pc_code_sM1]
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


theorem evaln_bound' (h:¬x≤s) : evaln O s c x = Option.none := by sorry

  
@[simp] theorem c_evaln_evp: eval_prim O (c_evaln) (Nat.pair x (Nat.pair code s)) =
  Encodable.encode (evaln O s code x) := by

  let code_s:=Nat.pair code s
  rw [show Nat.pair code s = code_s by rfl]
  rw [show code = code_s.l by simp [code_s]]
  rw [show s = code_s.r by simp [code_s]]
  -- let x_code_s:=Nat.pair x (Nat.pair code s)
  -- rw [show Nat.pair x (Nat.pair code s) = x_code_s by rfl]
  -- rw [show code = x_code_s.r.l by simp [x_code_s]]
  -- rw [show s = x_code_s.r.r by simp [x_code_s]]
  -- rw [show x = x_code_s.l by simp [x_code_s]]

  induction code_s using Nat.strong_induction_on generalizing x with
  | _ code_s ih =>

    let code:=code_s.l
    let s:=code_s.r
    rw [show code_s = (Nat.pair code s) from by simp [code,s]]
    simp only [pair_r, pair_l]


    match hs_val:s,hcode_val:code with
    | 0,    0   =>
      cases x with
      | zero => exact c_evaln_evp_aux_0_0_0
      | succ n => exact c_evaln_evp_aux_x_0_0
    | 0,    n+1 =>
      unfold c_evaln; unfold c_evaln_aux
      lift_lets
      extract_lets
      expose_names
      -- exact c_evaln_evp_aux_0_np1
      simp
      sorry
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

      let pc_ml_x := Nat.pair m.l (sM1+1)
      have pc_ml_x_lt_cs : pc_ml_x < code_s := by
        unfold pc_ml_x; rw [h0]
        exact pair_lt_pair_left (sM1 + 1) _m1
      let pc_mr_x := Nat.pair m.r (sM1+1)
      have pc_mr_x_lt_cs : pc_mr_x < code_s := by
        unfold pc_mr_x; rw [h0]
        exact pair_lt_pair_left (sM1 + 1) _m2
      let m_s := Nat.pair m (sM1+1)
      have m_s_lt_cs : m_s < code_s := by
        unfold m_s; rw [h0]
        apply pair_lt_pair_left
        exact hm
        -- (sM1 + 1) _m2

      let pc_code_sM1 := Nat.pair (n+4+1) sM1
      have pc_code_s_lt_cs : pc_code_sM1 < code_s := by
        unfold pc_code_sM1;
        rw [h0]
        apply pair_lt_pair_right
        exact lt_add_one sM1

      rw [show n+5=(n+4)+1 from rfl]
      -- stop


      cases hno:n.bodd with
      | false => cases hn2o:n.div2.bodd with
        -- pair
        | false =>
          have h0: n%4=0 := nMod4_eq_0 hno hn2o
          -- simplify the rhs
          -- simp
          simp [decodeCode]
          simp [evaln,hno, hn2o]


          -- rw [c_evaln_evp_aux_nMod4_0 h0]
          rw [c_evaln_evp_aux_nMod4_0]
          simp [h0]
          -- rw [c_replace_oracle_evp_aux_nMod4]


          -- simp only []
          rw [ih pc_mr_x pc_mr_x_lt_cs];
          rw [ih pc_ml_x pc_ml_x_lt_cs];

          simp only [pc_ml_x, pc_mr_x, m]
          simp


        -- prec
        | true =>
          have h0: n%4=2 := nMod4_eq_2 hno hn2o

          -- simplify the rhs
          -- simp
          simp [decodeCode]
          simp only [hno, hn2o, evaln]
          -- simp

          rw [c_evaln_evp_aux_nMod4_0]
          simp [h0]

          rw [ih pc_ml_x pc_ml_x_lt_cs];
          rw [ih pc_code_sM1 pc_code_s_lt_cs]
          have ih_i {i} : (eval_prim O c_evaln (Nat.pair (Nat.pair x.l (Nat.pair (x.r - 1) i)) (Nat.pair n.div2.div2.r (sM1 + 1)))) = (Encodable.encode (evaln O pc_mr_x.r (decodeCode pc_mr_x.l) (Nat.pair x.l (Nat.pair (x.r - 1) i)))) := by
            rw [ih pc_mr_x pc_mr_x_lt_cs];
          simp [ih_i]

          -- have rw1 : (evaln O pc_ml_x.r (decodeCode pc_ml_x.l) x.l) = 
          -- have rw2 : (evaln O pc_code_sM1.r (decodeCode pc_code_sM1.l) (Nat.pair x.l (x.r - 1))) = (evaln O sM1 ((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r)) (Nat.pair x.l n_1)) := by sorry

          cases Classical.em (x≤sM1) with
          | inl h =>
            simp [h]
            simp [pc_ml_x]
            simp [pc_mr_x]
            simp [pc_code_sM1]
            simp [m]
            cases x.r with
            | zero => rfl
            | succ xxx =>
              simp
              have rw3_aux : encodeCode (((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r))) = (n + 4 + 1) := by
                simp [encodeCode]
                apply codes_aux_2 hno hn2o
              
              have rw3 : ((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r)) = (decodeCode (n + 4 + 1)) := by
                rw [←(decodeCode_encodeCode (decodeCode (n + 4 + 1)))]
                rw [←(decodeCode_encodeCode (((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r))))]
                simp [rw3_aux]
              rw [rw3]
            
            

          | inr h =>
            simp [h,Option.bind]

      | true => cases hn2o:n.div2.bodd with
        -- comp
        | false =>
          have h0: n%4=1 := nMod4_eq_1 hno hn2o

          -- simplify the rhs
          -- simp
          simp [decodeCode]
          simp [evaln,hno, hn2o]

          rw [c_evaln_evp_aux_nMod4_0]
          simp [h0]

          rw [ih pc_mr_x pc_mr_x_lt_cs];
          simp [pc_mr_x, m]

          cases Classical.em (x≤sM1) with
          | inl h =>
            simp [h]
            cases Classical.em (evaln O (sM1 + 1) (decodeCode n.div2.div2.r) x=Option.none) with
            | inl hh => simp [hh]
            | inr hh =>
              have optval := Option.eq_none_or_eq_some (evaln O (sM1 + 1) (decodeCode n.div2.div2.r) x)
              simp [hh] at optval
              rcases optval with ⟨inter, hinter⟩
              -- rw
              simp [hinter]
              rw [ih pc_ml_x pc_ml_x_lt_cs];
              simp [pc_ml_x, m]

          | inr h =>
            simp [h,Option.bind]

        -- rfind
        | true =>
          have h0: n%4=3 := nMod4_eq_3 hno hn2o
          simp [decodeCode]
          simp [evaln,hno, hn2o]

          rw [c_evaln_evp_aux_nMod4_0]
          simp [h0]

          rw [ih m_s m_s_lt_cs];
          rw [ih pc_code_sM1 pc_code_s_lt_cs]
          -- have ih_i {i} : (eval_prim O c_evaln (Nat.pair (Nat.pair x.l (Nat.pair (x.r - 1) i)) (Nat.pair n.div2.div2.r (sM1 + 1)))) = (Encodable.encode (evaln O pc_mr_x.r (decodeCode pc_mr_x.l) (Nat.pair x.l (Nat.pair (x.r - 1) i)))) := by
          --   rw [ih pc_mr_x pc_mr_x_lt_cs];
          -- simp [ih_i]

          -- have rw1 : (evaln O pc_ml_x.r (decodeCode pc_ml_x.l) x.l) = 
          -- have rw2 : (evaln O pc_code_sM1.r (decodeCode pc_code_sM1.l) (Nat.pair x.l (x.r - 1))) = (evaln O sM1 ((decodeCode n.div2.div2.l).prec (decodeCode n.div2.div2.r)) (Nat.pair x.l n_1)) := by sorry

          cases Classical.em (x≤sM1) with
          | inl h =>
            simp [h]
            -- simp [pc_ml_x]
            -- simp [pc_mr_x]
            simp [m_s]
            simp [m]
            simp [pc_code_sM1]

            have rw0 : (decodeCode (n + 4 + 1)) = (decodeCode n.div2.div2).rfind' := by sorry
            rw [rw0]
            
          | inr h =>
            simp [h,Option.bind]



@[simp] theorem c_evaln_ev:eval O (c_evaln) = unpaired evaln := by rw [← eval_prim_eq_eval c_evaln_ev_pr]; simp only [c_evaln_evp];
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.evaln:Nat.PrimrecIn O (unpaired evaln) := by rw [← c_evaln_evp]; apply code_prim_prop c_evaln_ev_pr
theorem Nat.Primrec.evaln:Nat.Primrec (unpaired evaln) := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.evaln
end evaln
