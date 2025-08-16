import Computability.Constructions.Basic

open Nat.RecursiveIn.Code

-- section bfind
-- namespace Nat.RecursiveIn.Code
-- def p_bfind (O) (cf) (b) (n) := n≤b ∧ eval_prim O cf n = 0
-- instance pbf : DecidablePred (p_bfind O cf b) := by

--   exact Classical.decRel (p_bfind O cf) b
-- theorem hp_bfind (cf) (b) : ∃n, p_bfind O cf b n := by
--   use b+1
--   simp [p_bfind]
-- -- abbrev bfind (cf) := fun a => Nat.rfind fun n => (fun m => m = 0) <$> eval_prim O c (Nat.pair a n)
-- def c_bfind (cf:Code) :=
--   let i := left.comp right
--   let b := left
--   let bMi := c_sub.comp₂ b i
--   let prev := right.comp right
--   (
--     prec
--     (c_ifz.comp₃ (cf.comp b) b zero) $
--     c_ifz.comp₃ (cf.comp bMi) bMi prev
--   ).comp (pair c_id c_id)
-- @[simp] theorem c_bfind_ev_pr (hcf:code_prim cf) :code_prim (c_bfind cf) := by unfold c_bfind; repeat (first|assumption|simp|constructor)
-- -- @[simp] theorem c_bfind_evp : eval_prim O (c_bfind cf) b = @Nat.find (p_bfind O cf b) _ (hp_bfind cf b) := by
-- @[simp] theorem c_bfind_evp : eval_prim O (c_bfind cf) b = o2n (if ∃x≤b,eval_prim O cf x=0 then some x else Option.none) := by
--   simp [c_bfind]
--   cases Classical.em (∃x≤b,eval_prim O cf x=0) with
--   | inl h =>
--     simp [h]
--   | inr h => simp [h]

-- @[simp] theorem c_bfind_ev : eval O c_bfind (Nat.pair lN i) = o2n (n2l lN)[i]? := by simp [← eval_prim_eq_eval c_bfind_ev_pr]
-- end Nat.RecursiveIn.Code
-- end bfind



section l_append
def Nat.list_append (list index:ℕ):ℕ:=Nat.pair (list.l+1) $ Nat.pair list.r index
namespace Nat.RecursiveIn.Code
def c_l_append := pair (succ.comp $ left.comp left) (pair (right.comp left) right)
@[simp] theorem c_l_append_ev_pr:code_prim c_l_append := by unfold c_l_append; repeat (first|assumption|simp|constructor)
@[simp] theorem c_l_append_evp:eval_prim O c_l_append = unpaired2 Nat.list_append := by unfold Nat.list_append; simp [c_l_append,eval_prim];
@[simp] theorem c_l_append_ev:eval O c_l_append = unpaired2 Nat.list_append := by rw [← eval_prim_eq_eval c_l_append_ev_pr]; simp only [c_l_append_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.l_append:Nat.PrimrecIn O Nat.l_append := by ...
-- theorem Nat.Primrec.l_append:Nat.Primrec Nat.l_append := by ...
end l_append

section l_get_last
def Nat.list_get_last_aux (list index:ℕ):ℕ:=
  match index with
  | 0 => list.r
  | Nat.succ prev_index => (Nat.list_get_last_aux list prev_index).l
def Nat.list_get_lastn (list index:ℕ):ℕ:=(Nat.list_get_last_aux list index).r
def Nat.list_get_last (list:ℕ) :=list.r.r
def Nat.list_size (list:ℕ) := list.l
def Nat.list_get (list index:ℕ) := Nat.list_get_lastn list (list.list_size-1-index)

#check (Nat.pair 2 (Nat.pair (Nat.pair 0 132) 42))
#eval Nat.list_get_last (Nat.pair 2 (Nat.pair (Nat.pair 0 132) 42))
#eval Nat.list_get_lastn (Nat.pair 2 (Nat.pair (Nat.pair 0 132) 42)) 0
#eval Nat.list_get_lastn (Nat.pair 2 (Nat.pair (Nat.pair 0 132) 42)) 1

namespace Nat.RecursiveIn.Code
def c_l_get_lastn_aux := prec right (left.comp $ right.comp right)
@[simp] theorem c_l_get_lastn_aux_ev_pr:code_prim c_l_get_lastn_aux := by unfold c_l_get_lastn_aux; repeat (first|assumption|simp|constructor)
@[simp] theorem c_l_get_lastn_aux_evp:eval_prim O c_l_get_lastn_aux = unpaired2 Nat.list_get_last_aux := by
  simp [c_l_get_lastn_aux,eval_prim];
  funext n;
  simp [unpaired2]
  induction n.r with
  | zero => exact rfl
  | succ n h => exact congrArg Prod.fst (congrArg unpair h)
@[simp] theorem c_l_get_lastn_aux_ev:eval O c_l_get_lastn_aux = unpaired2 Nat.list_get_last_aux := by rw [← eval_prim_eq_eval c_l_get_lastn_aux_ev_pr]; simp only [c_l_get_lastn_aux_evp];

def c_l_get_lastn := right.comp c_l_get_lastn_aux
@[simp] theorem c_l_get_lastn_ev_pr:code_prim c_l_get_lastn := by unfold c_l_get_lastn; repeat (first|assumption|simp|constructor)
@[simp] theorem c_l_get_lastn_evp:eval_prim O c_l_get_lastn = unpaired2 Nat.list_get_lastn := by
  unfold list_get_lastn
  simp [c_l_get_lastn,eval_prim];
@[simp] theorem c_l_get_lastn_ev:eval O c_l_get_lastn = unpaired2 Nat.list_get_lastn := by rw [← eval_prim_eq_eval c_l_get_lastn_ev_pr]; simp only [c_l_get_lastn_evp];

def c_l_get_last := c_l_get_lastn.comp₂ c_id (c_const 0)
@[simp] theorem c_l_get_last_ev_pr:code_prim c_l_get_last := by unfold c_l_get_last; repeat (first|assumption|simp|constructor);
@[simp] theorem c_l_get_last_evp:eval_prim O c_l_get_last = Nat.list_get_last := by
  unfold list_get_last
  simp [c_l_get_last,eval_prim];
  exact rfl
@[simp] theorem c_l_get_last_ev:eval O c_l_get_last = Nat.list_get_last := by rw [← eval_prim_eq_eval c_l_get_last_ev_pr]; simp only [c_l_get_last_evp];
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.l_get:Nat.PrimrecIn O Nat.l_get := by ...
-- theorem Nat.Primrec.l_get:Nat.Primrec Nat.l_get := by ...
end l_get_last


-- takes a pair (list,index)
section l_get
namespace Nat.RecursiveIn.Code
def c_l_get := c_l_get_lastn.comp₂ left (c_sub.comp₂ (c_pred.comp (left.comp left)) (right))
@[simp] theorem c_l_get_ev_pr:code_prim c_l_get := by unfold c_l_get; repeat (first|assumption|simp|constructor)
@[simp] theorem c_l_get_evp:eval_prim O c_l_get = unpaired2 Nat.list_get := by
  unfold Nat.list_get;
  simp [c_l_get,eval_prim];
  funext xs
  exact rfl
@[simp] theorem c_l_get_ev:eval O c_l_get = unpaired2 Nat.list_get := by rw [← eval_prim_eq_eval c_l_get_ev_pr]; simp only [c_l_get_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.l_get:Nat.PrimrecIn O Nat.l_get := by ...
-- theorem Nat.Primrec.l_get:Nat.Primrec Nat.l_get := by ...
end l_get

-- takes a pair (list,index). returns l[i]+1 if exists, 0 otherwise
section l_get_opt
namespace Nat.RecursiveIn.Code
def c_l_get_opt :=
  let list        := left
  let list_length := left.comp list
  let index       := right

  c_if_lt_te.comp₄ index list_length
  (succ.comp $ c_l_get.comp₂ list index)
  (c_const 0)
  -- c_l_get_opt_lastn.comp₂ left (c_sub.comp₂ (c_pred.comp (left.comp left)) (right))
@[simp] theorem c_l_get_opt_ev_pr:code_prim c_l_get_opt := by unfold c_l_get_opt; repeat (first|assumption|simp|constructor)
@[simp] theorem c_l_get_opt_evp {O list index}:eval_prim O c_l_get_opt (Nat.pair list index) = if index<Nat.list_size list then (Nat.list_get list index)+1 else 0 := by
  simp [c_l_get_opt,eval_prim, comp₄];
  exact rfl
-- @[simp] theorem c_l_get_opt_ev:eval O c_l_get_opt = unpaired2 Nat.list_get := by rw [← eval_prim_eq_eval c_l_get_opt_ev_pr]; simp only [c_l_get_opt_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.l_get_opt:Nat.PrimrecIn O Nat.l_get_opt := by ...
-- theorem Nat.Primrec.l_get_opt:Nat.Primrec Nat.l_get_opt := by ...
end l_get_opt


@[simp] theorem Nat.list_get_last_append : Nat.list_get_last (Nat.list_append lst x) = x := by
  unfold list_append
  unfold list_get_last
  simp



section efl
namespace Nat.RecursiveIn.Code
def c_efl:ℕ→ℕ:=fun c=>c_l_append.comp (pair c_id c)
-- def c_efl:=fun c=>c_l_append.comp₂ c_id c
@[simp] theorem c_efl_ev_pr (h:code_prim c):code_prim $ c_efl c := by unfold c_efl; repeat (first|assumption|simp|constructor)

-- @[simp] theorem c_efl_pr_aux:Primrec (pair c_id) := by
--   refine Primrec.projection ?_
--   apply PrimrecIn.PrimrecIn₂_iff_Primrec₂.mp
--   intro O
--   apply pair_prim
-- @[simp] theorem c_efl_pr: Nat.Primrec c_efl := by
--   refine Primrec.nat_iff.mp ?_
--   apply c_efl_pr_aux

-- huh interesting, it doesn't care about c being code_prim or not.
@[simp] theorem c_efl_evp:eval_prim O (c_efl c) x= Nat.list_append x (eval_prim O c x) := by
  unfold list_append
  simp [c_efl,eval_prim];
  unfold list_append
  simp
@[simp] theorem c_efl_ev : eval O (c_efl c) x = Nat.list_append <$> x <*> (eval O c x) := by
  unfold Nat.list_append
  simp [c_efl,eval]
  simp [Seq.seq]

  exact Part.bind_some_eq_map x.list_append (eval O c x)
  -- exact Part.bind_some_eq_map x.list_append (eval O (decodeCode c) x)
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.efl:Nat.PrimrecIn O Nat.efl := by ...
-- theorem Nat.Primrec.efl:Nat.Primrec Nat.efl := by ...
-- theorem c_efl_ev_left (h:(eval O c x).Dom) : eval O (left.comp $ c_efl c) x = x := by
--   have h0 : (eval O c x).get h ∈ (eval O c x) := by exact Part.get_mem h
--   have h1 : eval O c x = Part.some ((eval O c x).get h) := by exact Part.get_eq_iff_eq_some.mp rfl

--   simp [c_efl, eval]
--   rw [h1]
--   -- should maybe define some theorem that simplfies the Nat.pair <*> business
--   simp [Seq.seq]
--   exact Part.Dom.bind h fun y ↦ Part.some x
end efl

@[simp] theorem last_efl : eval_prim O (c_l_get_last.comp (c_efl c)) = eval_prim O c := by
  simp only [eval_prim]
  simp




def Nat.list_empty := Nat.pair 0 0
def Nat.list_singleton (ele:ℕ) := Nat.list_append Nat.list_empty ele
namespace Nat.RecursiveIn.Code
def c_list_singleton (ele:Code): Code := c_l_append.comp₂ Nat.list_empty ele
end Nat.RecursiveIn.Code

open Nat in
@[simp] theorem append_empty : (list_empty.list_append x).list_get 0 = x := by
  unfold list_empty
  unfold list_append
  unfold list_get
  unfold list_get_lastn
  unfold list_get_last_aux
  unfold list_size
  simp


open Nat in
@[simp] theorem append_get_last_aux {l:ℕ}: l.list_get_last_aux i =  (l.list_append x).list_get_last_aux (i+1) := by
  induction i
  ·
    unfold list_get_last_aux
    unfold list_get_last_aux
    unfold list_append
    simp
  · expose_names
    unfold list_append
    unfold list_get_last_aux
    rw [h]
    unfold list_append
    simp

open Nat in
@[simp] theorem append_getlastn {l:ℕ}: l.list_get_lastn i = (l.list_append x).list_get_lastn (i+1) := by
  unfold list_get_lastn
  rw [append_get_last_aux]

open Nat in
@[simp] theorem append_size {l:ℕ} : (l.list_append x).list_size = l.list_size +1 := by
  unfold list_append
  unfold list_size
  simp

open Nat in
@[simp] theorem append_get {l:ℕ} (hi:i<l.list_size): l.list_get i = (l.list_append x).list_get i := by
  unfold list_get
  simp only [append_size]
  simp
  have hi5 : l.list_size - i - 1 = l.list_size - 1 - i := by exact Simproc.sub_add_eq_comm l.list_size i 1
  have hi6 : l.list_size - i > 0 := by exact zero_lt_sub_of_lt hi
  have main_rewrite : (l.list_size - 1 - i)+1 = l.list_size - i := by
    rw [←hi5]
    exact Nat.sub_add_cancel hi6

  rw [←main_rewrite]
  exact append_getlastn


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
