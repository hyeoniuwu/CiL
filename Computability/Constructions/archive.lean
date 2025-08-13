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
