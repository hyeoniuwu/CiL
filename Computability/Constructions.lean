import Computability.RecursiveInTheorems

open Nat.RecursiveIn.Code



section id
namespace Nat.RecursiveIn.Code
def c_id := left.pair right
@[simp] theorem c_id_ev_pr:code_prim c_id := by unfold c_id; repeat (constructor; try simp)
@[simp] theorem c_id_evp:eval_prim O c_id n= n := by simp [c_id,eval_prim]
@[simp] theorem c_id_ev:eval O c_id n = n := by simp [c_id,eval,Seq.seq]
  -- #check @eval_prim_eq_eval c_id O c_id_ev_pr
  -- apply (@eval_prim_eq_eval c_id O c_id_ev_pr)
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.id:Nat.PrimrecIn O Nat.id := by ...
-- theorem Nat.Primrec.id:Nat.Primrec Nat.id := by ...
end id
section const
namespace Nat.RecursiveIn.Code
def c_const:ℕ→Code
| 0 => zero
| n+1 => comp succ (c_const n)
@[simp] theorem c_const_ev_pr:code_prim (c_const n) := by
  induction n
  · unfold c_const; exact code_prim.zero
  · unfold c_const
    expose_names
    exact code_prim.comp code_prim.succ h
@[simp] theorem c_const_evp: ∀ n m, eval_prim O (c_const n) m = n
| 0, _ => rfl
| n+1, m => by simp! [c_const_evp n m]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.const:Nat.PrimrecIn O Nat.const := by ...
-- theorem Nat.Primrec.const:Nat.Primrec Nat.const := by ...
end const
section curry
namespace Nat.RecursiveIn.Code
def c_curry (c : Code) (n : ℕ) : Code := comp c (pair (c_const n) c_id)
theorem _id_eq_c_id : c_id = Code.id := by simp [c_id,Code.id]
theorem _const_eq_c_const : c_const = Code.const := by
  funext n;
  unfold c_const
  unfold Code.const
  induction n
  · exact rfl
  · simp
    unfold c_const
    unfold Code.const
    expose_names
    exact h
theorem _curry_eq_c_curry : c_curry = curry := by
  unfold c_curry
  unfold curry
  rw [_id_eq_c_id]
  rw [_const_eq_c_const]
-- @[simp] theorem c_curry_ev_pr:code_prim (c_curry c n) := by
@[simp] theorem c_curry_evp: eval_prim O (c_curry c n) x = eval_prim O c (Nat.pair n x) := by simp [c_curry,eval_prim]
@[simp] theorem c_curry_ev: eval O (c_curry c n) x = eval O c (Nat.pair n x) := by rw [_curry_eq_c_curry]; exact eval_curry c n x

end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.curry:Nat.PrimrecIn O Nat.curry := by ...
-- theorem Nat.Primrec.curry:Nat.Primrec Nat.curry := by ...
end curry

section sgsg'
/-- The signum function on naturals.  -/
@[simp] def Nat.sg := fun x => if x=0 then 0 else 1
/-- Maps zero to 1 and non-zero natural numbers to 0. This is the inverse of `Nat.sg` for boolean-like computations. -/
@[simp] def Nat.sg' := fun x => if x=0 then 1 else 0
namespace Nat.RecursiveIn.Code
def c_sg := comp (prec zero (((c_const 1).comp left).comp left)) (pair zero c_id)
@[simp] theorem c_sg_ev_pr:code_prim c_sg := by unfold c_sg; repeat (constructor; try simp)
@[simp] theorem c_sg_evp:eval_prim O c_sg = Nat.sg := by
  simp [c_sg,eval_prim]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp] theorem c_sg_ev : eval O c_sg = Nat.sg := by rw [← eval_prim_eq_eval c_sg_ev_pr]; simp only [c_sg_evp]
def c_sg' := comp (prec (c_const 1) (((zero).comp left).comp left)) (pair zero c_id)
@[simp] theorem c_sg'_ev_pr:code_prim c_sg' := by unfold c_sg'; repeat (constructor; try simp)
@[simp] theorem c_sg'_evp:eval_prim O c_sg' = Nat.sg' := by
  simp [c_sg',eval_prim]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp] theorem c_sg'_ev : eval O c_sg' = Nat.sg' := by rw [← eval_prim_eq_eval c_sg'_ev_pr]; simp only [c_sg'_evp]
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.sg:Nat.PrimrecIn O Nat.sg := by rw [←c_sg_evp]; apply code_prim_prop c_sg_ev_pr
theorem Nat.PrimrecIn.sg':Nat.PrimrecIn O Nat.sg' := by rw [←c_sg'_evp]; apply code_prim_prop c_sg'_ev_pr
theorem Nat.Primrec.sg:Nat.Primrec Nat.sg := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.sg
theorem Nat.Primrec.sg':Nat.Primrec Nat.sg' := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.sg'
end sgsg'


section add
namespace Nat.RecursiveIn.Code
def c_add := (prec c_id ((succ.comp right).comp right))
@[simp] theorem c_add_ev_pr:code_prim c_add := by unfold c_add; repeat (constructor; try simp)
@[simp] theorem c_add_evp:eval_prim O c_add = unpaired Nat.add := by
  simp [c_add,eval_prim]
  funext n;
  simp [unpaired]
  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h => exact Nat.add_left_inj.mpr h
@[simp] theorem c_add_ev:eval O c_add = unpaired Nat.add := by rw [← eval_prim_eq_eval c_add_ev_pr]; simp only [c_add_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.add:Nat.PrimrecIn O Nat.add := by ...
-- theorem Nat.Primrec.add:Nat.Primrec Nat.add := by ...
end add
section mul
namespace Nat.RecursiveIn.Code
def c_mul := prec zero (c_add.comp (pair left (right.comp right)))
@[simp] theorem c_mul_ev_pr:code_prim c_mul := by unfold c_mul; repeat (constructor; try simp)
@[simp] theorem c_mul_evp:eval_prim O c_mul = unpaired Nat.mul := by
  simp [c_mul,eval_prim]
  funext n;
  simp [unpaired]
  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h =>
    simp [*, mul_succ];
    (expose_names; exact Nat.add_comm (unpair n_1).1 ((unpair n_1).1 * n))
@[simp] theorem c_mul_ev:eval O c_mul = unpaired Nat.mul := by rw [← eval_prim_eq_eval c_mul_ev_pr]; simp only [c_mul_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.mul:Nat.PrimrecIn O Nat.mul := by ...
-- theorem Nat.Primrec.mul:Nat.Primrec Nat.mul := by ...
end mul
section pow
namespace Nat.RecursiveIn.Code
def c_pow := prec (c_const 1) (c_mul.comp (pair (right.comp right) left))
@[simp] theorem c_pow_ev_pr:code_prim c_pow := by unfold c_pow; repeat (constructor; try simp)
@[simp] theorem c_pow_evp:eval_prim O c_pow = unpaired Nat.pow := by
  simp [c_pow,eval_prim]
  funext n;
  simp [unpaired]

  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h => simp [*, pow_succ];
@[simp] theorem c_pow_ev:eval O c_pow = unpaired Nat.pow := by rw [← eval_prim_eq_eval c_pow_ev_pr]; simp only [c_pow_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.pow:Nat.PrimrecIn O Nat.pow := by ...
-- theorem Nat.Primrec.pow:Nat.Primrec Nat.pow := by ...
end pow

section prec1
namespace Nat.RecursiveIn.Code
def c_prec1 (m) (cf:Code) := ((prec (c_const m) (cf.comp right)).comp (zero.pair c_id))
@[simp] theorem c_prec1_ev_pr (hcf:code_prim cf) : code_prim (@c_prec1 m cf) := by
  unfold c_prec1;
  repeat constructor
  simp
  repeat constructor
  exact hcf
  repeat constructor
@[simp] theorem c_prec1_ev : eval_prim O (c_prec1 m cf) = (fun n => n.rec m fun y IH => eval_prim O cf <| Nat.pair y IH) := by simp [c_prec1,eval_prim]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.prec1:Nat.PrimrecIn O Nat.prec1 := by ...
-- theorem Nat.Primrec.prec1:Nat.Primrec Nat.prec1 := by ...
end prec1
section casesOn1
namespace Nat.RecursiveIn.Code
def c_casesOn1 (m) (cf:Code) := @c_prec1 m (cf.comp left)
-- theorem c_casesOn1_ev_pr:code_prim (@c_casesOn1 a b) := by unfold c_casesOn1; repeat constructor;
@[simp] theorem c_casesOn1_ev : eval_prim O (@c_casesOn1 m cf) = (Nat.casesOn · m (eval_prim O cf)) := by simp [c_casesOn1,eval_prim]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.casesOn1:Nat.PrimrecIn O Nat.casesOn1 := by ...
-- theorem Nat.Primrec.casesOn1:Nat.Primrec Nat.casesOn1 := by ...
end casesOn1

section pred
namespace Nat.RecursiveIn.Code
def c_pred := (c_casesOn1 0 c_id)
@[simp] theorem c_pred_ev_pr:code_prim c_pred := by unfold c_pred; repeat (constructor; try simp)
@[simp] theorem c_pred_evp:eval_prim O c_pred = Nat.pred := by
  simp [c_pred,eval_prim]
  funext n;
  cases n <;> simp [*]
@[simp] theorem c_pred_ev:eval O c_pred = Nat.pred := by rw [← eval_prim_eq_eval c_pred_ev_pr]; simp only [c_pred_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.pred:Nat.PrimrecIn O Nat.pred := by ...
-- theorem Nat.Primrec.pred:Nat.Primrec Nat.pred := by ...
end pred
section sub
namespace Nat.RecursiveIn.Code
def c_sub := prec c_id ((c_pred.comp right).comp right)
@[simp] theorem c_sub_ev_pr:code_prim c_sub := by unfold c_sub; repeat (constructor; try simp)
@[simp] theorem c_sub_evp:eval_prim O c_sub = unpaired Nat.sub := by
  simp [c_sub,eval_prim]
  funext n;
  simp [unpaired]
  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h =>
    simp [*, Nat.sub_add_eq];
@[simp] theorem c_sub_ev:eval O c_sub = unpaired Nat.sub := by rw [← eval_prim_eq_eval c_sub_ev_pr]; simp only [c_sub_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.sub:Nat.PrimrecIn O Nat.sub := by ...
-- theorem Nat.Primrec.sub:Nat.Primrec Nat.sub := by ...
end sub
section dist
namespace Nat.RecursiveIn.Code
def c_dist := c_add.comp (pair c_sub (c_sub.comp (pair right left)))
@[simp] theorem c_dist_ev_pr:code_prim c_dist := by unfold c_dist; repeat (constructor; try simp)
@[simp] theorem c_dist_evp:eval_prim O c_dist = unpaired Nat.dist := by simp [c_dist,eval_prim]; exact rfl
@[simp] theorem c_dist_ev:eval O c_dist = unpaired Nat.dist := by rw [← eval_prim_eq_eval c_dist_ev_pr]; simp only [c_dist_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.dist:Nat.PrimrecIn O Nat.dist := by ...
-- theorem Nat.Primrec.dist:Nat.Primrec Nat.dist := by ...
end dist
@[simp] theorem eq_zero_iff_dist_zero {a b:ℕ} : a.dist b = 0 ↔ a=b := by
  constructor
  · exact fun a_1 ↦ Nat.eq_of_dist_eq_zero a_1
  · exact fun a_1 ↦ Nat.dist_eq_zero a_1
theorem sgdist_eq_ifeq {a b:ℕ} : (if a.dist b = 0 then 0 else 1) = (if a=b then 0 else 1) := by
  simp only [eq_zero_iff_dist_zero]

section if_eq'
namespace Nat.RecursiveIn.Code
def c_if_eq' := c_sg.comp c_dist
@[simp] theorem c_if_eq'_ev_pr:code_prim c_if_eq' := by unfold c_if_eq'; repeat (constructor; try simp)
@[simp] theorem c_if_eq'_evp:eval_prim O c_if_eq' = fun ab => if ab.l=ab.r then 0 else 1 := by simp [c_if_eq',eval_prim];
@[simp] theorem c_if_eq'_ev:eval O c_if_eq' = fun ab => if ab.l=ab.r then 0 else 1 := by rw [← eval_prim_eq_eval c_if_eq'_ev_pr]; simp only [c_if_eq'_evp]; simp; funext xs; exact apply_ite Part.some ((unpair xs).1 = (unpair xs).2) 0 1
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_eq':Nat.PrimrecIn O Nat.if_eq' := by ...
-- theorem Nat.Primrec.if_eq':Nat.Primrec Nat.if_eq' := by ...
end if_eq'

section ifz
namespace Nat.RecursiveIn.Code
def c_ifz := c_add.comp $ pair (c_mul.comp $ pair (c_sg'.comp left) (left.comp right)) (c_mul.comp $ pair (c_sg.comp left) (right.comp right))
@[simp] theorem c_ifz_ev_pr:code_prim c_ifz := by unfold c_ifz; repeat (constructor; try simp)
@[simp] theorem c_ifz_evp:eval_prim O c_ifz = fun (cab:ℕ) => if cab.l=0 then cab.r.l else cab.r.r := by
  simp [c_ifz,eval_prim];
  funext xs
  have hsplit : (unpair xs).1 = 0 ∨ ¬ ((unpair xs).1 = 0) := by exact Or.symm (ne_or_eq (unpair xs).1 0)
  cases hsplit with
  | inl h => simp [h]
  | inr h => simp [h]
@[simp] theorem c_ifz_ev:eval O c_ifz = fun (cab:ℕ) => if cab.l=0 then cab.r.l else cab.r.r := by rw [← eval_prim_eq_eval c_ifz_ev_pr]; simp only [c_ifz_evp];
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.ifz:Nat.PrimrecIn O Nat.ifz := by ...
-- theorem Nat.Primrec.ifz:Nat.Primrec Nat.ifz := by ...
end ifz




section ef
namespace Nat.RecursiveIn.Code
def c_ef:ℕ→ℕ:=fun c=>(pair Nat.RecursiveIn.Code.id c)
-- @[simp] theorem c_ef_ev_pr:code_prim $ c_ef c := by unfold c_ef; repeat (constructor; try simp)
@[simp] theorem c_ef_pr_aux:Primrec (pair Nat.RecursiveIn.Code.id) := by
  refine Primrec.projection ?_
  apply PrimrecIn.PrimrecIn₂_iff_Primrec₂.mp
  intro O
  apply pair_prim
@[simp] theorem c_ef_pr: Nat.Primrec c_ef := by
  refine Primrec.nat_iff.mp ?_
  apply c_ef_pr_aux
-- @[simp] theorem c_ef_evp:eval_prim O c_ef = fun ab => if ab.l=ab.r then 0 else 1 := by simp [c_ef,eval_prim];
theorem c_ef_ev : eval O (c_ef c) x = Nat.pair <$> x <*> (eval O c x) := by simp [c_ef,eval]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.ef:Nat.PrimrecIn O Nat.ef := by ...
-- theorem Nat.Primrec.ef:Nat.Primrec Nat.ef := by ...
theorem c_ef_ev_left (h:(eval O c x).Dom) : eval O (left.comp $ c_ef c) x = x := by
  have h0 : (eval O c x).get h ∈ (eval O c x) := by exact Part.get_mem h
  have h1 : eval O c x = Part.some ((eval O c x).get h) := by exact Part.get_eq_iff_eq_some.mp rfl

  simp [c_ef, eval]
  rw [h1]
  -- should maybe define some theorem that simplfies the Nat.pair <*> business
  simp [Seq.seq]
  exact Part.Dom.bind h fun y ↦ Part.some x
end ef



section l_append
def Nat.list_append (list index:ℕ):ℕ:=Nat.pair (list.l+1) $ Nat.pair list.r index
namespace Nat.RecursiveIn.Code
def c_l_append := pair (succ.comp $ left.comp left) (pair (right.comp left) right)
@[simp] theorem c_l_append_ev_pr:code_prim c_l_append := by unfold c_l_append; repeat (constructor; try simp)
@[simp] theorem c_l_append_evp:eval_prim O c_l_append = unpaired Nat.list_append := by unfold Nat.list_append; simp [c_l_append,eval_prim];
@[simp] theorem c_l_append_ev:eval O c_l_append = unpaired Nat.list_append := by rw [← eval_prim_eq_eval c_l_append_ev_pr]; simp only [c_l_append_evp]
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
@[simp] theorem c_l_get_lastn_aux_ev_pr:code_prim c_l_get_lastn_aux := by unfold c_l_get_lastn_aux; repeat (constructor; try simp)
@[simp] theorem c_l_get_lastn_aux_evp:eval_prim O c_l_get_lastn_aux = unpaired Nat.list_get_last_aux := by
  simp [c_l_get_lastn_aux,eval_prim];
  funext n;
  simp [unpaired]
  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h => exact congrArg Prod.fst (congrArg unpair h)
@[simp] theorem c_l_get_lastn_aux_ev:eval O c_l_get_lastn_aux = unpaired Nat.list_get_last_aux := by rw [← eval_prim_eq_eval c_l_get_lastn_aux_ev_pr]; simp only [c_l_get_lastn_aux_evp];

def c_l_get_lastn := right.comp c_l_get_lastn_aux
@[simp] theorem c_l_get_lastn_ev_pr:code_prim c_l_get_lastn := by unfold c_l_get_lastn; repeat (constructor; try simp)
@[simp] theorem c_l_get_lastn_evp:eval_prim O c_l_get_lastn = unpaired Nat.list_get_lastn := by
  unfold list_get_lastn
  simp [c_l_get_lastn,eval_prim];
@[simp] theorem c_l_get_lastn_ev:eval O c_l_get_lastn = unpaired Nat.list_get_lastn := by rw [← eval_prim_eq_eval c_l_get_lastn_ev_pr]; simp only [c_l_get_lastn_evp];

def c_l_get_last := c_l_get_lastn.comp $ pair c_id (c_const 0)
@[simp] theorem c_l_get_last_ev_pr:code_prim c_l_get_last := by unfold c_l_get_last; repeat (constructor; try simp);
@[simp] theorem c_l_get_last_evp:eval_prim O c_l_get_last = Nat.list_get_last := by
  unfold list_get_last
  simp [c_l_get_last,eval_prim];
  exact rfl
@[simp] theorem c_l_get_last_ev:eval O c_l_get_last = Nat.list_get_last := by rw [← eval_prim_eq_eval c_l_get_last_ev_pr]; simp only [c_l_get_last_evp];
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.l_get:Nat.PrimrecIn O Nat.l_get := by ...
-- theorem Nat.Primrec.l_get:Nat.Primrec Nat.l_get := by ...
end l_get_last


section l_get
namespace Nat.RecursiveIn.Code
def c_l_get := c_l_get_lastn.comp $ pair left (c_sub.comp $ pair (c_pred.comp (left.comp left)) (right))
@[simp] theorem c_l_get_ev_pr:code_prim c_l_get := by unfold c_l_get; repeat (constructor; try simp)
@[simp] theorem c_l_get_evp:eval_prim O c_l_get = unpaired Nat.list_get := by
  unfold Nat.list_get;
  simp [c_l_get,eval_prim];
  funext xs
  exact rfl
@[simp] theorem c_l_get_ev:eval O c_l_get = unpaired Nat.list_get := by rw [← eval_prim_eq_eval c_l_get_ev_pr]; simp only [c_l_get_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.l_get:Nat.PrimrecIn O Nat.l_get := by ...
-- theorem Nat.Primrec.l_get:Nat.Primrec Nat.l_get := by ...
end l_get





@[simp] theorem Nat.list_get_last_append : Nat.list_get_last (Nat.list_append lst x) = x := by
  unfold list_append
  unfold list_get_last
  simp



section efl
namespace Nat.RecursiveIn.Code
-- def c_efl:ℕ→ℕ:=fun c=>c_l_append.comp (pair c_id c)
def c_efl:=fun c=>c_l_append.comp (pair c_id c)
@[simp] theorem c_efl_ev_pr (h:code_prim c):code_prim $ c_efl c := by
  unfold c_efl;
  -- simp
  repeat (constructor; try simp)
  exact h
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


section efl_prec
namespace Nat.RecursiveIn.Code
-- def c_efl_prec:ℕ→ℕ:=fun c=>c_l_append.comp (pair c_id c)
def c_efl_prec:=fun c=>c_l_append.comp (pair (c_id.comp (right.comp right)) c)
@[simp] theorem c_efl_prec_ev_pr (h:code_prim c):code_prim $ c_efl_prec c := by
  unfold c_efl_prec;
  -- simp
  repeat (constructor; try simp)
  exact h
-- @[simp] theorem c_efl_prec_pr_aux:Primrec (pair c_id) := by
--   refine Primrec.projection ?_
--   apply PrimrecIn.PrimrecIn₂_iff_Primrec₂.mp
--   intro O
--   apply pair_prim
-- @[simp] theorem c_efl_prec_pr: Nat.Primrec c_efl_prec := by
--   refine Primrec.nat_iff.mp ?_
--   apply c_efl_prec_pr_aux

-- huh interesting, it doesn't care about c being code_prim or not.
@[simp] theorem c_efl_prec_evp:eval_prim O (c_efl_prec c) x= Nat.list_append x.r.r (eval_prim O c x) := by
  unfold list_append
  simp [c_efl_prec,eval_prim];
  unfold list_append
  simp
@[simp] theorem c_efl_prec_ev : eval O (c_efl_prec c) x = Nat.list_append <$> x.r.r <*> (eval O c x) := by
  unfold Nat.list_append
  simp [c_efl_prec,eval]
  simp [Seq.seq]
  exact Part.bind_some_eq_map (unpair (unpair x).2).2.list_append (eval O c x)
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.efl_prec:Nat.PrimrecIn O Nat.efl_prec := by ...
-- theorem Nat.Primrec.efl_prec:Nat.Primrec Nat.efl_prec := by ...
-- theorem c_efl_prec_ev_left (h:(eval O c x).Dom) : eval O (left.comp $ c_efl_prec c) x = x := by
--   have h0 : (eval O c x).get h ∈ (eval O c x) := by exact Part.get_mem h
--   have h1 : eval O c x = Part.some ((eval O c x).get h) := by exact Part.get_eq_iff_eq_some.mp rfl

--   simp [c_efl_prec, eval]
--   rw [h1]
--   -- should maybe define some theorem that simplfies the Nat.pair <*> business
--   simp [Seq.seq]
--   exact Part.Dom.bind h fun y ↦ Part.some x
end efl_prec

@[simp] theorem last_efl_prec : eval_prim O (c_l_get_last.comp (c_efl c)) = eval_prim O c := by
  simp only [eval_prim]
  simp



def Nat.list_empty := Nat.pair 0 0
def Nat.list_singleton (ele:ℕ) := Nat.list_append Nat.list_empty ele
namespace Nat.RecursiveIn.Code
def c_list_singleton (ele:Code): Code := c_l_append.comp $ pair Nat.list_empty ele
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
@[simp] theorem append_get_0 {l:ℕ} (hi:0<l.l) : (l.list_get 0 = y) → (l.list_append x).list_get 0 = y := by
  unfold list_append
  unfold list_get
  unfold list_get_lastn
  unfold list_get_last_aux
  unfold list_size
  simp
  sorry


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




section cov_rec
namespace Nat.RecursiveIn.Code
/-
eval_prim O (c_cov_rec cf cg) (Nat.pair x i)
should be the list of all values of
eval_prim O (c_cov_rec cf cg) (Nat.pair x j)
for j=0 to i-1.
-/
-- def c_cov_rec (cf cg:Code):= prec (c_l_append.comp $ pair (c_const Nat.list_empty) (cf.comp left)) $ (c_efl cg).comp (right.comp right)
def c_cov_rec (cf cg:Code):= prec (c_l_append.comp $ pair (c_const Nat.list_empty) (cf.comp left)) $ c_efl_prec cg
-- @[simp] theorem c_div_flip_ev_pr:code_prim c_div_flip := by unfold c_div_flip; repeat (constructor; try simp)
theorem asd : eval_prim O (c_cov_rec cf cg) (Nat.pair x (i+1)) = eval_prim O (c_cov_rec cf cg) (Nat.pair x i) := by sorry
@[simp] theorem c_cov_rec_evp_size : 0<(eval_prim O (c_cov_rec cf cg) (Nat.pair x i)).list_size := by
  unfold c_cov_rec
  simp [eval_prim]
  induction i
  · simp
  · simp
@[simp] theorem c_cov_rec_evp_0 : eval_prim O (c_cov_rec cf cg) (Nat.pair x (i+1)) = list_append (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) (  eval_prim O cg $ Nat.pair x $ Nat.pair i $ eval_prim O (c_cov_rec cf cg) (Nat.pair x i)    ) := by
  rw  [c_cov_rec]
  rw  [eval_prim]
  simp

  -- exact?
@[simp] theorem c_cov_rec_evp_1 : Nat.list_get (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) 0 = eval_prim O cf x.l := by
  induction i with
  | zero =>
    unfold c_cov_rec
    simp [eval_prim]
  | succ i h =>
    rw [(@c_cov_rec_evp_0 O cf cg x i)]
    have h0 := @c_cov_rec_evp_size O cf cg x i
    rw [←append_get h0]
    exact h


@[simp] theorem c_cov_rec_evp_2 (h:j≤i): Nat.list_get (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) j =  Nat.list_get_last (eval_prim O (c_cov_rec cf cg) (Nat.pair x j)):= by
  sorry

@[simp] theorem c_cov_rec_evp_3 : Nat.list_get_last (eval_prim O (c_cov_rec cf cg) (Nat.pair x (i+1))) = (  eval_prim O cg $ Nat.pair x $ Nat.pair i $ eval_prim O (c_cov_rec cf cg) (Nat.pair x i)    ) := by
  rw [c_cov_rec_evp_0]
  simp only [list_get_last_append]

end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.div:Nat.PrimrecIn O Nat.div := by ...
-- theorem Nat.Primrec.div:Nat.Primrec Nat.div := by ...
end cov_rec






section div
namespace Nat.RecursiveIn.Code
-- def c_div_flip_aux := c_ifz.comp $ pair left $ pair (c_const (Nat.list_append Nat.list_empty 0)) $ c_cov_rec (c_const (Nat.list_empty)) $ c_mul.comp $ pair (c_sg.comp $ c_sub.comp $ pair (left.comp right) left) (succ.comp (c_l_get.comp $ pair (right.comp right) (c_sub.comp $ pair (left.comp right) left)))
def c_div_flip_aux := c_ifz.comp $ pair left $ pair (c_const (Nat.list_append Nat.list_empty 0)) $ c_cov_rec (c_const 0) $ c_mul.comp $ pair (c_sg.comp $ c_sub.comp $ pair (succ.comp $ left.comp right) (c_pred.comp left)) (succ.comp (c_l_get.comp $ pair (right.comp right) (c_sub.comp $ pair (left.comp right) (c_pred.comp left))))
def c_div_flip := c_l_get_last.comp c_div_flip_aux
def c_div := c_div_flip.comp (pair right left)
-- @[simp] theorem c_div_flip_ev_pr:code_prim c_div_flip := by unfold c_div_flip; repeat (constructor; try simp)
def div_flip_aux : ℕ→ℕ→ℕ := fun d n => if d=0 then 0 else (if n<d then 0 else (div_flip_aux d (n-d))+1)

theorem div_flip_aux_eq_div_flip : div_flip_aux = (flip ((· / ·) : ℕ → ℕ → ℕ)) := by
  funext d n
  simp [flip]
  cases d
  · unfold div_flip_aux
    simp
  · expose_names
    induction' n using Nat.strong_induction_on with n h
    unfold div_flip_aux
    simp
    cases Nat.lt_or_ge (n) (n_1+1) with
    | inl h2 =>
      simp [h2]
      exact Eq.symm (div_eq_of_lt h2)
    | inr h2 =>
      rw [h]
      simp [Nat.not_lt.mpr h2]
      have h3 : (n-(n_1+1)*1)/(n_1+1) = n/(n_1+1)-1 := by exact sub_mul_div n (n_1 + 1) 1
      have h4 : 0 < n/(n_1+1)  := by
        apply Nat.div_pos_iff.mpr
        constructor
        · exact zero_lt_succ n_1
        · exact h2
      have h5 : (n-(n_1+1)*1)/(n_1+1) +1 = n/(n_1+1) := by exact Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) h4 (_root_.id (Eq.symm h3)))
      simp at h5
      exact h5
      simp
      exact zero_lt_of_lt h2


theorem c_div_flip_evp_aux:eval_prim O c_div_flip = unpaired div_flip_aux := by
  funext dn
  let d:=dn.l
  let n:=dn.r
  have dn_eq : dn = Nat.pair d n := by exact Eq.symm (pair_unpair dn)
  rw [dn_eq]

  simp [c_div_flip, c_div_flip_aux]
  simp [eval_prim]
  cases d with
  | zero =>
    simp
    rw [div_flip_aux_eq_div_flip]
    simp [flip]
  | succ d' =>
    expose_names
    simp
    induction' n using Nat.strong_induction_on with n h
    unfold div_flip_aux


    cases n with
    | zero =>
      simp
      simp [c_cov_rec]
      simp [eval_prim]
    | succ n' =>
      expose_names
      rw [c_cov_rec_evp_3]
      simp [eval_prim]
      cases Nat.lt_or_ge (n') (d') with
      | inl h2 =>
        simp [h2]
        exact Nat.sub_eq_zero_of_le h2
      | inr h2 =>
        simp [Nat.not_lt.mpr h2]
        have h4 : n' + 1 > d' := by exact lt_add_one_of_le h2
        have h3 : n' + 1 - d' > 0 := by exact zero_lt_sub_of_lt h4
        have h5 : ¬ (n' + 1 - d'=0) := by exact Nat.sub_ne_zero_iff_lt.mpr h4
        simp only [h5, ↓reduceIte]
        simp only [Nat.add_right_cancel_iff]
        -- have h6 : (n' - (d' + 1)) < n'+1 := by exact sub_lt_succ n' (d' + 1)
        have h8 : (d' + 1) > 0 := by exact zero_lt_succ d'
        have h7 : (n'-d') < n'+1 := by exact sub_lt_succ n' d'
        rw [h (n'-d') h7]

@[simp] theorem c_div_flip_evp:eval_prim O c_div_flip = unpaired (flip ((· / ·) : ℕ → ℕ → ℕ)) := by
  rw [c_div_flip_evp_aux]
  simp [div_flip_aux_eq_div_flip]
theorem c_div_evp : eval_prim O c_div = unpaired Nat.div := by
  unfold c_div
  simp [eval_prim]
  simp [flip]
  exact rfl

theorem c_div_flip_aux_ev_pr :code_prim c_div_flip_aux := by
  unfold c_div_flip_aux;
  repeat (constructor; try simp)


  
theorem c_div_ev_pr :code_prim c_div := by
  unfold c_div;
  repeat (constructor; try simp)

@[simp] theorem c_div_ev:eval O c_div = unpaired Nat.div := by rw [← eval_prim_eq_eval c_div_ev_pr]; simp only [c_div_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.div:Nat.PrimrecIn O Nat.div := by ...
-- theorem Nat.Primrec.div:Nat.Primrec Nat.div := by ...
end div
















/-- Given a total choice function `c`, returns `a` or `b` conditioning on whether `c x=0`. -/
theorem Nat.RecursiveIn.ifz1 {O:ℕ→ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c): Nat.RecursiveIn O (fun x => if (c x=0) then (a:ℕ) else (b:ℕ):ℕ→ℕ) := by
  let construction := fun x =>
    Nat.add
    (Nat.mul b (Nat.sg (c x)))
    (Nat.mul a (Nat.sg' (c x)))
  have consRecin:Nat.RecursiveIn O construction := by
    simp only [construction]
    apply Nat.RecursiveIn.totalComp₂
    · apply of_primrec Nat.Primrec.add
    · apply Nat.RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const b)
      · apply Nat.RecursiveIn.totalComp'
        · exact of_primrec Nat.Primrec.sg
        · exact hc
    · apply Nat.RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const a)
      · apply Nat.RecursiveIn.totalComp'
        · exact of_primrec Nat.Primrec.sg'
        · exact hc
  have consEq: (fun x => if (c x=0) then (a:ℕ) else (b:ℕ):ℕ→ℕ) = construction := by
    simp [construction]
    funext xs
    cases Classical.em (c xs = 0) with -- do i really need classical.em here?
      | inl h => simp [h]
      | inr h => simp [h]

  rw [consEq]
  exact consRecin

theorem Nat.RecursiveIn.ite {O:ℕ→ℕ} {f g:ℕ→.ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c) (hf:Nat.RecursiveIn O f) (hg:Nat.RecursiveIn O g):Nat.RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
    have exists_index_for_f:∃ c:ℕ, eval O c = f := by exact exists_code_nat.mp hf
    have exists_index_for_g:∃ c:ℕ, eval O c = g := by exact exists_code_nat.mp hg
    rcases exists_index_for_f with ⟨index_f,index_f_is_f⟩
    rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

    have main2:(fun a => if (c a=0) then (f a) else (g a)) = fun a => Nat.pair (if c a=0 then (index_f) else (index_g)) a >>= eval₁ O := by
      funext xs
      cases Classical.em (c xs = 0) with
      | inl h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval₁, Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_f_is_f)) xs
      | inr h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval₁, Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_g_is_g)) xs
    rw [main2]


    apply Nat.RecursiveIn.evalRecInO'
    apply Nat.RecursiveIn.someTotal

    rw [Nat.RecursiveIn.pair']

    apply Nat.RecursiveIn.pair
    · simp only [Part.coe_some]
      apply Nat.RecursiveIn.ifz1
      exact hc
    exact id
