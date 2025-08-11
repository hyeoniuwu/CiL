import Computability.RecursiveInTheorems

set_option profiler true
-- set_option profiler.threshold 30

open Nat.RecursiveIn.Code

section comp₂
namespace Nat.RecursiveIn.Code
@[simp] def comp₂ : Code→Code→Code→Code := fun c1 c2 c3 => c1.comp (pair c2 c3)
theorem comp₂_ev_pr (hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3) :code_prim (comp₂ c1 c2 c3) := by
  unfold comp₂;
  constructor
  exact hc1
  constructor
  exact hc2
  exact hc3
-- theorem comp₂_evp:eval_prim O (comp₂ c1 c2 c3) x = eval_prim O c1 (Nat.pair (eval_prim O (c2) x) (eval_prim O (c3) x))  := by simp [comp₂,eval_prim];
theorem comp₂_evp:eval_prim O (comp₂ c1 c2 c3) = fun x => eval_prim O c1 (Nat.pair (eval_prim O (c2) x) (eval_prim O (c3) x))  := by simp [comp₂,eval_prim];
-- <$> x <*>
-- @[simp] theorem comp₂_ev(hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3):eval O (comp₂ c1 c2 c3) = fun x => (Nat.pair <$> (eval O (c2) x) <*> (eval O (c3) x)) >>= (eval O c1) := by
  -- rw [← eval_prim_eq_eval (comp₂_ev_pr hc1 hc2 hc3)]; simp only [comp₂_evp]

end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.comp₂:Nat.PrimrecIn O Nat.comp₂ := by ...
-- theorem Nat.Primrec.comp₂:Nat.Primrec Nat.comp₂ := by ...
end comp₂

section id
namespace Nat.RecursiveIn.Code
def c_id := left.pair right
@[simp] theorem c_id_ev_pr:code_prim c_id := by unfold c_id; repeat (first|assumption|simp|constructor)
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
@[simp] theorem c_sg_ev_pr:code_prim c_sg := by unfold c_sg; repeat (first|assumption|simp|constructor)
@[simp] theorem c_sg_evp:eval_prim O c_sg = Nat.sg := by
  simp [c_sg,eval_prim]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp] theorem c_sg_ev : eval O c_sg = Nat.sg := by rw [← eval_prim_eq_eval c_sg_ev_pr]; simp only [c_sg_evp]
def c_sg' := comp (prec (c_const 1) (((zero).comp left).comp left)) (pair zero c_id)
@[simp] theorem c_sg'_ev_pr:code_prim c_sg' := by unfold c_sg'; repeat (first|assumption|simp|constructor)
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

@[simp] abbrev c_not := c_sg'

end sgsg'


section add
namespace Nat.RecursiveIn.Code
def c_add := (prec c_id ((succ.comp right).comp right))
@[simp] theorem c_add_ev_pr:code_prim c_add := by unfold c_add; repeat (first|assumption|simp|constructor)
@[simp] theorem c_add_evp:eval_prim O c_add = unpaired2 Nat.add := by
  simp [c_add,eval_prim]
  funext n;
  simp [unpaired2]
  induction n.r with
  | zero => exact rfl
  | succ n h => exact Nat.add_left_inj.mpr h
@[simp] theorem c_add_ev:eval O c_add = unpaired2 Nat.add := by rw [← eval_prim_eq_eval c_add_ev_pr]; simp only [c_add_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.add:Nat.PrimrecIn O Nat.add := by ...
-- theorem Nat.Primrec.add:Nat.Primrec Nat.add := by ...
end add
section mul
namespace Nat.RecursiveIn.Code
def c_mul := prec zero (c_add.comp (pair left (right.comp right)))
@[simp] theorem c_mul_ev_pr:code_prim c_mul := by unfold c_mul; repeat (first|assumption|simp|constructor)
@[simp] theorem c_mul_evp:eval_prim O c_mul = unpaired2 Nat.mul := by
  simp [c_mul,eval_prim]
  funext n;
  simp [unpaired2]
  induction n.r with
  | zero => exact rfl
  | succ n h =>
    simp [*, mul_succ];
    (expose_names; exact Nat.add_comm (unpair n_1).1 ((unpair n_1).1 * n))
@[simp] theorem c_mul_ev:eval O c_mul = unpaired2 Nat.mul := by rw [← eval_prim_eq_eval c_mul_ev_pr]; simp only [c_mul_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.mul:Nat.PrimrecIn O Nat.mul := by ...
-- theorem Nat.Primrec.mul:Nat.Primrec Nat.mul := by ...
end mul
section pow
namespace Nat.RecursiveIn.Code
def c_pow := prec (c_const 1) (c_mul.comp (pair (right.comp right) left))
@[simp] theorem c_pow_ev_pr:code_prim c_pow := by unfold c_pow; repeat (first|assumption|simp|constructor)
@[simp] theorem c_pow_evp:eval_prim O c_pow = unpaired2 Nat.pow := by
  simp [c_pow,eval_prim]
  funext n;
  simp [unpaired2]

  induction n.r with
  | zero => exact rfl
  | succ n h => simp [*, pow_succ];
@[simp] theorem c_pow_ev:eval O c_pow = unpaired2 Nat.pow := by rw [← eval_prim_eq_eval c_pow_ev_pr]; simp only [c_pow_evp]
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
@[simp] theorem c_pred_ev_pr:code_prim c_pred := by unfold c_pred; repeat (first|assumption|simp|constructor)
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
@[simp] theorem c_sub_ev_pr:code_prim c_sub := by unfold c_sub; repeat (first|assumption|simp|constructor)
@[simp] theorem c_sub_evp:eval_prim O c_sub = unpaired2 Nat.sub := by
  simp [c_sub,eval_prim]
  funext n;
  simp [unpaired2]
  induction n.r with
  | zero => exact rfl
  | succ n h =>
    simp [*, Nat.sub_add_eq];
@[simp] theorem c_sub_ev:eval O c_sub = unpaired2 Nat.sub := by rw [← eval_prim_eq_eval c_sub_ev_pr]; simp only [c_sub_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.sub:Nat.PrimrecIn O Nat.sub := by ...
-- theorem Nat.Primrec.sub:Nat.Primrec Nat.sub := by ...
end sub
section dist
namespace Nat.RecursiveIn.Code
def c_dist := c_add.comp (pair c_sub (c_sub.comp (pair right left)))
@[simp] theorem c_dist_ev_pr:code_prim c_dist := by unfold c_dist; repeat (first|assumption|simp|constructor)
@[simp] theorem c_dist_evp:eval_prim O c_dist = unpaired2 Nat.dist := by simp [c_dist,eval_prim]; exact rfl
@[simp] theorem c_dist_ev:eval O c_dist = unpaired2 Nat.dist := by rw [← eval_prim_eq_eval c_dist_ev_pr]; simp only [c_dist_evp]
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
/-- eval c_if_eq' (x,y) = [x=y] -/
def c_if_eq' := c_sg.comp c_dist
@[simp] theorem c_if_eq'_ev_pr:code_prim c_if_eq' := by unfold c_if_eq'; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_eq'_evp:eval_prim O c_if_eq' = fun ab => if ab.l=ab.r then 0 else 1 := by simp [c_if_eq',eval_prim];
@[simp] theorem c_if_eq'_ev:eval O c_if_eq' = fun ab => if ab.l=ab.r then 0 else 1 := by
  rw [← eval_prim_eq_eval c_if_eq'_ev_pr]; simp only [c_if_eq'_evp]; funext xs; exact apply_ite Part.some (xs.l = xs.r) 0 1
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_eq':Nat.PrimrecIn O Nat.if_eq' := by ...
-- theorem Nat.Primrec.if_eq':Nat.Primrec Nat.if_eq' := by ...
end if_eq'



section comp₄
namespace Nat.RecursiveIn.Code
@[simp] def comp₄ : Code→Code→Code→Code→Code→Code := fun c1 c2 c3 c4 c5 => c1.comp₂ (pair c2 c3) (pair c4 c5)
theorem comp₄_ev_pr (hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3) (hc4:code_prim c4) (hc5:code_prim c5):code_prim (comp₄ c1 c2 c3 c4 c5) := by
  unfold comp₄;
  repeat (first|assumption|simp|constructor)
theorem comp₄_evp:eval_prim O (comp₄ c1 c2 c3 c4 c5) x=
  eval_prim O c1 (Nat.pair (Nat.pair (eval_prim O (c2) x) (eval_prim O (c3) x)) ((Nat.pair (eval_prim O (c4) x) (eval_prim O (c5) x)))) := by
  simp [comp₄,eval_prim];
-- <$> x <*>
-- @[simp] theorem comp₄_ev(hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3):eval O (comp₄ c1 c2 c3) = fun x => (Nat.pair <$> (eval O (c2) x) <*> (eval O (c3) x)) >>= (eval O c1) := by
  -- rw [← eval_prim_eq_eval (comp₄_ev_pr hc1 hc2 hc3)]; simp only [comp₄_evp]

end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.comp₄:Nat.PrimrecIn O Nat.comp₄ := by ...
-- theorem Nat.Primrec.comp₄:Nat.Primrec Nat.comp₄ := by ...
end comp₄
section comp₃
namespace Nat.RecursiveIn.Code
@[simp] def comp₃ : Code→Code→Code→Code→Code := fun c1 c2 c3 c4 => c1.comp₂ c2 (pair c3 c4)
theorem comp₃_ev_pr (hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3) (hc4:code_prim c4) (hc5:code_prim c5):code_prim (comp₃ c1 c2 c3 c4) := by
  unfold comp₃;
  repeat (first|assumption|simp|constructor)
theorem comp₃_evp:eval_prim O (comp₃ c1 c2 c3 c4) x=
  eval_prim O c1 (Nat.pair (eval_prim O (c2) x) ((Nat.pair (eval_prim O (c3) x) (eval_prim O (c4) x)))) := by
  simp [comp₃,eval_prim];
-- <$> x <*>
-- @[simp] theorem comp₃_ev(hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3):eval O (comp₃ c1 c2 c3) = fun x => (Nat.pair <$> (eval O (c2) x) <*> (eval O (c3) x)) >>= (eval O c1) := by
  -- rw [← eval_prim_eq_eval (comp₃_ev_pr hc1 hc2 hc3)]; simp only [comp₃_evp]

end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.comp₃:Nat.PrimrecIn O Nat.comp₃ := by ...
-- theorem Nat.Primrec.comp₃:Nat.Primrec Nat.comp₃ := by ...
end comp₃



section if_eq_te
namespace Nat.RecursiveIn.Code
/-- eval c_if_eq_te (x,y) = [x=y] -/
def c_if_eq_te :=
  let eq := c_if_eq'.comp₂ (left.comp left) (right.comp left);
  c_add.comp₂
  (c_mul.comp₂ eq (right.comp right))
  (c_mul.comp₂ (c_not.comp eq) (left.comp right))
@[simp] theorem c_if_eq_te_ev_pr:code_prim c_if_eq_te := by unfold c_if_eq_te; repeat (first|assumption|simp|constructor)


@[simp] theorem c_if_eq_te_evp:eval_prim O c_if_eq_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a=b then c else d := by
  simp [c_if_eq_te,eval_prim];
  cases Classical.em (a=b) with
  | inl h => simp [h]
  | inr h => simp [h]
@[simp] theorem c_if_eq_te_ev:eval O c_if_eq_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a=b then c else d  := by
  rw [← eval_prim_eq_eval c_if_eq_te_ev_pr];
  simp
theorem c_if_eq_te_evp':eval_prim O c_if_eq_te = fun x => if x.l.l=x.l.r then x.r.l else x.r.r := by
  simp [c_if_eq_te,eval_prim];
  funext xs
  cases Classical.em (xs.l.l=xs.l.r) with
  | inl h => simp [h]
  | inr h => simp [h]
theorem c_if_eq_te_ev':eval O c_if_eq_te = fun x => if x.l.l=x.l.r then x.r.l else x.r.r := by
  rw [← eval_prim_eq_eval c_if_eq_te_ev_pr]; simp only [c_if_eq_te_evp']; funext xs;
  cases Classical.em (xs.l.l=xs.l.r) with
  | inl h => simp [h]
  | inr h => simp [h]

-- the simp normal form.
-- @[simp] theorem c_if_eq_te_evp_simp:eval_prim O (c_if_eq_te.comp₄ c1 c2 c3 c4) x
--   =
-- if (eval_prim O c1 x)=(eval_prim O c2 x) then (eval_prim O c3 x) else (eval_prim O c4 x) := by simp


end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_eq_te:Nat.PrimrecIn O Nat.if_eq_te := by ...
-- theorem Nat.Primrec.if_eq_te:Nat.Primrec Nat.if_eq_te := by ...
end if_eq_te
section if_lt_te
namespace Nat.RecursiveIn.Code
/-- eval c_if_lt_te (x,y) = [x<y] -/
def c_if_lt_te :=
  let lt := c_sg.comp $ c_sub.comp₂ (succ.comp $ left.comp left) (right.comp left);

  c_add.comp₂
  (c_mul.comp₂ lt (right.comp right))
  (c_mul.comp₂ (c_not.comp lt) (left.comp right))
@[simp] theorem c_if_lt_te_ev_pr:code_prim c_if_lt_te := by unfold c_if_lt_te; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_lt_te_evp:eval_prim O c_if_lt_te = fun x => if x.l.l<x.l.r then x.r.l else x.r.r := by
  simp [c_if_lt_te,eval_prim];
  funext xs
  cases Classical.em (xs.l.l<xs.l.r) with
  | inl h => simp [h, Nat.sub_eq_zero_of_le h]
  | inr h =>
    have h1: xs.l.l+1-xs.l.r>0 := by exact tsub_pos_iff_not_le.mpr h
    have h0: ¬(xs.l.l+1-xs.l.r=0) := by exact Nat.ne_zero_of_lt h1
    simp [h, h0]
@[simp] theorem c_if_lt_te_ev:eval O c_if_lt_te = fun x => if x.l.l<x.l.r then x.r.l else x.r.r := by
  rw [← eval_prim_eq_eval c_if_lt_te_ev_pr]; simp only [c_if_lt_te_evp]; funext xs;
  cases Classical.em (xs.l.l<xs.l.r) with
  | inl h => simp [h, Nat.sub_eq_zero_of_le h]
  | inr h =>
    have h1: xs.l.l+1-xs.l.r>0 := by exact tsub_pos_iff_not_le.mpr h
    have h0: ¬(xs.l.l+1-xs.l.r=0) := by exact Nat.ne_zero_of_lt h1
    simp [h, h0]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_lt_te:Nat.PrimrecIn O Nat.if_lt_te := by ...
-- theorem Nat.Primrec.if_lt_te:Nat.Primrec Nat.if_lt_te := by ...
end if_lt_te



section if_le_te
namespace Nat.RecursiveIn.Code
-- we use the fact that `a<b+1 ↔ a≤b`.
/-- eval c_if_le_te (x,y) = [x≤y] -/
def c_if_le_te := c_if_lt_te.comp (pair (pair (left.comp left) (succ.comp $ right.comp left)) right)
@[simp] theorem c_if_le_te_ev_pr:code_prim c_if_le_te := by unfold c_if_le_te; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_le_te_evp:eval_prim O c_if_le_te = fun x => if x.l.l≤x.l.r then x.r.l else x.r.r := by
  simp [c_if_le_te,eval_prim];
  funext xs
  cases Classical.em (xs.l.l<xs.l.r+1) with
  | inl h => simp [h, Nat.lt_add_one_iff.mp h]
  | inr h => simp [h, Nat.lt_add_one_iff.not.mp h]
@[simp] theorem c_if_le_te_ev:eval O c_if_le_te = fun x => if x.l.l≤x.l.r then x.r.l else x.r.r := by
  rw [← eval_prim_eq_eval c_if_le_te_ev_pr]; simp only [c_if_le_te_evp]; funext xs;
  cases Classical.em (xs.l.l<xs.l.r+1) with
  | inl h => simp [h, Nat.lt_add_one_iff.mp h]
  | inr h => simp [h, Nat.lt_add_one_iff.not.mp h]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_le_te:Nat.PrimrecIn O Nat.if_le_te := by ...
-- theorem Nat.Primrec.if_le_te:Nat.Primrec Nat.if_le_te := by ...
end if_le_te

section ifz
namespace Nat.RecursiveIn.Code
def c_ifz := c_add.comp $ pair (c_mul.comp $ pair (c_sg'.comp left) (left.comp right)) (c_mul.comp $ pair (c_sg.comp left) (right.comp right))
@[simp] theorem c_ifz_ev_pr:code_prim c_ifz := by unfold c_ifz; repeat (first|assumption|simp|constructor)
@[simp] theorem c_ifz_evp:eval_prim O c_ifz = fun (cab:ℕ) => if cab.l=0 then cab.r.l else cab.r.r := by
  simp [c_ifz,eval_prim];
  funext xs
  have hsplit : xs.l = 0 ∨ ¬ (xs.l = 0) := by exact Or.symm (ne_or_eq xs.l 0)
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
-- @[simp] theorem c_ef_ev_pr:code_prim $ c_ef c := by unfold c_ef; repeat (first|assumption|simp|constructor)
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


section efl_prec
namespace Nat.RecursiveIn.Code
/--
A specialised code used as an auxiliary for `c_cov_rec`.
Given an input of the form (x, (i, list)), the code (c_efl_prec c) computes list.append (eval c input).
(The form above is what you would expect in the inductive case in primitive recursion.)
-/
def c_efl_prec:=fun c=>c_l_append.comp (pair (c_id.comp (right.comp right)) c)
-- def c_efl_prec:=fun c=>c_l_append.comp₂ (c_id.comp (right.comp right)) c
@[simp] theorem c_efl_prec_ev_pr (h:code_prim c):code_prim $ c_efl_prec c := by unfold c_efl_prec; repeat (first|assumption|simp|constructor)
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




-- course of values recursion.
section cov_rec
namespace Nat.RecursiveIn.Code
/-
eval_prim O (c_cov_rec cf cg) (Nat.pair x i)
should be the list of all values of
eval_prim O (c_cov_rec cf cg) (Nat.pair x j)
for j=0 to i-1.
-/
/--
Code for course-of-values recursion.

base case:      `eval (c_cov_rec cf cg) (x 0)` = list with one element, eval cf x

inductive case: Let `l` be the list of previous values, from `j=0` to `i`
                Then `eval (c_cov_rec cf cg) (x i+1) = l.append (eval cg (x (i l)))`
-/
def c_cov_rec (cf cg:Code):= prec (c_l_append.comp₂ (c_const Nat.list_empty) (cf)) $ c_efl_prec cg
@[simp] theorem c_cov_rec_evp_size_positive : 0<(eval_prim O (c_cov_rec cf cg) (Nat.pair x i)).list_size := by
  unfold c_cov_rec
  simp [eval_prim]
  induction i
  · simp
  · simp
@[simp] theorem c_cov_rec_evp_size : (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)).list_size = i+1 := by
  unfold c_cov_rec
  simp [eval_prim]
  induction i
  · simp; exact rfl
  · simp; (expose_names; exact h)
theorem c_cov_rec_evp_0 : eval_prim O (c_cov_rec cf cg) (Nat.pair x (i+1)) = list_append (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) (  eval_prim O cg $ Nat.pair x $ Nat.pair i $ eval_prim O (c_cov_rec cf cg) (Nat.pair x i)    ) := by
  rw  [c_cov_rec]
  rw  [eval_prim]
  simp
@[simp] theorem c_cov_rec_evp_4 : Nat.list_get_last (eval_prim O (c_cov_rec cf cg) (Nat.pair x 0)) = eval_prim O cf x := by
  unfold c_cov_rec
  simp [eval_prim]
@[simp] theorem c_cov_rec_evp_1 : Nat.list_get (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) 0 = eval_prim O cf x := by
  induction i with
  | zero =>
    unfold c_cov_rec
    simp [eval_prim]
  | succ i h =>
    rw [(@c_cov_rec_evp_0 O cf cg x i)]
    have h0 := @c_cov_rec_evp_size_positive O cf cg x i
    rw [←append_get h0]
    exact h

@[simp] theorem c_cov_rec_evp_3 : Nat.list_get_last (eval_prim O (c_cov_rec cf cg) (Nat.pair x (i+1))) = (  eval_prim O cg $ Nat.pair x $ Nat.pair i $ eval_prim O (c_cov_rec cf cg) (Nat.pair x i)    ) := by
  rw [c_cov_rec_evp_0]
  simp only [list_get_last_append]

theorem c_cov_rec_evp_2_aux1 :
  Nat.list_get_last (eval_prim O (c_cov_rec cf cg) (Nat.pair x i))
    =
  Nat.list_get (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) i := by
  simp [list_get_last]
  simp [list_get]
  simp [list_get_lastn]
  simp [list_get_last_aux]
theorem c_cov_rec_evp_2_aux2 (h:j≤i) :
  Nat.list_get (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) j
    =
  Nat.list_get (eval_prim O (c_cov_rec cf cg) (Nat.pair x (i+1))) j
  := by
  simp [c_cov_rec_evp_0]
  apply append_get
  simp
  exact lt_add_one_of_le h

@[simp] theorem c_cov_rec_evp_2 (h:j≤i): Nat.list_get (eval_prim O (c_cov_rec cf cg) (Nat.pair x i)) j =  Nat.list_get_last (eval_prim O (c_cov_rec cf cg) (Nat.pair x j)):= by
  rw [c_cov_rec_evp_2_aux1]
  induction i with
  | zero => rw [show j=0 from eq_zero_of_le_zero h]
  | succ n ih =>
    have h0: j=n+1 ∨ j≤n := by exact Or.symm (le_or_eq_of_le_succ h)
    cases h0 with
    | inl h1 => rw [h1]
    | inr h1 =>
      have h2 := ih h1
      rw [←h2]
      rw [←c_cov_rec_evp_2_aux2]
      exact h1

end Nat.RecursiveIn.Code
end cov_rec






section div
def div_flip_aux : ℕ→ℕ→ℕ := fun d n => if d=0 then 0 else (if n<d then 0 else (div_flip_aux d (n-d))+1)
open Nat in
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

namespace Nat.RecursiveIn.Code
/-
This example serves as a blueprint for using `c_cov_rec` in proofs.

For this specific example, one can bypass defining the auxiliary function `c_div_flip_aux` and write a shorter proof; see https://github.com/hyeoniuwu/CiL/blob/99fd356e7835d1856fb73306df7828f96b42a85c/Computability/Constructions.lean#L758.

However, I've written the "longer" way, which is more efficient. For more complex constructions, this longer way becomes necessary.

The reason for explicitly defining the auxiliary function (the function without c_l_get_last.comp attached) is to be able to rewrite the
"unfolded" definitions in the recursive case with the shorter function name.
-/
def c_div_flip_aux :=
  let dividend := succ.comp $ left.comp right
  let divisor := left
  let list_of_prev_values := right.comp right

  c_cov_rec

  (c_const 0) $            -- base case: if dividend is 0, return 0

  c_ifz.comp₂ divisor $    -- in general, test if the divisor is zero
  pair (c_const 0) $       -- if so, return 0
  c_if_lt_te.comp₄ dividend divisor (c_const 0) $ -- if dividend < divisor, return 0
  (succ.comp (c_l_get.comp₂ list_of_prev_values (c_sub.comp₂ dividend divisor))) -- else return (dividend-divisor)/divisor+1
def c_div_flip := c_l_get_last.comp c_div_flip_aux
def c_div := c_div_flip.comp (pair right left)
-- i want the inductive case to be simplified to an expression involving c_div_flip2.
-- this cannot be done after unfolding c_div_flip2, as that will destroy all 'c_div_flip2' 's.
-- not sure how to do it automatically. in the meanwhile, i can explicitly define it, like below:


theorem c_div_flip_evp_aux_aux :
  eval_prim O c_div_flip (Nat.pair (d+1) (n+1))
    =
  if n<d then 0 else eval_prim O c_div_flip (Nat.pair (d+1) (n-d)) + 1
    := by

  unfold c_div_flip; simp only [eval_prim, c_l_get_last_evp] -- unwrap the list_get_last wrapper

  -- now we rewrite the expr just until it contains the expression for the list of previous calculations
  rw (config := {occs := .pos [1]}) [c_div_flip_aux]
  simp only [c_cov_rec_evp_3]

  -- we then "refold" the list of previous calculations in terms of the function
  rw [←c_div_flip_aux]

  -- now we can simplify the expression, without meddling with the internals of the list of previous calculations
  simp [eval_prim]

  -- to each call of a previous value, we rewrite to its eval_prim O c (previous value) by using c_cov_rec_evp_2
  have h0: n-d≤n := by exact sub_le n d
  unfold c_div_flip_aux
  rw [c_cov_rec_evp_2 h0]



theorem c_div_flip_evp_aux:eval_prim O c_div_flip = unpaired2 div_flip_aux := by
  funext dn
  let d:=dn.l
  let n:=dn.r
  have dn_eq : dn = Nat.pair d n := by exact Eq.symm (pair_unpair dn)
  rw [dn_eq]

  induction' n using Nat.strong_induction_on with n ih

  cases n with
  | zero =>
    simp [div_flip_aux_eq_div_flip,flip]
    simp [c_div_flip, c_div_flip_aux, eval_prim]
  | succ n' =>
    cases hd:d with
    | zero =>
      simp [div_flip_aux_eq_div_flip,flip]
      simp [c_div_flip, c_div_flip_aux, eval_prim]
    | succ d' =>
      rw [c_div_flip_evp_aux_aux]
      unfold div_flip_aux; simp
      rw [hd] at ih
      have h7 : (n'-d') < n'+1 := by exact sub_lt_succ n' d'
      rw [ih (n'-d') h7]
      unfold div_flip_aux; simp


@[simp] theorem c_div_flip_evp:eval_prim O c_div_flip = unpaired2 (flip ((· / ·) : ℕ → ℕ → ℕ)) := by
  rw [c_div_flip_evp_aux]
  simp [div_flip_aux_eq_div_flip]
@[simp] theorem c_div_evp : eval_prim O c_div = unpaired2 ((· / ·) : ℕ → ℕ → ℕ) := by
  unfold c_div
  simp [eval_prim]
  simp [flip]


@[simp] theorem c_div_ev_pr :code_prim c_div := by
  unfold c_div;
  repeat (first|assumption|simp|constructor)

@[simp] theorem c_div_ev:eval O c_div = unpaired2 Nat.div := by rw [← eval_prim_eq_eval c_div_ev_pr]; simp only [c_div_evp]; exact rfl
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.div:Nat.PrimrecIn O Nat.div := by ...
-- theorem Nat.Primrec.div:Nat.Primrec Nat.div := by ...
end div





section mod
namespace Nat.RecursiveIn.Code
def c_mod := c_sub.comp₂ left (c_mul.comp₂ right c_div)
@[simp] theorem c_mod_ev_pr:code_prim c_mod := by unfold c_mod; repeat (first|assumption|simp|constructor)
@[simp] theorem c_mod_evp:eval_prim O c_mod = unpaired2 ((· % ·) : ℕ → ℕ → ℕ) := by
  simp [c_mod,eval_prim];

  funext mn
  let m:=mn.l
  let n:=mn.r
  have mn_eq : mn = Nat.pair m n := by exact Eq.symm (pair_unpair mn)
  rw [mn_eq]

  apply Nat.sub_eq_of_eq_add
  simp [add_comm (m % n), Nat.div_add_mod]


@[simp] theorem c_mod_ev:eval O c_mod = unpaired2 ((· % ·) : ℕ → ℕ → ℕ) := by rw [← eval_prim_eq_eval c_mod_ev_pr]; simp only [c_mod_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.mod:Nat.PrimrecIn O Nat.mod := by ...
-- theorem Nat.Primrec.mod:Nat.Primrec Nat.mod := by ...
end mod



-- We define interpretations of naturals as finite strings on the alphabet {0,1}.
-- (l,b) is interpreted as the string of length l, whose sequence matches with the binary representation of b.

section BSMem
/-- `BSMem (x,(l,b)) = [x∈Dₐ]` (iversion brackets) -/
def Nat.BSMem : ℕ→ℕ := fun xa => if Nat.testBit xa.r.r xa.l then 1 else 0
theorem BSMem_eq_BSMem_aux : Nat.BSMem = fun xa => xa.r.r % (2^xa.l) := by sorry
namespace Nat.RecursiveIn.Code

#eval BSMem (Nat.pair 1 (Nat.pair 5 0b01000))
#eval BSMem (Nat.pair 2 (Nat.pair 5 0b01000))
#eval BSMem (Nat.pair 3 (Nat.pair 5 0b01000))

def c_BSMem := c_mod.comp₂ (right.comp right) (c_pow.comp₂ (c_const 2) left)
@[simp] theorem c_BSMem_ev_pr:code_prim c_BSMem := by unfold c_BSMem; repeat (first|assumption|simp|constructor)
@[simp] theorem c_BSMem_evp:eval_prim O c_BSMem = Nat.BSMem := by
  simp [c_BSMem,eval_prim]
  rw [BSMem_eq_BSMem_aux]
@[simp] theorem c_BSMem_ev:eval O c_BSMem = Nat.BSMem := by rw [← eval_prim_eq_eval c_BSMem_ev_pr]; simp only [c_BSMem_evp]
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.BSMem:Nat.PrimrecIn O Nat.BSMem := by rw [← c_BSMem_evp]; apply code_prim_prop c_BSMem_ev_pr
theorem Nat.Primrec.BSMem:Nat.Primrec Nat.BSMem := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.BSMem
end BSMem

section BSUnion
def Nat.BSUnion : ℕ→ℕ := fun bl1bl2 => Nat.pair (Nat.max bl1bl2.l.l bl1bl2.r.l) (Nat.lor bl1bl2.l.r bl1bl2.r.r)
theorem BSUnion_eq_BSUnion_aux : Nat.BSUnion = fun xa => xa.r.r % (2^xa.l) := by sorry
namespace Nat.RecursiveIn.Code
def c_BSUnion := c_mod.comp₂ (right.comp right) (c_pow.comp₂ (c_const 2) left)
@[simp] theorem c_BSUnion_ev_pr:code_prim c_BSUnion := by unfold c_BSUnion; repeat (first|assumption|simp|constructor)
@[simp] theorem c_BSUnion_evp:eval_prim O c_BSUnion = Nat.BSUnion := by
  simp [c_BSUnion,eval_prim]
  rw [BSUnion_eq_BSUnion_aux]
@[simp] theorem c_BSUnion_ev:eval O c_BSUnion = Nat.BSUnion := by rw [← eval_prim_eq_eval c_BSUnion_ev_pr]; simp only [c_BSUnion_evp]
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.BSUnion:Nat.PrimrecIn O Nat.BSUnion := by rw [← c_BSUnion_evp]; apply code_prim_prop c_BSUnion_ev_pr
theorem Nat.Primrec.BSUnion:Nat.Primrec Nat.BSUnion := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.BSUnion
end BSUnion

section BSSize
def Nat.BSSize : ℕ → ℕ
| 0     => 0
| (n+1) => (n+1)&&&1 + BSSize ((n+1)/2)
theorem BSSize_eq_BSSize_aux : Nat.BSSize = fun xa => xa.r.r % (2^xa.l) := by sorry
namespace Nat.RecursiveIn.Code



def c_BSSize := c_mod.comp₂ (right.comp right) (c_pow.comp₂ (c_const 2) left)
@[simp] theorem c_BSSize_ev_pr:code_prim c_BSSize := by unfold c_BSSize; repeat (first|assumption|simp|constructor)
@[simp] theorem c_BSSize_evp:eval_prim O c_BSSize = Nat.BSSize := by
  simp [c_BSSize,eval_prim]
  rw [BSSize_eq_BSSize_aux]
@[simp] theorem c_BSSize_ev:eval O c_BSSize = Nat.BSSize := by rw [← eval_prim_eq_eval c_BSSize_ev_pr]; simp only [c_BSSize_evp]
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.BSSize:Nat.PrimrecIn O Nat.BSSize := by rw [← c_BSSize_evp]; apply code_prim_prop c_BSSize_ev_pr
theorem Nat.Primrec.BSSize:Nat.Primrec Nat.BSSize := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.BSSize
end BSSize





section mul2
namespace Nat.RecursiveIn.Code
def c_mul2 := c_mul.comp₂ c_id (c_const 2)
@[simp] theorem c_mul2_ev_pr:code_prim c_mul2 := by unfold c_mul2; repeat (first|assumption|simp|constructor)
@[simp] theorem c_mul2_evp:eval_prim O c_mul2 = fun x => x*2 := by simp [c_mul2]
@[simp] theorem c_mul2_ev:eval O c_mul2 = (fun x => x*(2:ℕ)) := by rw [← eval_prim_eq_eval c_mul2_ev_pr]; simp only [c_mul2_evp];
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.mul2:Nat.PrimrecIn O Nat.mul2 := by ...
-- theorem Nat.Primrec.mul2:Nat.Primrec Nat.mul2 := by ...
end mul2
section div2
namespace Nat.RecursiveIn.Code
def c_div2 := c_div.comp₂ c_id (c_const 2)
@[simp] theorem c_div2_ev_pr:code_prim c_div2 := by unfold c_div2; repeat (first|assumption|simp|constructor)
@[simp] theorem c_div2_evp:eval_prim O c_div2 = fun x => x/2 := by simp [c_div2]
@[simp] theorem c_div2_ev:eval O c_div2 = (fun x => x/(2:ℕ)) := by rw [← eval_prim_eq_eval c_div2_ev_pr]; simp only [c_div2_evp];
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.div2:Nat.PrimrecIn O Nat.div2 := by ...
-- theorem Nat.Primrec.div2:Nat.Primrec Nat.div2 := by ...
end div2







section replace_oracle
namespace Nat.RecursiveIn.Code
def encodeCode_replace_oracle (o:ℕ) : Code → ℕ
| Code.zero        => 0
| Code.succ        => 1
| Code.left        => 2
| Code.right       => 3
| Code.oracle      => o
| Code.pair cf cg  => 2*(2*(Nat.pair (encodeCode_replace_oracle o cf) (encodeCode_replace_oracle o cg))  )   + 5
| Code.comp cf cg  => 2*(2*(Nat.pair (encodeCode_replace_oracle o cf) (encodeCode_replace_oracle o cg))  )+1 + 5
| Code.prec cf cg  => 2*(2*(Nat.pair (encodeCode_replace_oracle o cf) (encodeCode_replace_oracle o cg))+1)   + 5
| Code.rfind' cf   => 2*(2*(encodeCode_replace_oracle o cf                            )+1)+1 + 5
def replace_oracle (o:ℕ) := fun n => (encodeCode_replace_oracle o (decodeCode n))




/-- `eval c_replace_oracle (o,code)` = `code` but with calls to oracle replaced with calls to code `o` -/
def c_replace_oracle_aux :=
-- def c_replace_oracle :=
  let o               := left
  let input_to_decode := succ.comp (left.comp right)
  let comp_hist       := right.comp right
  let n               := c_sub.comp₂ input_to_decode (c_const 5)
  let m               := c_div2.comp $ c_div2.comp n
  let ml              := c_l_get.comp₂ comp_hist (left.comp m)
  let mr              := c_l_get.comp₂ comp_hist (right.comp m)
  let mp              := c_l_get.comp₂ comp_hist m
  let nMod4           := c_mod.comp₂ n (c_const 4)
  let pair_code       := c_add.comp₂ (            c_mul2.comp $             c_mul2.comp (pair ml mr)) (c_const 5)
  let comp_code       := c_add.comp₂ (succ.comp $ c_mul2.comp $             c_mul2.comp (pair ml mr)) (c_const 5)
  let prec_code       := c_add.comp₂ (            c_mul2.comp $ succ.comp $ c_mul2.comp (pair ml mr)) (c_const 5)
  let rfind'_code     := c_add.comp₂ (succ.comp $ c_mul2.comp $ succ.comp $ c_mul2.comp mp          ) (c_const 5)

  -- c_l_get_last.comp $

  c_cov_rec

  (c_const 0) $

  c_if_eq_te.comp₄ input_to_decode (c_const 1) (c_const 1) $
  c_if_eq_te.comp₄ input_to_decode (c_const 2) (c_const 2) $
  c_if_eq_te.comp₄ input_to_decode (c_const 3) (c_const 3) $
  c_if_eq_te.comp₄ input_to_decode (c_const 4) o           $
  c_if_eq_te.comp₄ nMod4           (c_const 0) (pair_code) $
  c_if_eq_te.comp₄ nMod4           (c_const 1) (comp_code) $
  c_if_eq_te.comp₄ nMod4           (c_const 2) (prec_code) $
                                                rfind'_code
def c_replace_oracle := c_l_get_last.comp c_replace_oracle_aux
set_option maxRecDepth 5000 in
@[simp] theorem c_replace_oracle_ev_pr:code_prim (c_replace_oracle) := by
  unfold c_replace_oracle;
  repeat (first|assumption|simp|constructor)



-- expanding lets: ~70ms
-- not expanding lets: ~20ms
theorem c_replace_oracle_evp_aux (hx:x≤4): eval_prim O (c_replace_oracle) (Nat.pair o x) = replace_oracle o x := by
  unfold c_replace_oracle
  unfold c_replace_oracle_aux
  lift_lets
  extract_lets
  expose_names

  have hinput_to_decode {x hist} : eval_prim O input_to_decode (Nat.pair o (Nat.pair (x) hist)) = x+1 := by simp [input_to_decode]
  have ho {x hist} : eval_prim O o_1 (Nat.pair o (Nat.pair (x) hist)) = o := by simp [o_1]

  match x with
  | 0 => simp [hinput_to_decode, ho]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 1 => simp [hinput_to_decode, ho]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 2 => simp [hinput_to_decode, ho]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 3 => simp [hinput_to_decode, ho]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 4 => simp [hinput_to_decode, ho]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | n+5 => simp at hx

lemma c_replace_oracle_evp_aux_nMod4_bounds1 : (n/2/2).l≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
lemma c_replace_oracle_evp_aux_nMod4_bounds2 : (n/2/2).r≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
lemma c_replace_oracle_evp_aux_nMod4_bounds3 : (n/2/2)≤n+4 := by exact le_add_right_of_le (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))

theorem c_replace_oracle_evp_aux_nMod4 :
  eval_prim O (c_replace_oracle) (Nat.pair o ((n+4)+1))
    =
  let m:=n.div2.div2
  let ml := eval_prim O (c_replace_oracle) (Nat.pair o m.l)
  let mr := eval_prim O (c_replace_oracle) (Nat.pair o m.r)
  let mp := eval_prim O (c_replace_oracle) (Nat.pair o m)


       if n%4=0 then 2*(2*(Nat.pair (ml) (mr))  )     + 5
  else if n%4=1 then 2*(2*(Nat.pair (ml) (mr))  ) +1  + 5
  else if n%4=2 then 2*(2*(Nat.pair (ml) (mr)) +1 )   + 5
  else if n%4=3 then 2*(2*(mp)  +1)+1   + 5
  else 0

  := by


  lift_lets
  extract_lets
  expose_names

  unfold c_replace_oracle;
  unfold c_replace_oracle_aux

  lift_lets
  extract_lets
  expose_names


  have hinput_to_decode : eval_prim O input_to_decode (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = n+5 := by simp [input_to_decode]
  have hn : eval_prim O n_1 (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = n := by simp [n_1, hinput_to_decode]
  have hnMod4 : eval_prim O nMod4 (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = n%4 := by simp [nMod4, hn]
  have hm : eval_prim O m_1 (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = m := by
    simp [m_1]
    simp [hn]
    simp [m]
    simp [Nat.div2_val]

  have hml : eval_prim O ml_1 (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = ml := by
    simp [ml_1]
    simp [comp_hist]
    simp [hm]
    simp [ml]

    unfold c_replace_oracle
    unfold c_replace_oracle_aux
    lift_lets
    unfold m
    simp only [div2_val]
    rw [c_cov_rec_evp_2 c_replace_oracle_evp_aux_nMod4_bounds1]
    simp
  have hmr : eval_prim O mr_1 (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = mr := by
    simp [mr_1]
    simp [comp_hist]
    simp [hm]
    simp [mr]

    unfold c_replace_oracle
    unfold c_replace_oracle_aux
    lift_lets
    unfold m
    simp only [div2_val]
    rw [c_cov_rec_evp_2 c_replace_oracle_evp_aux_nMod4_bounds2]
    simp
  have hmp : eval_prim O mp_1 (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = mp := by
    simp [mp_1]
    simp [comp_hist]
    simp [hm]
    simp [mp]

    unfold c_replace_oracle
    unfold c_replace_oracle_aux
    lift_lets
    unfold m
    simp only [div2_val]
    rw [c_cov_rec_evp_2 c_replace_oracle_evp_aux_nMod4_bounds3]
    simp
  have hpair_code : eval_prim O pair_code (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = 2 * (2 * Nat.pair ml mr) + 5 := by
    simp [pair_code]
    simp [hml]
    simp [hmr]
    simp [mul_comm]
  have hcomp_code : eval_prim O comp_code (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = 2*(2*(Nat.pair (ml) (mr))  ) +1  + 5 := by
    simp [comp_code]
    simp [hml]
    simp [hmr]
    simp [mul_comm]
  have hprec_code : eval_prim O prec_code (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = 2*(2*(Nat.pair (ml) (mr)) +1 )   + 5 := by
    simp [prec_code]
    simp [hml]
    simp [hmr]
    simp [mul_comm]
  have hrfind'_code : eval_prim O rfind'_code (Nat.pair o (Nat.pair (n+4) (eval_prim O c_replace_oracle_aux (Nat.pair o (n+4))))) = 2*(2*(mp)  +1)+1   + 5 := by
    simp [rfind'_code]
    simp [hmp]
    simp [mul_comm]

-- how can i avoid writing this out in full?
  have stupidrewrite : (eval_prim O
          ((c_const 0).c_cov_rec
            (c_if_eq_te.comp
              ((input_to_decode.pair (c_const 1)).pair
                ((c_const 1).pair
                  (c_if_eq_te.comp
                    ((input_to_decode.pair (c_const 2)).pair
                      ((c_const 2).pair
                        (c_if_eq_te.comp
                          ((input_to_decode.pair (c_const 3)).pair
                            ((c_const 3).pair
                              (c_if_eq_te.comp
                                ((input_to_decode.pair (c_const 4)).pair
                                  (o_1.pair
                                    (c_if_eq_te.comp
                                      ((nMod4.pair (c_const 0)).pair
                                        (pair_code.pair
                                          (c_if_eq_te.comp
                                            ((nMod4.pair (c_const 1)).pair
                                              (comp_code.pair
                                                (c_if_eq_te.comp
                                                  ((nMod4.pair (c_const 2)).pair
                                                    (prec_code.pair rfind'_code))))))))))))))))))))))
          (Nat.pair o (n + 4))) = eval_prim O c_replace_oracle_aux (Nat.pair o (n+4)) := by exact rfl

  simp [stupidrewrite]



  simp [hinput_to_decode]
  simp only [hnMod4]

  match h:n%4 with
  | 0 => simp [hpair_code]
  | 1 => simp [hcomp_code]
  | 2 => simp [hprec_code]
  | 3 => simp [hrfind'_code]
  | x+4 =>
    have contrad : n%4<4 := by
      apply Nat.mod_lt
      decide
    rw [h] at contrad
    rw [show x.succ.succ.succ.succ=x+4 from rfl] at contrad
    simp at contrad

theorem nMod4_eq_0 (h0:n.bodd=false) (h1:n.div2.bodd=false) : n%4=0 := by sorry
theorem nMod4_eq_1 (h0:n.bodd=true ) (h1:n.div2.bodd=false) : n%4=1 := by sorry
theorem nMod4_eq_2 (h0:n.bodd=false) (h1:n.div2.bodd=true ) : n%4=2 := by sorry
theorem nMod4_eq_3 (h0:n.bodd=true ) (h1:n.div2.bodd=true ) : n%4=3 := by sorry

-- set_option maxHeartbeats 1000000 in
-- set_option maxHeartbeats 3 in
@[simp] theorem c_replace_oracle_evp: eval_prim O (c_replace_oracle) = unpaired2 replace_oracle := by
  funext oc
  let o:=oc.l
  let c:=oc.r
  have oc_eq : oc = Nat.pair o c := by exact Eq.symm (pair_unpair oc)
  rw [oc_eq]

  simp only [unpaired2, pair_l, pair_r] -- simplify the rhs


  induction c using Nat.strong_induction_on with
  | _ c ih =>
    match c with
    | 0 => apply c_replace_oracle_evp_aux; decide
    | 1 => apply c_replace_oracle_evp_aux; decide
    | 2 => apply c_replace_oracle_evp_aux; decide
    | 3 => apply c_replace_oracle_evp_aux; decide
    | 4 => apply c_replace_oracle_evp_aux; decide
    | n + 5 =>
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
          simp [replace_oracle, encodeCode_replace_oracle, decodeCode, hno, hn2o] -- simplify the rhs
          -- rw [c_replace_oracle_evp_aux_nMod4_0 h0]
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1]; simp [replace_oracle, m]
          · rw [ih m.r _m2]; simp [replace_oracle, m]

        | true =>
          have h0: n%4=2 := nMod4_eq_2 hno hn2o
          simp [replace_oracle, encodeCode_replace_oracle, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1]; simp [replace_oracle, m]
          · rw [ih m.r _m2]; simp [replace_oracle, m]

      | true => cases hn2o:n.div2.bodd with
        | false =>
          have h0: n%4=1 := nMod4_eq_1 hno hn2o
          simp [replace_oracle, encodeCode_replace_oracle, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1]; simp [replace_oracle, m]
          · rw [ih m.r _m2]; simp [replace_oracle, m]

        | true =>
          have h0: n%4=3 := nMod4_eq_3 hno hn2o
          simp [replace_oracle, encodeCode_replace_oracle, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          rw [ih m hm]; simp [replace_oracle, m]
          -- constructor
          -- · rw [ih m.l _m1]; simp [replace_oracle, m]
          -- · rw [ih m.r _m2]; simp [replace_oracle, m]

-- theorem test : n+5=(n+4)+1 := by exact?



@[simp] theorem c_replace_oracle_ev:eval O (c_replace_oracle) = unpaired2 replace_oracle := by rw [← eval_prim_eq_eval c_replace_oracle_ev_pr]; simp only [c_replace_oracle_evp];
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.replace_oracle:Nat.PrimrecIn O (unpaired2 replace_oracle) := by rw [← c_replace_oracle_evp]; apply code_prim_prop c_replace_oracle_ev_pr
theorem Nat.Primrec.replace_oracle:Nat.Primrec (unpaired2 replace_oracle) := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.replace_oracle
end replace_oracle


























section evaln
-- namespace Nat.RecursiveIn.Code

/-



-/
-- def c_evaln := c_mod.comp₂ (right.comp right) (c_pow.comp₂ (c_const 2) left)
-- @[simp] theorem c_evaln_ev_pr:code_prim c_evaln := by unfold c_evaln; repeat (first|assumption|simp|constructor)
-- @[simp] theorem c_evaln_evp:evaln_prim O c_evaln = Nat.evaln := by
--   simp [c_evaln,evaln_prim]
--   funext n;
--   sorry
--   simp [unpaired2]
--   induction n.r with
--   | zero => exact rfl
--   | succ n h => exact Nat.evaln_left_inj.mpr h
-- @[simp] theorem c_evaln_ev:evaln O c_evaln = unpaired2 Nat.evaln := by rw [← evaln_prim_eq_evaln c_evaln_ev_pr]; simp only [c_evaln_evp]
-- end Nat.RecursiveIn.Code
-- -- theorem Nat.PrimrecIn.evaln:Nat.PrimrecIn O Nat.evaln := by ...
-- -- theorem Nat.Primrec.evaln:Nat.Primrec Nat.evaln := by ...
end evaln
















































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
