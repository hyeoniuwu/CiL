import Computability.RecursiveInTheorems

open Nat.RecursiveIn.Code

section comp₂
namespace Nat.RecursiveIn.Code
@[simp] def comp₂ : Code→Code→Code→Code := fun c1 c2 c3 => c1.comp (pair c2 c3)
@[simp, aesop safe] theorem comp₂_ev_pr (hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3) :code_prim (comp₂ c1 c2 c3) := by
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
@[simp, aesop safe] theorem c_id_ev_pr:code_prim c_id := by unfold c_id; repeat (first|assumption|simp|constructor)
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
@[simp] theorem c_const_ev: ∀ n m, eval O (c_const n) m = n
| 0, _ => rfl
| n+1, m => by simp! [c_const_ev n m]
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
@[simp, aesop safe] theorem c_sg_ev_pr:code_prim c_sg := by unfold c_sg; repeat (first|assumption|simp|constructor)
@[simp] theorem c_sg_evp:eval_prim O c_sg = Nat.sg := by
  simp [c_sg,eval_prim]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp] theorem c_sg_ev : eval O c_sg = Nat.sg := by rw [← eval_prim_eq_eval c_sg_ev_pr]; simp only [c_sg_evp]
def c_sg' := comp (prec (c_const 1) (((zero).comp left).comp left)) (pair zero c_id)
@[simp, aesop safe] theorem c_sg'_ev_pr:code_prim c_sg' := by unfold c_sg'; repeat (first|assumption|simp|constructor)
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
@[simp, aesop safe] theorem c_add_ev_pr:code_prim c_add := by unfold c_add; repeat (first|assumption|simp|constructor)
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
@[simp, aesop safe] theorem c_mul_ev_pr:code_prim c_mul := by unfold c_mul; repeat (first|assumption|simp|constructor)
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
@[simp, aesop safe] theorem c_pow_ev_pr:code_prim c_pow := by unfold c_pow; repeat (first|assumption|simp|constructor)
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
@[simp, aesop safe] theorem c_pred_ev_pr:code_prim c_pred := by unfold c_pred; repeat (first|assumption|simp|constructor)
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
@[simp, aesop safe] theorem c_sub_ev_pr:code_prim c_sub := by unfold c_sub; repeat (first|assumption|simp|constructor)
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
@[simp, aesop safe] theorem c_dist_ev_pr:code_prim c_dist := by unfold c_dist; repeat (first|assumption|simp|constructor)
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
@[simp, aesop safe] theorem c_if_eq'_ev_pr:code_prim c_if_eq' := by unfold c_if_eq'; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_eq'_evp:eval_prim O c_if_eq' = fun ab => if ab.l=ab.r then 0 else 1 := by simp [c_if_eq',eval_prim];
@[simp] theorem c_if_eq'_ev:eval O c_if_eq' = fun ab => if ab.l=ab.r then Part.some 0 else Part.some 1 := by
  rw [← eval_prim_eq_eval c_if_eq'_ev_pr]; simp only [c_if_eq'_evp]; funext xs; exact apply_ite Part.some (xs.l = xs.r) 0 1
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_eq':Nat.PrimrecIn O Nat.if_eq' := by ...
-- theorem Nat.Primrec.if_eq':Nat.Primrec Nat.if_eq' := by ...
end if_eq'



section comp₄
namespace Nat.RecursiveIn.Code
@[simp] def comp₄ : Code→Code→Code→Code→Code→Code := fun c1 c2 c3 c4 c5 => c1.comp₂ (pair c2 c3) (pair c4 c5)
@[simp, aesop safe] theorem comp₄_ev_pr (hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3) (hc4:code_prim c4) (hc5:code_prim c5):code_prim (comp₄ c1 c2 c3 c4 c5) := by
  unfold comp₄;
  repeat (first|assumption|simp|constructor)
theorem comp₄_evp:eval_prim O (comp₄ c1 c2 c3 c4 c5) x=
  eval_prim O c1 (Nat.pair (Nat.pair (eval_prim O (c2) x) (eval_prim O (c3) x)) ((Nat.pair (eval_prim O (c4) x) (eval_prim O (c5) x)))) := by
  simp [comp₄,eval_prim, comp₂];
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
@[simp, aesop safe] theorem comp₃_ev_pr (hc1:code_prim c1) (hc2:code_prim c2) (hc3:code_prim c3) (hc4:code_prim c4) :code_prim (comp₃ c1 c2 c3 c4) := by
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
@[simp, aesop safe] theorem c_if_eq_te_ev_pr:code_prim c_if_eq_te := by unfold c_if_eq_te; repeat (first|assumption|simp|constructor)


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
@[simp, aesop safe] theorem c_if_lt_te_ev_pr:code_prim c_if_lt_te := by unfold c_if_lt_te; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_lt_te_evp:eval_prim O c_if_lt_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a<b then c else d := by
  simp [c_if_lt_te,eval_prim];
  -- funext xs
  cases Classical.em (a<b) with
  | inl h => simp [h, Nat.sub_eq_zero_of_le h]
  | inr h =>
    have h1: a+1-b>0 := by exact tsub_pos_iff_not_le.mpr h
    have h0: ¬(a+1-b=0) := by exact Nat.ne_zero_of_lt h1
    simp [h, h0]
@[simp] theorem c_if_lt_te_ev:eval O c_if_lt_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a<b then c else d := by
  rw [← eval_prim_eq_eval c_if_lt_te_ev_pr]; simp
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_lt_te:Nat.PrimrecIn O Nat.if_lt_te := by ...
-- theorem Nat.Primrec.if_lt_te:Nat.Primrec Nat.if_lt_te := by ...
end if_lt_te



section if_le_te
namespace Nat.RecursiveIn.Code
-- we use the fact that `a<b+1 ↔ a≤b`.
/-- eval c_if_le_te (x,y) = [x≤y] -/
def c_if_le_te := c_if_lt_te.comp (pair (pair (left.comp left) (succ.comp $ right.comp left)) right)
@[simp, aesop safe] theorem c_if_le_te_ev_pr:code_prim c_if_le_te := by unfold c_if_le_te; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_le_te_evp:eval_prim O c_if_le_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a≤b then c else d := by
  simp [c_if_le_te,eval_prim];
  -- funext xs
  cases Classical.em (a<b+1) with
  | inl h => simp [h, Nat.lt_add_one_iff.mp h]
  | inr h => simp [h, Nat.lt_add_one_iff.not.mp h]
@[simp] theorem c_if_le_te_ev:eval O c_if_le_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a≤b then c else d := by
  rw [← eval_prim_eq_eval c_if_le_te_ev_pr]; simp
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_le_te:Nat.PrimrecIn O Nat.if_le_te := by ...
-- theorem Nat.Primrec.if_le_te:Nat.Primrec Nat.if_le_te := by ...
end if_le_te

section flip
namespace Nat.RecursiveIn.Code
/-- eval c_flip (x,y) = (y,x) -/
def c_flip := pair right left
@[simp, aesop safe] theorem c_flip_ev_pr:code_prim c_flip := by unfold c_flip; repeat (first|assumption|simp|constructor)
@[simp] theorem c_flip_evp:eval_prim O c_flip (Nat.pair a b) = Nat.pair b a := by
  simp [c_flip,eval_prim];
@[simp] theorem c_flip_ev:eval O c_flip (Nat.pair a b) = Nat.pair b a := by
  rw [← eval_prim_eq_eval c_flip_ev_pr]; simp
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.flip:Nat.PrimrecIn O Nat.flip := by ...
-- theorem Nat.Primrec.flip:Nat.Primrec Nat.flip := by ...
end flip


section if_gt_te
namespace Nat.RecursiveIn.Code
/-- eval c_if_gt_te (x,y) = [x>y] -/
def c_if_gt_te := c_if_lt_te.comp (pair (c_flip.comp left) right)
@[simp, aesop safe] theorem c_if_gt_te_ev_pr:code_prim c_if_gt_te := by unfold c_if_gt_te; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_gt_te_evp:eval_prim O c_if_gt_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a>b then c else d := by simp [c_if_gt_te,eval_prim];
@[simp] theorem c_if_gt_te_ev:eval O c_if_gt_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a>b then c else d := by
  rw [← eval_prim_eq_eval c_if_gt_te_ev_pr]; simp
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_gt_te:Nat.PrimrecIn O Nat.if_gt_te := by ...
-- theorem Nat.Primrec.if_gt_te:Nat.Primrec Nat.if_gt_te := by ...
end if_gt_te
section if_ge_te
namespace Nat.RecursiveIn.Code
/-- eval c_if_ge_te (x,y) = [x>y] -/
def c_if_ge_te := c_if_le_te.comp (pair (c_flip.comp left) right)
@[simp, aesop safe] theorem c_if_ge_te_ev_pr:code_prim c_if_ge_te := by unfold c_if_ge_te; repeat (first|assumption|simp|constructor)
@[simp] theorem c_if_ge_te_evp:eval_prim O c_if_ge_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a≥b then c else d := by simp [c_if_ge_te,eval_prim];
@[simp] theorem c_if_ge_te_ev:eval O c_if_ge_te (Nat.pair (Nat.pair a b) (Nat.pair c d)) = if a≥b then c else d := by
  rw [← eval_prim_eq_eval c_if_ge_te_ev_pr]; simp
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_ge_te:Nat.PrimrecIn O Nat.if_ge_te := by ...
-- theorem Nat.Primrec.if_ge_te:Nat.Primrec Nat.if_ge_te := by ...
end if_ge_te

section ifz
namespace Nat.RecursiveIn.Code
def c_ifz := c_add.comp $ pair (c_mul.comp $ pair (c_sg'.comp left) (left.comp right)) (c_mul.comp $ pair (c_sg.comp left) (right.comp right))
@[simp, aesop safe] theorem c_ifz_ev_pr:code_prim c_ifz := by unfold c_ifz; repeat (first|assumption|simp|constructor)
@[simp] theorem c_ifz_evp:eval_prim O c_ifz = fun (cab:ℕ) => if cab.l=0 then cab.r.l else cab.r.r := by
  simp [c_ifz,eval_prim];
  funext xs
  have hsplit : xs.l = 0 ∨ ¬ (xs.l = 0) := by exact Or.symm (ne_or_eq xs.l 0)
  cases hsplit with
  | inl h => simp [h]
  | inr h => simp [h]
theorem c_ifz_ev':eval O c_ifz = fun (cab:ℕ) => if cab.l=0 then cab.r.l else cab.r.r := by rw [← eval_prim_eq_eval c_ifz_ev_pr]; simp only [c_ifz_evp];
@[simp] theorem c_ifz_ev:eval O c_ifz cab = if cab.l=0 then cab.r.l else cab.r.r := by
  simp [c_ifz_ev']
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.ifz:Nat.PrimrecIn O Nat.ifz := by ...
-- theorem Nat.Primrec.ifz:Nat.Primrec Nat.ifz := by ...
end ifz




section ef
namespace Nat.RecursiveIn.Code
def c_ef:ℕ→ℕ:=fun c=>(pair Nat.RecursiveIn.Code.id c)
-- @[s, aesop safeimp] theorem c_ef_ev_pr:code_prim $ c_ef c := by unfold c_ef; repeat (first|assumption|simp|constructor)
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
