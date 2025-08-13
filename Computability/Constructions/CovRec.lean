import Computability.Constructions.Basic
open Nat.RecursiveIn.Code

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
def c_cov_rec (cf cg:Code):=
  prec
  (c_l_append.comp₂ (c_const Nat.list_empty) (cf))
  (c_efl_prec cg)
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
  simp [eval_prim, comp₄]

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
  | 0 => simp [hinput_to_decode, ho, comp₄]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 1 => simp [hinput_to_decode, ho, comp₄]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 2 => simp [hinput_to_decode, ho, comp₄]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 3 => simp [hinput_to_decode, ho, comp₄]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
  | 4 => simp [hinput_to_decode, ho, comp₄]; simp only [replace_oracle, encodeCode_replace_oracle, decodeCode]
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

  simp [comp₄, stupidrewrite]


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
        -- pair
        | false =>
          have h0: n%4=0 := nMod4_eq_0 hno hn2o
          simp [replace_oracle, encodeCode_replace_oracle, decodeCode, hno, hn2o] -- simplify the rhs
          -- rw [c_replace_oracle_evp_aux_nMod4_0 h0]
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1]; simp [replace_oracle, m]
          · rw [ih m.r _m2]; simp [replace_oracle, m]

        -- prec
        | true =>
          have h0: n%4=2 := nMod4_eq_2 hno hn2o
          simp [replace_oracle, encodeCode_replace_oracle, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1]; simp [replace_oracle, m]
          · rw [ih m.r _m2]; simp [replace_oracle, m]

      | true => cases hn2o:n.div2.bodd with
        -- comp
        | false =>
          have h0: n%4=1 := nMod4_eq_1 hno hn2o
          simp [replace_oracle, encodeCode_replace_oracle, decodeCode, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1]; simp [replace_oracle, m]
          · rw [ih m.r _m2]; simp [replace_oracle, m]

        -- rfind
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
