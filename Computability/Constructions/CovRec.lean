/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.List

/-!
# CovRec.lean

This file defines constructs to work with course-of-values recursion (using only primitive recursive codes).

Course-of-values recursion allows a recursive definition of f(x) in terms of f(0), f(1), ... f(x-1), unlike
primitive recursion which only exposes f(x-1).

The main definition is `c_cov_rec`, which has a similar interface to `prec`, but exposes the list of all previous computations
f(0), f(1), ... f(x-1) instead of f(x-1).

We also define several theorems `c_cov_rec_evp_*`, which simplify interactions with `c_cov_rec`.

This file also contains two examples using course-of-values recursion; division and an example on parsing codes.

## Notation/quirks

 - Where `x`, `y` are naturals, `⟪x, y⟫ = Nat.pair x y`.
-/

open Computability.Code
open List Nat

section efl_prec
namespace Computability.Code
/--
A specialised code used as an auxiliary for `c_cov_rec`.
Given an input of the form ``⟪x, i, list⟫``, the code (c_efl_prec c) computes list.append (eval c input).
(The form above is what you would expect in the inductive case in primitive recursion.)
-/
def c_efl_prec := λ c ↦ c_list_concat.comp (pair (c_id.comp (right.comp right)) c)
@[cp] theorem c_efl_prec_prim (h:code_prim c):code_prim $ c_efl_prec c := by unfold c_efl_prec; apply_cp
@[simp] theorem c_efl_prec_evp : evalp O (c_efl_prec c) x = l2n ((n2l x.r.r).concat (evalp O c x)) := by
  simp [c_efl_prec]
end Computability.Code
end efl_prec

-- course of values recursion.
section cov_rec
namespace Computability.Code
/--
Code for course-of-values recursion.

base case:
  `eval (c_cov_rec cf cg) (x, 0)` = `[eval cf x]` (list with one element)

inductive case:
  let `l` be the list of previous values, from `j=0` to `i`.
  Then `eval (c_cov_rec cf cg) (x, i+1) = l.append $ eval cg (x, i, l)`.
-/
def c_cov_rec (cf cg : Code) :=
  prec
  (c_list_concat.comp₂ c_list_nil cf)
  (c_efl_prec cg)
@[cp] theorem c_cov_rec_prim (hc1:code_prim c1) (hc2:code_prim c2) : code_prim (c_cov_rec c1 c2) := by unfold c_cov_rec; apply_cp
@[simp] theorem c_cov_rec_evp_size_positive : 0<(n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫)).length := by
  unfold c_cov_rec
  induction i <;> simp
@[simp] theorem c_cov_rec_evp_size : (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫)).length = i+1 := by
  unfold c_cov_rec
  simp [evalp]
  induction i
  · simp
  · simpa
theorem c_cov_rec_evp_indt :
  evalp O (c_cov_rec cf cg) ⟪x, i+1⟫
    =
  (l2n $ List.concat
  (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫))
  (evalp O cg ⟪x, i, evalp O (c_cov_rec cf cg) ⟪x,i⟫⟫)
  ) := by
  rw [c_cov_rec]
  rw [evalp]
  simp
@[simp] theorem c_cov_rec_evp_base_I : getLastI (n2l (evalp O (c_cov_rec cf cg) ⟪x,0⟫)) = evalp O cf x := by
  unfold c_cov_rec
  simp [getLastI]
@[simp] theorem c_cov_rec_evp_get0 : (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫))[0] = evalp O cf x := by
  induction i with
  | zero => unfold c_cov_rec; simp [evalp]
  | succ i h => simp [c_cov_rec_evp_indt]; exact h
@[simp] theorem c_cov_rec_evp_get0_I : getI (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫)) 0 = evalp O cf x := by
  induction i with
  | zero => unfold c_cov_rec; simp [evalp, getI]
  | succ i h => simp [c_cov_rec_evp_indt]; simp [getI]
@[simp] theorem c_cov_rec_indt_last : getLastI (evalp O (c_cov_rec cf cg) ⟪x, i+1⟫) =
  evalp O cg ⟪x, i, evalp O (c_cov_rec cf cg) ⟪x,i⟫⟫ := by
  rw [c_cov_rec_evp_indt]
  simp
theorem c_cov_rec_evp_last :
  getLastI (evalp O (c_cov_rec cf cg) ⟪x,i⟫)
    =
  (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫))[i] := by
  rw [getLastI_eq_getLast?]
  rw [getLast?_eq_getElem?]
  simp [c_cov_rec_evp_size]
theorem c_cov_rec_evp_last_I :
  getLastI (evalp O (c_cov_rec cf cg) ⟪x,i⟫)
    =
  getI (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫)) i := by
  rw [c_cov_rec_evp_last]
  exact (getI_eq_getElem _ _).symm
theorem c_cov_rec_evp_get_aux (h:j≤i) :
  (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫))[j]'(by simp [c_cov_rec_evp_size]; omega)
    =
  (n2l (evalp O (c_cov_rec cf cg) ⟪x, i+1⟫))[j]'(by simp [c_cov_rec_evp_size]; omega)
  := by
  simp [c_cov_rec_evp_indt]
  exact getElem_append_left' _ _
theorem c_cov_rec_evp_get_aux_I (h:j≤i) :
  getI (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫)) j
    =
  getI (n2l (evalp O (c_cov_rec cf cg) ⟪x, i+1⟫)) j
  := by
  simp [c_cov_rec_evp_indt]

  have bounds1: j<(n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫)).length := by
    simp
    exact lt_add_one_of_le h
  have bounds2: j<((n2l (evalp O (cf.c_cov_rec cg) ⟪x,i⟫) ++ [evalp O cg ⟪x, i, evalp O (c_cov_rec cf cg) ⟪x,i⟫⟫])).length := by
    simp
    omega
  simp [getI]
  grind? says grind only [= List.getElem?_eq_none, length_append, getElem?_pos, getElem?_neg, getElem?_append, → eq_nil_of_append_eq_nil]

@[simp] theorem c_cov_rec_evp_get (h:j≤i):
  (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫))[j]'(by simp [c_cov_rec_evp_size]; omega)
    =
  getLastI (evalp O (c_cov_rec cf cg) ⟪x, j⟫) := by

  rw [c_cov_rec_evp_last]
  induction i with
  | zero => simp only [show j=0 from eq_zero_of_le_zero h]
  | succ n ih =>
    cases le_or_eq_of_le_succ h with
    | inr h1 => simp only [h1]
    | inl h1 =>
      rw [← ih h1]
      rw [← c_cov_rec_evp_get_aux]
      exact h1
@[simp] theorem c_cov_rec_evp_getI (h:j≤i):
  getI (n2l (evalp O (c_cov_rec cf cg) ⟪x,i⟫)) j
    =
  getLastI (evalp O (c_cov_rec cf cg) ⟪x, j⟫) := by
  rw [← @c_cov_rec_evp_get j i O cf cg x h]
  exact getI_eq_getElem _ _

end Computability.Code
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

namespace Computability.Code
/-
This example serves as a blueprint for using `c_cov_rec` in proofs.

For this specific example, one can bypass defining the auxiliary function `c_div_flip_aux` and write a shorter proof; see https://github.com/hyeoniuwu/CiL/blob/99fd356e7835d1856fb73306df7828f96b42a85c/Computability/Constructions.lean#L758.

However, I've written the "longer" way, which is more efficient. For more complex constructions, this longer way becomes necessary.

The reason for explicitly defining the auxiliary function (the function without c_l_get_last.comp attached) is to be able to rewrite the
"unfolded" definitions in the recursive case with the shorter function name.

The let-bindings allow for more organised/performant proofs, and also helps readability in the construction.
This is especially true for more complex `c_cov_rec` constructions, such as `c_replace_oracle_aux` later.

All let bindings are used in the inductive case of course-of-values recursion.

Recall that the interface for the inductive case is designed like `prec`; in `c_cov_rec cf cg ⟪x, i+1⟫`, the
input that the code `cg` will get looks like:
`⟪x, i, evalp O (c_cov_rec cf cg) ⟪x,i⟫⟫`.
-/
/-- `evalp O c_div_flip ⟪d, n⟫ = n/d`. -/
def c_div_flip_aux :=
  let dividend := succ.comp $ left.comp right
  let divisor := left
  let list_of_prev_values := right.comp right

  c_cov_rec

  (c_const 0) $ -- base case: if dividend is 0, return 0

  c_ifz.comp₂ divisor $ -- in general, test if the divisor is zero
  pair (c_const 0) $ -- if so, return 0
  c_if_lt_te.comp₄ dividend divisor (c_const 0) $ -- if dividend < divisor, return 0
  (succ.comp (c_list_getI.comp₂ list_of_prev_values (c_sub.comp₂ dividend divisor))) -- else return (dividend-divisor)/divisor+1
def c_div_flip := c_list_getLastI.comp c_div_flip_aux
def c_div := c_div_flip.comp (c_flip)

theorem c_div_flip_evp_aux_aux :
  evalp O c_div_flip ⟪d+1, n+1⟫
    =
  if n<d then 0 else evalp O c_div_flip ⟪d+1, n-d⟫ + 1
    := by

  rw (config:={occs:=.pos [1]}) [c_div_flip]
  unfold c_div_flip_aux

  lift_lets; extract_lets; expose_names

  let (eq:=hinp2) inp2 := evalp O c_div_flip_aux (Nat.pair (d+1) (n))
  unfold c_div_flip_aux at hinp2; lift_lets at hinp2
  let (eq:=hinp) inp := Nat.pair (d + 1) (Nat.pair n inp2)

  have hdivisor : evalp O divisor inp = d+1 := by simp [hinp, divisor]
  have hdividend : evalp O dividend inp = n+1 := by simp [hinp, dividend]
  have hlist_of_prev_values : evalp O list_of_prev_values inp = evalp O c_div_flip_aux ⟪d+1, n⟫ := by
    simp [hinp, inp2, list_of_prev_values]

  simp
  simp only [← hinp2, ← hinp]
  simp [hdivisor,hdividend,hlist_of_prev_values]

  unfold c_div_flip
  unfold c_div_flip_aux
  simp only []
  rw [evalp]
  simp

theorem c_div_flip_evp_aux:evalp O c_div_flip = unpaired2 div_flip_aux := by
  funext dn
  let d := dn.l
  let n := dn.r
  have dn_eq : dn = Nat.pair d n := by exact Eq.symm (pair_unpair dn)
  rw [dn_eq]
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero => simp [div_flip_aux_eq_div_flip,flip, c_div_flip, c_div_flip_aux, evalp]
  | succ n' =>
    cases hd:d with
    | zero => simp [div_flip_aux_eq_div_flip,flip,c_div_flip, c_div_flip_aux, evalp]
    | succ d' =>
      rw [c_div_flip_evp_aux_aux]
      unfold div_flip_aux; simp
      rw [hd] at ih
      rw [ih (n'-d') (sub_lt_succ n' d')]
      unfold div_flip_aux; simp

@[simp] theorem c_div_flip_evp : evalp O c_div_flip = unpaired2 (flip ((· / ·) : ℕ → ℕ → ℕ)) := by
  rw [c_div_flip_evp_aux]
  simp [div_flip_aux_eq_div_flip]
@[simp] theorem c_div_evp : evalp O c_div ⟪a,b⟫ = a/b := by
  unfold c_div
  simp [evalp]
  simp [flip]

@[cp] theorem c_div_prim : code_prim c_div := by
  unfold c_div;
  unfold c_div_flip;
  unfold c_div_flip_aux;
  apply_cp 40

@[simp] theorem c_div_ev:eval O c_div ⟪a,b⟫ = a/b := by
  rw [← evalp_eq_eval c_div_prim];
  simp
  exact Eq.symm (Part.some_div_some a b)
end Computability.Code
end div

section mod
namespace Computability.Code
def c_mod := c_sub.comp₂ left (c_mul.comp₂ right c_div)
@[cp] theorem c_mod_prim:code_prim c_mod := by unfold c_mod; apply_cp
@[simp] theorem c_mod_evp : evalp O c_mod = unpaired2 ((· % ·) : ℕ → ℕ → ℕ) := by
  simp [c_mod,evalp];

  funext mn
  let m:=mn.l
  let n:=mn.r
  have mn_eq : mn = ⟪m, n⟫ := by exact Eq.symm (pair_unpair mn)
  rw [mn_eq]

  apply Nat.sub_eq_of_eq_add
  simp [add_comm (m % n), Nat.div_add_mod]

@[simp] theorem c_mod_ev:eval O c_mod = unpaired2 ((· % ·) : ℕ → ℕ → ℕ) := by rw [← evalp_eq_eval c_mod_prim]; simp only [c_mod_evp]
end Computability.Code
end mod

section div2
namespace Computability.Code
def c_div2 := c_div.comp₂ c_id (c_const 2)
@[cp] theorem c_div2_prim:code_prim c_div2 := by unfold c_div2; apply_cp
@[simp] theorem c_div2_evp : evalp O c_div2 = div2 := by simp [c_div2]; funext x; exact Eq.symm (div2_val x)
@[simp] theorem c_div2_ev:eval O c_div2 = div2 := by simp [← evalp_eq_eval c_div2_prim]
end Computability.Code
end div2
section mod2
namespace Computability.Code
def c_mod2 := c_mod.comp₂ c_id (c_const 2)
@[cp] theorem c_mod2_prim:code_prim c_mod2 := by unfold c_mod2; apply_cp
@[simp] theorem c_mod2_evp : evalp O c_mod2 = λ x ↦ x%2 := by simp [c_mod2];
@[simp] theorem c_mod2_ev:eval O c_mod2 = (λ x:ℕ ↦ x%2) := by simp [← evalp_eq_eval c_mod2_prim]
end Computability.Code
end mod2

section replace_oracle
namespace Computability.Code
/-! ### parsing codes with c_cov_rec
#### Structure of section
  · `c_replace_oracle_aux` : main body of construction, using c_cov_rec
  · `c_replace_oracle` : to see why this is defined separately, see comments on `c_div_flip_aux`
  · `c_replace_oracle_prim` : show `c_replace_oracle` is primrec
  · `c_replace_oracle_evp_aux` : shows that the code has correct behaviour on the non-inductive codes i.e
    `zero`, `succ`, `left`, `right` and `oracle`. This is much easier than e.g. `prec`, which required
    inductive reasoning on previous codes.
  · `c_replace_oracle_evp_aux_nMod4_bounds*` : the `c_cov_rec` construction accesses previous computations
    by looking that up on a list. to know that the lookup succeeded (and thus simplify using the `c_cov_rec_evp*` theorems),
    we need to know that the index is smaller than the current input. These bounds theorem show exactly that.
  · `c_replace_oracle_evp_aux_nMod4` : shows behaviour of the codes on the inductive codes i.e
    `pair`, `comp`, `prec` and `rfind'`. One thing to note is that this theorem does not show correctness by itself;
    it only demonstrates that evaluating `c_replace_oracle` on an inductive code, can be simplified to evaluating
    `c_replace_oracle` on smaller codes. To show correctness, one would need to use strong induction on codes, which we do next.
  · `c_replace_oracle_evp` : shows that the code has correct behaviour on evaluation, using strong induction. The proof requires
    basically no interaction with `evalp`, as that has all been done in the previous theorems.
-/

/--
Given a code `c`, `replace_oracle o c` replaces all instances of the code `oracle` with the code `o` instead.

Examples:
replace_oracle c oracle = c
replace_oracle c succ = succ
replace_oracle c (prec zero oracle) = prec zero c
-/
def replace_oracle (o : Code) : Code → Code
| Code.zero        => Code.zero
| Code.succ        => Code.succ
| Code.left        => Code.left
| Code.right       => Code.right
| Code.oracle      => o
| Code.pair cf cg  => Code.pair (replace_oracle o cf) (replace_oracle o cg)
| Code.comp cf cg  => Code.comp (replace_oracle o cf) (replace_oracle o cg)
| Code.prec cf cg  => Code.prec (replace_oracle o cf) (replace_oracle o cg)
| Code.rfind' cf   => Code.rfind' (replace_oracle o cf)

/--
`eval c_replace_oracle (o,code) = replace_oracle o code`.
-/
def c_replace_oracle_aux :=
  let o               := left
  let input_to_decode := succ.comp (left.comp right)
  let comp_hist       := right.comp right
  let n               := c_sub.comp₂ input_to_decode (c_const 5)
  let m               := c_div2.comp $ c_div2.comp n
  let lookup (c')     := c_list_getI.comp₂ comp_hist c'
  let ml              := lookup (left.comp m)
  let mr              := lookup (right.comp m)
  let mp              := lookup m
  let nMod4           := c_mod.comp₂ n (c_const 4)
  let pair_code       := c_add.comp₂ (            c_mul2.comp $             c_mul2.comp (pair ml mr)) (c_const 5)
  let comp_code       := c_add.comp₂ (succ.comp $ c_mul2.comp $             c_mul2.comp (pair ml mr)) (c_const 5)
  let prec_code       := c_add.comp₂ (            c_mul2.comp $ succ.comp $ c_mul2.comp (pair ml mr)) (c_const 5)
  let rfind'_code     := c_add.comp₂ (succ.comp $ c_mul2.comp $ succ.comp $ c_mul2.comp mp          ) (c_const 5)

  c_cov_rec

  (c_const 0) $ -- base case, when code = 0.

  c_if_eq_te.comp₄ input_to_decode (c_const 1) (c_const 1) $
  c_if_eq_te.comp₄ input_to_decode (c_const 2) (c_const 2) $
  c_if_eq_te.comp₄ input_to_decode (c_const 3) (c_const 3) $
  c_if_eq_te.comp₄ input_to_decode (c_const 4) o           $
  c_if_eq_te.comp₄ nMod4           (c_const 0) pair_code   $
  c_if_eq_te.comp₄ nMod4           (c_const 1) comp_code   $
  c_if_eq_te.comp₄ nMod4           (c_const 2) prec_code   $
                                               rfind'_code

def c_replace_oracle := c_list_getLastI.comp c_replace_oracle_aux
/-
The most efficient way to show `code_prim (c_replace_oracle)` is by showing the primitiveness of each
let-binding.

If one were to instead unfold all let-bindings, there are performance penalties.
-/
@[cp] theorem c_replace_oracle_prim : code_prim (c_replace_oracle) := by
  unfold c_replace_oracle;
  unfold c_replace_oracle_aux
  extract_lets;
  expose_names;
  have cp_o : code_prim o := by apply_cp
  have cp_input_to_decode : code_prim input_to_decode := by apply_cp
  have cp_comp_hist : code_prim comp_hist := by apply_cp
  have cp_n : code_prim n := by apply_cp
  have cp_m : code_prim m := by apply_cp
  have cp_ml : code_prim ml := by apply_cp
  have cp_mr : code_prim mr := by apply_cp
  have cp_mp : code_prim mp := by apply_cp
  have cp_nMod4 : code_prim nMod4 := by apply_cp
  have cp_pair_code : code_prim pair_code := by apply_cp
  have cp_comp_code : code_prim comp_code := by apply_cp
  have cp_prec_code : code_prim prec_code := by apply_cp
  have cp_rfind'_code : code_prim rfind'_code := by apply_cp
  apply_cp 40

theorem c_replace_oracle_evp_aux (hx:x≤4): evalp O (c_replace_oracle) ⟪o, x⟫ = c2n (replace_oracle (n2c o) (n2c x)) := by
  unfold c_replace_oracle
  unfold c_replace_oracle_aux
  lift_lets; extract_lets; expose_names
  have hinput_to_decode {x hist} : evalp O input_to_decode ⟪o, x, hist⟫ = x+1 := by simp [input_to_decode]
  have ho {x hist} : evalp O o_1 ⟪o, x, hist⟫ = o := by simp [o_1]
  match x with
  | 0 => simp []; simp only [replace_oracle, replace_oracle, n2c, c2n]
  | 1 => simp [hinput_to_decode, ho]; simp only [replace_oracle, replace_oracle, n2c, c2n]
  | 2 => simp [hinput_to_decode, ho]; simp only [replace_oracle, replace_oracle, n2c, c2n]
  | 3 => simp [hinput_to_decode, ho]; simp only [replace_oracle, replace_oracle, n2c, c2n]
  | 4 => simp [hinput_to_decode, ho]; simp only [replace_oracle, replace_oracle, n2c, c2n_n2c]
  | n+5 => simp at hx

lemma c_replace_oracle_evp_aux_nMod4_bounds1 : (n/2/2).l≤n+4 := by
  exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
lemma c_replace_oracle_evp_aux_nMod4_bounds2 : (n/2/2).r≤n+4 := by
  exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
lemma c_replace_oracle_evp_aux_nMod4_bounds3 : (n/2/2)≤n+4 := by
  exact le_add_right_of_le (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))

theorem c_replace_oracle_evp_aux_nMod4 :
  evalp O (c_replace_oracle) ⟪o, ((n+4)+1)⟫
    =
  let m  := n.div2.div2
  let ml := evalp O (c_replace_oracle) ⟪o, m.l⟫
  let mr := evalp O (c_replace_oracle) ⟪o, m.r⟫
  let mp := evalp O (c_replace_oracle) ⟪o, m  ⟫

       if n%4=0 then 2*(2*⟪ml, mr⟫  )     + 5
  else if n%4=1 then 2*(2*⟪ml, mr⟫  ) +1  + 5
  else if n%4=2 then 2*(2*⟪ml, mr⟫ +1 )   + 5
  else if n%4=3 then 2*(2*(mp)  +1)+1     + 5
  else 0

  := by
  lift_lets; extract_lets; expose_names
  unfold c_replace_oracle;
  unfold c_replace_oracle_aux
  lift_lets; extract_lets; expose_names
  let (eq:=hinp) inp := evalp O c_replace_oracle_aux ⟪o, n+4⟫
  unfold c_replace_oracle_aux at hinp; lift_lets at hinp

  have hinput_to_decode : evalp O input_to_decode ⟪o, n+4, inp⟫ = n+5 := by simp [input_to_decode]
  have hn : evalp O n_1 ⟪o, n+4, inp⟫ = n := by simp [n_1, hinput_to_decode]
  have hnMod4 : evalp O nMod4 ⟪o, n+4, inp⟫ = n%4 := by simp [nMod4, hn]
  have hm : evalp O m_1 ⟪o, n+4, inp⟫ = m := by simp [m_1, hn, m]
  have hlookup {c'} (hcs'': evalp O c' ⟪o, n+4, inp⟫ ≤ n+4) :
    evalp O (lookup c') ⟪o, n+4, inp⟫
      =
    let c'' := evalp O c' ⟪o, n+4, inp⟫
    evalp O (c_replace_oracle) ⟪o, c''⟫ := by
    lift_lets; extract_lets; expose_names
    have aux2 : evalp O c' ⟪o, n+4, inp⟫ = c'' := by simp [c'']
    simp [lookup]
    simp [aux2] at *
    simp [comp_hist]
    simp [inp]
    unfold c_replace_oracle
    unfold c_replace_oracle_aux
    lift_lets
    simp [hcs'']

  have hml : evalp O ml_1 ⟪o, n+4, inp⟫ = ml := by
    have := @hlookup (left.comp m_1) (by simp [hm, m, div2_val, c_replace_oracle_evp_aux_nMod4_bounds1])
    simp [ml_1, this, hm]
    rfl
  have hmr : evalp O mr_1 ⟪o, n+4, inp⟫ = mr := by
    have := @hlookup (right.comp m_1) (by simp [hm, m, div2_val, c_replace_oracle_evp_aux_nMod4_bounds2])
    simp [mr_1, this, hm]
    rfl
  have hmp : evalp O mp_1 ⟪o, n+4, inp⟫ = mp := by
    have := @hlookup m_1 (by simp [hm, m, div2_val, c_replace_oracle_evp_aux_nMod4_bounds3])
    simp [mp_1, this, hm]
    rfl
  have hpair_code : evalp O pair_code ⟪o, n+4, inp⟫ = 2 * (2 * ⟪ml, mr⟫) + 5 := by simp [pair_code, hml, hmr, mul_comm]
  have hcomp_code : evalp O comp_code ⟪o, n+4, inp⟫ = 2*(2*⟪ml, mr⟫  ) +1  + 5 := by simp [comp_code, hml, hmr, mul_comm]
  have hprec_code : evalp O prec_code ⟪o, n+4, inp⟫ = 2*(2*⟪ml, mr⟫ +1 )   + 5 := by simp [prec_code, hml, hmr, mul_comm]
  have hrfind'_code : evalp O rfind'_code ⟪o, n+4, inp⟫ = 2*(2*(mp)  +1)+1   + 5 := by simp [rfind'_code, hmp, mul_comm]

  simp [← hinp]
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

lemma codes_aux_aux_0 (hno : n.bodd = false) :  2 * n.div2 = n := by
  have h0 := bodd_add_div2 n
  simp [hno] at h0
  exact h0
lemma codes_aux_aux_1 (hno : n.bodd = true) :  2 * n.div2 +1 = n := by
  have h0 := bodd_add_div2 n
  simp [hno] at h0
  rw (config:={occs:=.pos [2]}) [←h0]
  exact Nat.add_comm (2 * n.div2) 1
lemma codes_aux_0 (hno : n.bodd = false) (hn2o : n.div2.bodd = false) : 2 * (2 * n.div2.div2) = n := by
  rw [codes_aux_aux_0 hn2o]
  rw [codes_aux_aux_0 hno]
lemma codes_aux_1 (hno : n.bodd = true) (hn2o : n.div2.bodd = false) : 2 * (2 * n.div2.div2 ) +1 = n := by
  rw [codes_aux_aux_0 hn2o]
  rw [codes_aux_aux_1 hno]
lemma codes_aux_2 (hno : n.bodd = false) (hn2o : n.div2.bodd = true) : 2 * (2 * n.div2.div2 + 1) = n := by
  rw [codes_aux_aux_1 hn2o]
  rw [codes_aux_aux_0 hno]
lemma codes_aux_3 (hno : n.bodd = true) (hn2o : n.div2.bodd = true) : 2 * (2 * n.div2.div2 + 1)+1 = n := by
  rw [codes_aux_aux_1 hn2o]
  rw [codes_aux_aux_1 hno]

theorem nMod4_eq_0 (hno:n.bodd=false) (hn2o:n.div2.bodd=false) : n%4=0 := by rw [←codes_aux_0 hno hn2o]; omega
theorem nMod4_eq_1 (hno:n.bodd=true ) (hn2o:n.div2.bodd=false) : n%4=1 := by rw [←codes_aux_1 hno hn2o]; omega
theorem nMod4_eq_2 (hno:n.bodd=false) (hn2o:n.div2.bodd=true ) : n%4=2 := by rw [←codes_aux_2 hno hn2o]; omega
theorem nMod4_eq_3 (hno:n.bodd=true ) (hn2o:n.div2.bodd=true ) : n%4=3 := by rw [←codes_aux_3 hno hn2o]; omega

@[simp] theorem c_replace_oracle_evp: evalp O (c_replace_oracle) = λ x ↦c2n (replace_oracle (n2c x.l) (n2c x.r)) := by
  funext oc
  let o:=oc.l
  let c:=oc.r
  have oc_eq : oc = Nat.pair o c := by exact Eq.symm (pair_unpair oc)
  rw [oc_eq]
  simp only [pair_l, pair_r] -- simplify the rhs
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
          simp [replace_oracle, replace_oracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          -- rw [c_replace_oracle_evp_aux_nMod4_0 h0]
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1];
          · rw [ih m.r _m2];
        -- prec
        | true =>
          have h0: n%4=2 := nMod4_eq_2 hno hn2o
          simp [replace_oracle, replace_oracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1];
          · rw [ih m.r _m2];
      | true => cases hn2o:n.div2.bodd with
        -- comp
        | false =>
          have h0: n%4=1 := nMod4_eq_1 hno hn2o
          simp [replace_oracle, replace_oracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          constructor
          · rw [ih m.l _m1];
          · rw [ih m.r _m2];
        -- rfind
        | true =>
          have h0: n%4=3 := nMod4_eq_3 hno hn2o
          simp [replace_oracle, replace_oracle, n2c, c2n, hno, hn2o] -- simplify the rhs
          rw [c_replace_oracle_evp_aux_nMod4]
          simp [h0]
          rw [ih m hm];

@[simp] theorem c_replace_oracle_ev:eval O (c_replace_oracle) = λ x:ℕ ↦ c2n (replace_oracle (n2c x.l) (n2c x.r)) := by rw [← evalp_eq_eval c_replace_oracle_prim]; simp only [c_replace_oracle_evp];

@[simp] theorem plift_eq (ho:code_total O o) : (@PFun.lift ℕ ℕ fun x ↦ (eval O o x).get (ho x) )= eval O o := by
  ext a b : 1
  simp_all only [PFun.coe_val, Part.some_get]

theorem eval_replace_oracle_prop {O o c} (ho:code_total O o) : eval O (replace_oracle o c) = eval (λ x ↦ (eval O o x).get (ho x)) c := by
  unfold replace_oracle
  induction c <;> (simp [eval]; try (unfold replace_oracle; simp_all))
end Computability.Code
end replace_oracle
