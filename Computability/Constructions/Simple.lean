/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.Simple

open Computability.Code
open Computability


-- def c_bdd_total_search (c:Code) := zero
-- theorem c_bdd_total_search_evp : evalp O (c_bdd_total_search c) x = 0 ↔ ∀ y≤x, evalp O c y = 0 := by
--   sorry


/-
`c_bdd_search c` is a primrec code that, on input `⟪x, l⟫`, evaluates:
  `[c](x,0)`
  `[c](x,1)`
  ... up to
  `[c](x,l)`,
  until one of the computations return a non-zero output. Suppose `[c](x,i)` is the first such computation.

  Then, `some ⟪i, [c](x,i)⟫` is returned.

  If no such value is found, `none` is returned.

  The code `c` must be total.
-/
def c_bdd_search (c:Code) := prec
  (
    pair zero $ c_eval.comp₂ c (pair c_id (c_const 0))
  ) -- abusing the fact that ⟪0,0⟫ = 0 = Option.none
  (
    let prev_comp := right.comp right
    let iP1 := left.comp right
    let computation := c_eval.comp₂ c (pair c_id iP1)

    c_ifz.comp₃ prev_comp
    (c_ifz.comp₃ computation zero (pair iP1 computation))
    prev_comp
    -- pair zero $ c_eval.comp₂ c (pair c_id iP1)
  )
theorem c_bdd_search_evp_total (h:code_total O c) : code_total O (c_bdd_search c) := by
  sorry
theorem c_bdd_search_evp_0 (h:code_total O c) :
  (eval O (c_bdd_search c) ⟪x, l⟫).get (c_bdd_search_evp_total h ⟪x, l⟫) = 0
  ↔
  ∀ i ≤ l, (eval O c ⟪x,i⟫).get (h ⟪x,i⟫) = 0 := by
  sorry

theorem c_bdd_search_evp_1 (h:code_total O c) :
  ⟪i, r⟫ ∈ ((eval O (c_bdd_search c) ⟪x, l⟫).get (c_bdd_search_evp_total h ⟪x, l⟫) : Option ℕ)
  ↔
  r ∈ ((eval O c ⟪x,i⟫).get (h ⟪x,i⟫) : Option ℕ) ∧ ∀ j ≤ i,(eval O c ⟪x,j⟫).get (h ⟪x,j⟫) = 0 := by
  sorry
--   by sorry

-- note. i can offload some of the conditions below to C, from C_aux
/-
`C_aux` is a code that checks, on input `⟪i, s, R⟫`, the following:
  1. i ≤ s
  2. ¬ fs_in R i
  3. ∃ x ∈ Wn ∅ i s, x > 2*i,
  and returns the minimal `x` in condition 3.
-/
def C_aux : Code := zero
theorem C_aux_evp_0 : x ∈ (evalp Nat.fzero C_aux ⟪⟪s,R⟫, i⟫ : Option ℕ) → i ≤ s ∧ ¬ fs_in R i ∧ x ∈ Wn ∅ i s ∧ x > 2*i := by
  sorry
theorem C_aux_evp_2 : (i ≤ s ∧ ¬ fs_in R i ∧ ∃ x ∈ Wn ∅ i s, x > 2*i) → (evalp Nat.fzero C_aux ⟪⟪s,R⟫, i⟫ : Option ℕ).isSome := by
  sorry
theorem C_aux_evp_1 : evalp Nat.fzero C_aux ⟪⟪s,R⟫, i⟫ = 0 ↔ (¬ fs_in R i → ∀ x ∈ Wn ∅ i s, x ≤ 2*i) := by
  sorry
theorem C_aux_total : code_total O C_aux := by
  sorry


section list_foldr_param
namespace Computability.Code
def c_list_foldr_param_aux (cf:Code) :=
  let param := left
  let init := left.comp right
  let lN := right.comp right
  (c_list_foldr $
  (pair (left.comp left) $ cf.comp₃ (left.comp left) (right.comp left) (right.comp right))).comp₂
  (pair param init)
  ((c_list_zipWith c_id).comp₂ (c_list_replicate.comp₂ (c_list_length.comp lN) (param)) lN)
def c_list_foldr_param (cf:Code) := right.comp (c_list_foldr_param_aux cf)
@[cp] theorem c_list_foldr_param_aux_prim (hcf:code_prim cf) : code_prim (c_list_foldr_param_aux cf) := by
  rewrite [c_list_foldr_param_aux]
  apply_rules (config := {maxDepth:=30, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
theorem auxaux {f: ℕ→ℕ} : List.foldr (fun a b ↦ ⟪a.l,f ⟪a.l,⟪a.r,b.r⟫⟫⟫) ⟪param,init⟫
    (List.zipWith (fun (x y : ℕ) ↦ ⟪x,y⟫) (List.replicate (l).length param) (l)) =
  ⟪param,List.foldr (fun a b ↦ f ⟪param,⟪a,b⟫⟫) init (l)⟫ := by
    induction l with
    | nil => simp
    | cons head tail ih =>
      simp
      have : (List.zipWith (fun x y ↦ ⟪x,y⟫) (List.replicate (tail.length + 1) param) (head :: tail)) = ⟪param, head⟫ :: (List.zipWith (fun x y ↦ ⟪x,y⟫) (List.replicate tail.length param) tail) := by
        rfl
      simp only [this]
      simp [ih]
@[simp] theorem c_list_foldr_param_aux_evp : evalp O (c_list_foldr_param_aux cf) ⟪param, init, lN⟫ =
  Nat.pair param
  (
    List.foldr
    (fun a b => evalp O cf ⟪param, a, b⟫)
    (init)
    (n2l lN)
  )
  := by
    simp [c_list_foldr_param_aux]
    exact auxaux
@[simp] theorem c_list_foldr_param_evp : evalp O (c_list_foldr_param cf) ⟪param, init, lN⟫ =
  (
    List.foldr
    (fun a b => evalp O cf ⟪param, a, b⟫)
    (init)
    (n2l lN)
  ) := by
    simp [c_list_foldr_param]
end Computability.Code
end list_foldr_param


section fs_in
namespace Computability.Code
def c_fs_in := c_mod.comp₂
  (c_div.comp₂ left (c_pow.comp₂ (c_const 2) right))
  (c_const 2)
@[cp] theorem c_fs_in_prim : code_prim c_fs_in := by
  unfold c_fs_in
  apply_rules (config := {maxDepth:=30, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
@[simp] theorem c_fs_in_evp: evalp O c_fs_in ⟪x,y⟫ = (b2n $ fs_in x y) := by
  simp [c_fs_in,evalp];
  simp [fs_in, b2n]
  grind
end Computability.Code
end fs_in

section fs_add
namespace Computability.Code
def c_fs_add := c_ifz.comp₃
  (c_fs_in.comp c_id)
  (c_add.comp₂ left (c_pow.comp₂ (c_const 2) right))
  (left)
@[cp] theorem c_fs_add_prim : code_prim c_fs_add := by
  unfold c_fs_add
  apply_rules (config := {maxDepth:=30, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
theorem c_fs_add_aux (x y : ℕ) : x.testBit y ↔ x = x ||| (2^y) := by
  constructor
  intro h
  apply Nat.eq_of_testBit_eq
  grind
  intro h
  grind
@[simp] theorem c_fs_add_evp: evalp O c_fs_add ⟪x,y⟫ = (fs_add x y) := by
  simp [c_fs_add,evalp];
  simp [fs_add, fs_in, b2n]
  sorry

end Computability.Code
end fs_add



open Classical in
noncomputable def step (s:ℕ) := λ i prev ↦
  let Aₚ := prev.l
  let Rₚ := prev.r
  if ¬ fs_in Rₚ i then
    if found : ∃ x ∈ Wn ∅ i s, x > 2*i then
      let x := Nat.find found
      ⟪fs_add Aₚ x, fs_add Rₚ i⟫
    else prev
  else prev
def c_step :=
  let s := left
  let i := left.comp right
  let prev := right.comp right

  let Aₚ := left.comp prev
  let Rₚ := right.comp prev
  c_ifz.comp₃ (c_sg'.comp $ c_fs_in.comp₂ Rₚ i)
  (
    let search := zero
    c_ifz.comp₃ (search)
      (pair (c_fs_add.comp₂ Aₚ search) (c_fs_add.comp₂ Rₚ i))
    prev
  )
  prev
@[simp] theorem c_step_evp : evalp O c_step = λ x:ℕ ↦ Simple.step x.l x.r.l x.r.r := by

  sorry

def c_C :=
  (
    prec
    zero $
    let s := left.comp right
    let prev := right.comp right
    (c_list_foldr_param c_step).comp₃ s prev (c_list_reverse.comp $ c_list_range.comp s)
  ).comp₂ zero c_id

theorem c_C_evp : evalp O c_C = Simple.C := by
  funext x
  induction x with
  | zero =>
    simp [c_C]
    unfold Simple.C
    rfl
  | succ s ih =>
    unfold Simple.C
    rw [←ih]
    simp [c_C, -List.foldr_reverse]

#exit

def c_simple := zero
theorem c_simple_ev : W ∅ c_simple = Simple.A := by sorry

theorem exists_simple_set : ∃ A:Set ℕ, simpleIn ∅ A := by
  use Simple.A
  rw [←c_simple_ev]
  apply simpleInReq.mp
  constructor
  ·
    rw [c_simple_ev]
    exact Simple.A_CoInfinite
  intro c inf
  have a0 := Simple.P c
  simp at a0
  have := a0 inf
  rw [c_simple_ev]
  exact Set.nonempty_iff_ne_empty.mp (a0 inf)
