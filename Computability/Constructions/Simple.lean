/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Bitwise
import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.Simple

/-!
# Constructions/Simple.lean

This file constructs the function `Simple.C` from Simple.lean as a code.

The overall structure of the proof is written to facilitate adapation to proving the construction of
a low simple set, which will be done in Constructions/Post.lean.

## Structure
The difficult part of the construction is in implementing the search procedure of a `x` s.t.
`∃ x ∈ Wn ∅ i s, x > 2*i`.

This is done using `c_bdd_search`, which searches for a `x` that halts on code `c` for `s`
steps, from a specified lower bound to an upper bound. `c` and `s` are specified from the input.

Once the search procedure can be defined, `Simple.step`, and in turn `Simple.C`, can be constructed
as codes (`c_step` and `c_C` respectively) easily.

Then, we can define `c_simple` such that its domain is exactly `Simple.A`;
we let `c_simple` search (by dovetailing) for a step `s` such that its input is in `(C s).l`.

## Main declarations

- `c_C`: The code which implements `Simple.C`.
- `c_simple`: The code whose domain is `Simple.A`.
- `c_simple_ev`: Asserts that the domain of `c_simple` is `Simple.A`.
- `exists_simple_set`: Asserts the existence of a simple set.

-/

open Oracle.Single
open Oracle.Single.Code
open Computability


/--
`c_bdd_search c` is a primrec code that, on input `⟪(s, a, k), l⟫`, evaluates:
  let e := [c]⟪s, a, k⟫
  `[e]ₛ(a+0)`
  `[e]ₛ(a+1)`
  ... up to
  `[e]ₛ(a+l)`,
  until one of the computations halt. Suppose `[e]ₛ(a+i)` is the first such computation.

  Then, `some ⟪a+i, [e](a+i)⟫` is returned.

  If no such value is found, `none` is returned.
-/
def c_bdd_search (c : Code) := prec
  (
    let compt := c_evaln.comp₃ (left.comp right) c (left) -- = [e]ₛ(a)
    c_ifz.comp₃ compt zero <|
    succ.comp <| pair zero <| c_pred.comp compt
  )
  (
    let prev_comp := right.comp right -- = [e]ₛ(a+i)
    let iP1 := succ.comp <| left.comp right
    let s := left.comp left
    let a := left.comp <| right.comp left
    let k := right.comp <| right.comp left
    let aPi := c_add.comp₂ a <| iP1
    let computation := c_evaln.comp₃ (aPi) (c.comp₃ s a k) s -- = [e]ₛ(a+i+1)
    c_ifz.comp₃ prev_comp
    (
      c_ifz.comp₃ computation
      zero
      (succ.comp <| pair iP1 <| c_pred.comp computation)
    )
    prev_comp
  )
@[cp] theorem c_bdd_search_prim {c} (h : code_prim c) : code_prim <| c_bdd_search c := by
  unfold c_bdd_search
  lift_lets
  extract_lets
  expose_names
  have hcompt : code_prim compt := by apply_cp
  have hprev_comp : code_prim prev_comp := by apply_cp
  have hiP1 : code_prim iP1 := by apply_cp
  have hs : code_prim s := by apply_cp
  have ha : code_prim a := by apply_cp
  have hk : code_prim k := by apply_cp
  have haPi : code_prim aPi := by apply_cp
  apply_cp 60

theorem c_bdd_search_evp_0 {O c s a k l} :
  (evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, l⟫) = 0
  ↔
  ∀ i ≤ l, (evaln O s (evalp O c ⟪s,a,k⟫) (a+i)) = Option.none := by
  induction l with
  | zero => simp [c_bdd_search,  ← o2n_a0]
  | succ n ih =>
    unfold c_bdd_search
    lift_lets; extract_lets; expose_names
    simp only [evp_simps]
    simp only [Nat.unpaired, Nat.unpair_pair, Nat.pred_eq_sub_one, Nat.succ_eq_add_one]
    -- we will simplify terms in the goal with inp
    let (eq := hinp) inp := ⟪⟪s,a,k⟫, ⟪n,evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫⟫⟫
    unfold c_bdd_search at hinp; lift_lets at hinp;
    simp only [evp_simps] at hinp
    simp only [Nat.unpaired, Nat.unpair_pair, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] at hinp
    rw [← hinp]
    have hprev_comp : evalp O prev_comp inp = evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫ := by
      unfold c_bdd_search
      lift_lets;
      simp [prev_comp, hinp]
    -- show that the code let-bindings correspond to our let-bindings
    have hs_1 : evalp O s_1 inp = s := by simp [s_1, inp]
    have ha_1 : evalp O a_1 inp = a := by simp [a_1, inp]
    have hk_1 : evalp O k_1 inp = k := by simp [k_1, inp]
    have hiP1 : evalp O iP1 inp = n+1 := by simp [iP1, inp]
    have haPi : evalp O aPi inp = a+(n+1) := by simp [aPi, ha_1, hiP1]
    simp only [hprev_comp]
    have hcomputation :
        evalp O computation inp = o2n (evaln O s (evalp O c ⟪s,a,k⟫) (a+(n+1))) := by
      simp [computation, hs_1, haPi, ha_1, hk_1]
    simp only [hcomputation, hiP1]
    split at ⊢
    next h2 =>
      have ih1 := ih.mp h2
      split at ⊢
      next h3 =>
        simp only [true_iff]
        intro i hi
        cases hi : Nat.le_or_eq_of_le_succ hi with
        | inl h => exact ih1 i h
        | inr h =>
          simpa [h] using o2n_a0.mp h3
      next h3 =>
        constructor
        · intro h
          simp at h
        · intro h
          have := o2n_a0.mpr <| h (n+1) (le_refl (n+1))
          simp [h3] at this
    next h2 =>
      constructor
      · intro h
        simp [h2] at h
      · intro h
        apply ih.mpr ?_
        exact fun i hi ↦ h i (Nat.le_add_right_of_le hi)
theorem c_bdd_aux {x} (h : x ≠ 0) : ∃ y z, ⟪y, z⟫ ∈ n2o x := by
  use (x-1).l; use (x-1).r
  simp [encode_nonzero_opt h]
theorem c_bdd_search_evp_1 {O c s a k l i r} :
    ⟪i, r⟫ ∈ (n2o (evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, l⟫))
    ↔
    i ≤ l ∧
    r ∈ ((evaln O s (evalp O c ⟪s,a,k⟫) (a+i))) ∧
    ∀ j < i,(evaln O s (evalp O c ⟪s,a,k⟫) (a+j)) = none := by
  induction l generalizing i r with
  | zero =>
    simp only [c_bdd_search, evp_simps]
    simp only [Nat.unpaired, Nat.unpair_pair, pair_l, Nat.n2c, pair_r, Nat.pred_eq_sub_one,
      Nat.succ_eq_add_one, Nat.unpaired2, Nat.add_eq, Nat.rec_zero, Option.mem_def,
      nonpos_iff_eq_zero]
    apply Iff.intro
    · intro a_1
      apply And.intro
      · split at a_1
        next h => simp_all only [hnat_to_opt_0, reduceCtorEq]
        next h => simp_all only [hnat_to_opt_0', Option.some.injEq, Nat.pair_eq_pair]
      · apply And.intro
        · split at a_1
          next h => simp_all only [hnat_to_opt_0, reduceCtorEq]
          next h =>
            simp_all only [hnat_to_opt_0', Option.some.injEq, Nat.pair_eq_pair]
            obtain ⟨left, right⟩ := a_1
            subst right left
            simp_all only [add_zero]
            have : (evaln O s (n2c (evalp O c ⟪s,a,k⟫)) a).isSome := by
              exact hnat_10 h
            exact hnat_11 this
        · intro j a_2
          split at a_1
          next h => simp_all only [hnat_to_opt_0, reduceCtorEq]
          next h =>
            simp_all only [hnat_to_opt_0', Option.some.injEq, Nat.pair_eq_pair]
            obtain ⟨left, right⟩ := a_1
            subst left right
            simp_all only [not_lt_zero']
    · intro a_1
      simp_all only
      obtain ⟨left, right⟩ := a_1
      obtain ⟨left_1, right⟩ := right
      subst left
      simp_all
  | succ n ih =>
    unfold c_bdd_search
    lift_lets; extract_lets; expose_names
    simp only [evp_simps]
    simp only [Nat.unpaired, Nat.unpair_pair, Nat.pred_eq_sub_one, Nat.succ_eq_add_one,
      Option.mem_def]
    let (eq := hinp) inp := ⟪⟪s,⟪a,k⟫⟫, ⟪n,evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫⟫⟫
    unfold c_bdd_search at hinp; lift_lets at hinp;
    simp only [evp_simps] at hinp
    simp only [Nat.unpaired, Nat.unpair_pair, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] at hinp
    rw [← hinp]
    have hprev_comp : evalp O prev_comp inp = evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫ := by
      unfold c_bdd_search
      lift_lets;
      simp [prev_comp, hinp]
    have hs_1 : evalp O s_1 inp = s := by simp [s_1, inp]
    have ha_1 : evalp O a_1 inp = a := by simp [a_1, inp]
    have hk_1 : evalp O k_1 inp = k := by simp [k_1, inp]
    have hiP1 : evalp O iP1 inp = n+1 := by simp [iP1, inp]
    have haPi : evalp O aPi inp = a+(n+1) := by simp [aPi, ha_1, hiP1]
    have hcomputation :
        evalp O computation inp = o2n (evaln O s (evalp O c ⟪s,a,k⟫) (a+(n+1))) := by
      simp [computation, hs_1, haPi, ha_1, hk_1]
    simp only [hprev_comp, hcomputation, hiP1]
    split
    next h =>
      split
      next h2 =>
        simp only [hnat_to_opt_0, reduceCtorEq, false_iff, not_and, not_forall]
        intro hi h3
        cases Nat.eq_or_lt_of_le hi with
        | inl h4 =>
          simp [← h4] at h2
          simp [h3] at h2
        | inr h4 => simp [c_bdd_search_evp_0.mp h i (Nat.le_of_lt_succ h4)] at h3
      next h2 =>
        simp only [hnat_to_opt_0', Option.some.injEq, Nat.pair_eq_pair]
        constructor
        · rintro ⟨h3,h4⟩
          rw [h3] at h2 h4 ⊢
          constructor
          · exact le_refl i
          constructor
          · simp only [hnat_2 (hnat_10 h2)] at h4
            rw [← h4]
            simp
          intro j hj
          rw [← h3] at hj
          exact c_bdd_search_evp_0.mp h j (Nat.le_of_lt_succ hj)
        simp only [and_imp]
        intro hi h3 h4
        have : n + 1 = i := by
          have : i = n+1 ∨ i< n+1 := Nat.eq_or_lt_of_le hi
          cases this with
          | inl h => simp [h]
          | inr h5 =>
            have := c_bdd_search_evp_0.mp h i (Nat.le_of_lt_succ h5)
            simp [this] at h3
        simp [this, h3]
    next h =>
      constructor
      · intro h2
        rcases ih.mp h2 with ⟨h3, h4, h5⟩
        exact ⟨Nat.le_succ_of_le h3, h4, h5⟩
      simp only [and_imp]
      intro hi h2 h3
      apply ih.mpr
      simp only [Option.mem_def]
      constructor
      · cases Nat.eq_or_lt_of_le hi with
        | inl h5 =>
          clear hi
          rcases c_bdd_aux h with ⟨y, z, hyz⟩
          rcases ih.mp hyz with ⟨_, h7, _⟩
          simp [h5]
          simp [h3 y (by omega)] at h7
        | inr h => exact Nat.le_of_lt_succ h
      exact ⟨h2,h3⟩

section fs_in
namespace Oracle.Single.Code
def c_fs_in := c_mod.comp₂
  (c_div.comp₂ left (c_pow.comp₂ (c_const 2) right))
  (c_const 2)
@[cp] theorem c_fs_in_prim : code_prim c_fs_in := by unfold c_fs_in; apply_cp
@[simp, evp_simps] theorem c_fs_in_evp {O x y} : evalp O c_fs_in ⟪x,y⟫ = (b2n <| fs_in x y) := by
  simp [c_fs_in,evalp];
  simp [fs_in, b2n]
  grind
end Oracle.Single.Code
end fs_in

section fs_add
namespace Oracle.Single.Code
def c_fs_add := c_or.comp₂ left <| c_pow.comp₂ (c_const 2) right
@[cp] theorem c_fs_add_prim : code_prim c_fs_add := by unfold c_fs_add; apply_cp
@[simp, evp_simps] theorem c_fs_add_evp {O x y} : evalp O c_fs_add ⟪x,y⟫ = (fs_add x y) := by
  simp [c_fs_add,evalp];
end Oracle.Single.Code
end fs_add

theorem evaln_dom_imp_x_le_s {O s c x} (h : (evaln O s c x).isSome) : x ≤ s := by
  contrapose h
  simp only [not_le, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h ⊢
  cases s with
  | zero => simp [evaln]
  | succ n => cases c <;> simp [evaln, not_le.mpr (Nat.lt_of_succ_lt h)];

/--
A code which satisfies: `evalp (χ ∅) c_step ⟪s, i, prev⟫ = Simple.step s i prev`.

Compare the defn below to the defn of `Simple.step`.

The nontrivial part of implementing `Simple.step` is the following part:
```
if found : ∃ x ∈ Wn ∅ i s, x > 2*i then
  let x := Nat.find found
```

We use `c_bdd_search` to implement this part.

We want to search, from y=2*i+1 to s, a value s.t. [i]_s(y) halts.

`search` is 0 if `found` is false, otherwise is the minimal `a+1` s.t.
`[i]_s(2*i+1+a)↓`.
-/
def c_step :=
  let s := left
  let i := left.comp right
  let prev := right.comp right
  let Aₚ := left.comp prev
  let Rₚ := right.comp prev
  let i2P1 := succ.comp <| c_mul.comp₂ (c_const 2) <| left.comp right
  c_ifz.comp₃ (c_sg'.comp <| c_fs_in.comp₂ Rₚ i)
  prev
  (
    let search := (c_bdd_search (right.comp right)).comp₂ (pair s <| pair i2P1 i) s
    let x := c_add.comp₂ i2P1 (left.comp <| c_pred.comp search)
    c_ifz.comp₃ search
    prev
    (pair (c_fs_add.comp₂ Aₚ x) (c_fs_add.comp₂ Rₚ i))
  )
@[cp] theorem c_step_prim : code_prim c_step := by
  unfold c_step
  lift_lets; extract_lets; expose_names
  have hs : code_prim s := by apply_cp
  have hi : code_prim i := by apply_cp
  have hprev : code_prim prev := by apply_cp
  have hAₚ : code_prim Aₚ := by apply_cp
  have hRₚ : code_prim Rₚ := by apply_cp
  have hi2P1 : code_prim i2P1 := by apply_cp
  have hsearch : code_prim search := by apply_cp
  have hx : code_prim x := by apply_cp
  apply_cp 60
@[simp, evp_simps] theorem c_step_evp {s i prev} :
    evalp (χ ∅) c_step ⟪s, i, prev⟫ = Simple.step s i prev := by
  unfold Simple.step
  unfold c_step
  lift_lets; extract_lets; expose_names
  simp only [evp_simps]
  simp only [Nat.sg', ite_eq_right_iff, one_ne_zero, imp_false, ite_not,
    Bool.not_eq_true, Set.mem_setOf_eq, gt_iff_lt]
  let (eq := hinp) inp := ⟪s, i, prev⟫
  rw [← hinp]
    -- show that the code let-bindings correspond to our let-bindings
  have hprev : (evalp (χ ∅) prev_1 inp) = prev := by simp [prev_1, inp]
  have hRp_1 : (evalp (χ ∅) Rₚ inp) = Rₚ_1 := by simp [Rₚ, hprev, Rₚ_1]
  have hAₚ_1 : (evalp (χ ∅) Aₚ inp) = Aₚ_1 := by simp [Aₚ, hprev, Aₚ_1]
  have hi :    (evalp (χ ∅) i_1 inp) = i := by simp [i_1, inp]
  have hs :    (evalp (χ ∅) s_1 inp) = s := by simp [s_1, inp]
  have hi2P1 : (evalp (χ ∅) i2P1 inp) = 2*i+1 := by simp [i2P1, inp]
  simp only [hRp_1, hi, hprev, hAₚ_1, gt_iff_lt]
  split; rotate_left
  next h0 =>
    simp [b2n] at h0
    simp [h0]
  next h0 =>
    simp only [b2n, ite_eq_right_iff, one_ne_zero, imp_false, Bool.not_eq_true] at h0
    simp only [h0, ↓reduceIte, gt_iff_lt]
    clear h0
    split; rotate_left
    next h0 =>
      unfold search at h0
      simp only [hs, evp_simps] at h0
      rcases c_bdd_aux h0 with ⟨z,r, hzr⟩
      simp only [hi2P1, hi, Option.mem_def] at hzr
      rcases c_bdd_search_evp_1.mp hzr with ⟨hzr1, hzr2, hzr3⟩
      simp only [evalp, pair_r, Option.mem_def] at hzr1 hzr2 hzr3
      have found_aux : (evalnSet ∅ s (n2c i) (2*i+1+z)).isSome = true ∧ (2*i+1+z) > 2 * i := by
        constructor
        · simp only [evalnSet]
          rw [hzr2]
          rfl
        omega
      have found : ∃ x_1, (evalnSet ∅ s (n2c i) x_1).isSome = true ∧ x_1 > 2 * i := by
        use 2*i+1+z
      simp only [gt_iff_lt, found, ↓reduceDIte, Nat.pair_eq_pair, and_true]
      apply congrArg
      simp? [x, search, hs, hi, hi2P1] says
        simp only [evp_simps, hi2P1, hs, hi, Nat.pred_eq_sub_one,
          Nat.unpaired2, pair_l, pair_r, Nat.add_eq, x, search]
      simp only [hnat_12 hzr, pair_l]
      let (eq := hnf) nf := Nat.find found
      have nf0 := @Nat.find_min _ _ found
      have nf1 := @Nat.find_spec _ _ found
      rw [← hnf] at nf0 nf1 ⊢
      have tri := lt_trichotomy (2 * i + 1 + z) nf
      cases tri with
      | inl h =>
        have := @nf0 (2 * i + 1 + z) h
        simp only [gt_iff_lt, not_and, not_lt] at this
        have := this found_aux.1
        omega
      | inr h =>
      cases h with
      | inl h => exact h
      | inr h =>
        have a2 : nf - 2*i-1 < z := by omega
        have a3 := hzr3 (nf - 2*i-1) a2
        have a4 : (2 * i + 1 + (nf - 2 * i - 1)) = nf := by omega
        simp [a4] at a3
        simp [evalnSet] at nf1
        simp [a3] at nf1
    next h0 =>
      simp only [evp_simps, search, hi2P1, hi, hs] at h0
      have := c_bdd_search_evp_0.mp h0
      split; rotate_left
      next h1 => simp
      next h1 =>
        rcases h1 with ⟨h2,h3,h4⟩
        simp only [evalnSet, evp_simps] at h3
        have a0 : h2 ≤ s := evaln_dom_imp_x_le_s h3
        have a2 : h2-2*i-1 ≤ s := by omega
        have a1 := this (h2-2*i-1) a2
        simp only at a1
        have a3 : (2 * i + 1 + (h2 - 2 * i - 1)) = h2 := by omega
        simp [a3] at a1
        simp [a1] at h3

def c_C := c_prec1 0 <|
    let s := left
    let prev := right
    (c_list_foldr_param c_step).comp₃ s prev (c_list_reverse.comp <| c_list_range.comp s)

@[cp] theorem c_C_prim : code_prim c_C := by unfold c_C; apply_cp

@[simp, evp_simps] theorem c_C_evp : evalp (χ ∅) c_C = Simple.C := by
  funext x
  induction x with
  | zero =>
    unfold Simple.C
    simpa [c_C] using by rfl
  | succ s ih =>
    unfold Simple.C
    rw [←ih]
    simp [c_C, -List.foldr_reverse]

def c_simple := dovetail <|
  let x := left
  let s := right
  c_sg'.comp <| c_fs_in.comp₂ (left.comp <| c_C.comp s) x

theorem W_eq_iff_mem {O c A} : W O c = A ↔ (∀ x, x∈A ↔ (evalSet O c x).Dom) := by
  simp only [W]
  constructor
  · intro h
    rw [← h]
    intro x
    simp only [PFun.mem_dom]
    exact Iff.symm Part.dom_iff_mem
  intro h
  refine Set.ext ?_
  exact fun x ↦ (fun {a b} ↦ iff_comm.mp) (h x)

theorem c_simple_ev : W ∅ c_simple = Simple.A := by
  apply W_eq_iff_mem.mpr
  simp only [Simple.A, Set.mem_setOf_eq, c_simple]
  intro x
  have : code_prim (c_sg'.comp (c_fs_in.comp₂ (left.comp (c_C.comp right)) left)) := by apply_cp
  simp only [evalSet]
  constructor
  · intro h
    rcases h with ⟨s,hs⟩
    apply dovetail_ev_2.mpr
    use s
    simp [←evalp_eq_eval this]
    simp [hs, b2n]
  · intro h
    rcases dovetail_ev_2.mp h with ⟨s,hs⟩
    simp only [← evalp_eq_eval this, evp_simps] at hs
    simp only [Nat.sg', b2n, ite_eq_right_iff, one_ne_zero, imp_false, Bool.not_eq_true,
      PFun.coe_val, pair_r, pair_l, Part.some_inj, Bool.not_eq_false] at hs
    exact Exists.intro s hs

theorem exists_simple_set : ∃ A : Set ℕ, simpleIn ∅ A := by
  use Simple.A
  rw [←c_simple_ev]
  apply simpleInReq.mp
  constructor
  · rw [c_simple_ev]
    exact Simple.A_CoInfinite
  intro c inf
  have a0 := Simple.P c
  simp only [n2c_c2n] at a0
  have := a0 inf
  rw [c_simple_ev]
  exact Set.nonempty_iff_ne_empty.mp (a0 inf)
