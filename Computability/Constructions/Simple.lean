/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.EvalString
import Computability.SetOracles
import Computability.Simple

/-!
# Constructions/Simple.lean

This file constructs the function `Simple.C` from Simple.lean as a code.

The overall structure of the proof is written to facilitate adapation to proving the construction of a
low simple set, which will be done in Constructions/Post.lean.

## Structure
The difficult part of the construction is in implementing the search procedure of a `x` s.t.
`∃ x ∈ Wn ∅ i s, x > 2*i`.

This is done using `c_bdd_search`, which searches for an `x` that halts on code `c` for `s`
steps, from a specified lower bound to an upper bound. `c` and `s` are specified from the input.

Once the search procedure can be defined, `Simple.step`, and in turn `Simple.C`, can be constructed as codes
(`c_step` and `c_C` respectively) easily.

Then, we can define `c_simple` such that its domain is exactly `Simple.A`;
we let `c_simple` search (by dovetailing) for a step `s` such that its input is in `(C s).l`.

## Main declarations

- `c_C`:
- `c_simple`:
- `c_simple_ev`:
- `exists_simple_set`:

-/

open Computability.Code
open Computability


/-
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
def c_bdd_search (c:Code) := prec
  (
    let compt := c_evaln.comp₃ (left.comp right) c (left) -- = [e]ₛ(a)
    c_ifz.comp₃ compt zero $
    succ.comp $ pair zero $ c_pred.comp compt
  )
  (
    let prev_comp := right.comp right -- = [e]ₛ(a+i)
    let iP1 := succ.comp $ left.comp right
    let s := left.comp left
    let a := left.comp $ right.comp left
    let k := right.comp $ right.comp left
    let aPi := c_add.comp₂ a $ iP1
    let computation := c_evaln.comp₃ (aPi) (c.comp₃ s a k) s -- = [e]ₛ(a+i+1)

    c_ifz.comp₃ prev_comp
    (
      c_ifz.comp₃ computation
      zero
      (succ.comp $ pair iP1 $ c_pred.comp computation)
    )
    prev_comp
  )
@[cp] theorem c_bdd_search_prim (h:code_prim c):code_prim $ c_bdd_search c := by
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

theorem c_bdd_search_evp_0 :
  (evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, l⟫) = 0
  ↔
  ∀ i ≤ l, (evaln O s (evalp O c ⟪s,a,k⟫) (a+i)) = Option.none := by
  induction l with
  | zero => simp [c_bdd_search,  ← o2n_a0]
  | succ n ih =>
    unfold c_bdd_search
    lift_lets; extract_lets; expose_names
    simp [evalp]
    let (eq:=hinp) inp := ⟪⟪s,a,k⟫, ⟪n,evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫⟫⟫
    unfold c_bdd_search at hinp; lift_lets at hinp; simp at hinp
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
    simp [hprev_comp]
    have hcomputation : evalp O computation inp = o2n (evaln O s (evalp O c ⟪s,a,k⟫) (a+(n+1))) := by
      simp [computation, hs_1, haPi, ha_1, hk_1]
    simp [hcomputation, hiP1]
    split at ⊢
    next h2 =>
      have ih1 := ih.mp h2
      split at ⊢
      next h3 =>
        simp
        intro i hi
        cases hi:Nat.le_or_eq_of_le_succ hi with
        | inl h => exact ih1 i h
        | inr h =>
          simp [h]
          exact o2n_a0.mp h3
      next h3 =>
        constructor
        · intro h
          simp at h
        · intro h
          have := o2n_a0.mpr $ h (n+1) (le_refl (n+1))
          simp [h3] at this
    next h2 =>
      constructor
      · intro h
        simp [h2] at h
      · intro h
        apply ih.mpr ?_
        exact λ i hi ↦ h i (Nat.le_add_right_of_le hi)
theorem c_bdd_aux (h:x≠0) : ∃ y z, ⟪y, z⟫ ∈ n2o x := by
  use (x-1).l; use (x-1).r
  simp [hnat_to_opt_2 h]
theorem c_bdd_search_evp_1:
  ⟪i, r⟫ ∈ (n2o (evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, l⟫))
  ↔
  i ≤ l ∧ r ∈ ((evaln O s (evalp O c ⟪s,a,k⟫) (a+i))) ∧ ∀ j < i,(evaln O s (evalp O c ⟪s,a,k⟫) (a+j)) = none := by
  induction l generalizing i r with
  | zero =>
    simp [c_bdd_search]
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
    simp [evalp]
    let (eq:=hinp) inp := ⟪⟪s,⟪a,k⟫⟫, ⟪n,evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫⟫⟫
    unfold c_bdd_search at hinp; lift_lets at hinp; simp at hinp
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
    have hcomputation : evalp O computation inp = o2n (evaln O s (evalp O c ⟪s,a,k⟫) (a+(n+1))) := by
      simp [computation, hs_1, haPi, ha_1, hk_1]
    simp [hprev_comp, hcomputation, hiP1]
    split
    next h =>
      split
      next h2 =>
        simp
        intro hi h3
        cases Nat.eq_or_lt_of_le hi with
        | inl h4 =>
          simp [←h4] at h2
          simp [h3] at h2
        | inr h4 => simp [c_bdd_search_evp_0.mp h i (Nat.le_of_lt_succ h4)] at h3

      next h2 =>
        simp only [hnat_to_opt_0', Option.some.injEq, Nat.pair_eq_pair]
        constructor
        rintro ⟨h3,h4⟩
        rw [h3] at h2 h4 ⊢
        constructor
        · exact le_refl i
        constructor
        · simp [hnat_2 (hnat_10 h2)] at h4
          rw [←h4]
          simp

        intro j hj
        rw [←h3] at hj
        exact c_bdd_search_evp_0.mp h j (Nat.le_of_lt_succ hj)

        simp
        intro hi h3 h4
        have : n + 1 = i := by
          have : i = n+1 ∨ i< n+1 := Nat.eq_or_lt_of_le hi
          cases this with
          | inl h => simp [h]
          | inr h5 =>
            have := c_bdd_search_evp_0.mp h i (Nat.le_of_lt_succ h5)
            simp [this] at h3
        simp [this]
        simp [h3]


    next h =>
      constructor
      · intro h2
        rcases ih.mp h2 with ⟨h3, h4, h5⟩
        exact ⟨Nat.le_succ_of_le h3, h4, h5⟩
      simp
      intro hi h2 h3
      apply ih.mpr
      simp
      constructor
      ·
        cases Nat.eq_or_lt_of_le hi with
        | inl h5 =>
          clear hi
          simp [h5]
          have a0 := c_bdd_aux h
          rcases a0 with ⟨y,z,hyz⟩
          rcases ih.mp hyz with ⟨h6,h7,h8⟩
          simp [h3 y (by omega)] at h7
        | inr h => exact Nat.le_of_lt_succ h
      exact ⟨h2,h3⟩


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
@[cp] theorem c_list_foldr_param_aux_prim (hcf:code_prim cf) : code_prim (c_list_foldr_param_aux cf) := by unfold c_list_foldr_param_aux; apply_cp 60
@[cp] theorem c_list_foldr_param_prim (hcf:code_prim cf) : code_prim (c_list_foldr_param cf) := by
  rewrite [c_list_foldr_param]
  apply_cp 60
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
@[cp] theorem c_fs_in_prim : code_prim c_fs_in := by unfold c_fs_in; apply_cp
@[simp] theorem c_fs_in_evp: evalp O c_fs_in ⟪x,y⟫ = (b2n $ fs_in x y) := by
  simp [c_fs_in,evalp];
  simp [fs_in, b2n]
  grind
end Computability.Code
end fs_in

section bitwise
namespace Computability.Code
def c_bitwise_aux (c:Code) :=
  let iP1 := succ.comp (left.comp right)

  let comp_hist       := right.comp right
  let lookup (n'' m'')     := c_list_getI.comp₂ comp_hist (pair n'' m'')

  let n := left.comp iP1
  let m := right.comp iP1
  let n' := c_div.comp₂ n (c_const 2)
  let m' := c_div.comp₂ m (c_const 2)
  let b₁ := c_mod.comp₂ n (c_const 2)
  let b₂ := c_mod.comp₂ m (c_const 2)
  let r  := lookup n' m'

  c_cov_rec

  (c_const 0) $

  c_ifz.comp₃ n
    (c_ift.comp₃ (c.comp₂ zero (c_const 1)) m zero) $
  c_ifz.comp₃ m
    (c_ift.comp₃ (c.comp₂ (c_const 1) zero) n zero) $
  c_ift.comp₃ (c.comp₂ b₁ b₂)
  (succ.comp (c_add.comp₂ r r))
  (c_add.comp₂ r r)
def c_bitwise (c) := c_list_getLastI.comp ((c_bitwise_aux c).comp₂ (c_const 17) c_id)
@[cp] theorem c_bitwise_prim (hc:code_prim c) : code_prim (c_bitwise c) := by
  unfold c_bitwise;
  unfold c_bitwise_aux
  extract_lets;
  expose_names;
  have cpiP1 : code_prim iP1 := by apply_cp
  have cpcomp_hist : code_prim comp_hist := by apply_cp
  have cpn : code_prim n := by apply_cp
  have cpm : code_prim m := by apply_cp
  have cpn' : code_prim n' := by apply_cp
  have cpm' : code_prim m' := by apply_cp
  have cpb₁ : code_prim b₁ := by apply_cp
  have cpb₂ : code_prim b₂ := by apply_cp
  have cpr : code_prim r := by apply_cp
  apply_cp 50
theorem lt_pair_of_lt_lt (ha : a<c) (hb : b<d) : ⟪a,b⟫ < ⟪c,d⟫ := by
  have a0 : ⟪a,b⟫ < ⟪c,b⟫ := by exact Nat.pair_lt_pair_left b ha
  have a1 : ⟪c,b⟫ < ⟪c,d⟫ := by exact Nat.pair_lt_pair_right c hb
  exact Nat.lt_trans a0 a1
theorem c_bitwise_evp_rec_bounds {n m : ℕ} : ⟪(n + 1) / 2,(m + 1) / 2⟫ < ⟪n + 1,m + 1⟫ := by
  exact lt_pair_of_lt_lt (Nat.div_lt_self' n 0) (Nat.div_lt_self' m 0)
theorem c_bitwise_evp_0_0 : evalp O (c_bitwise c) ⟪0, 0⟫ = Nat.bitwise (fun a b => n2b $ evalp O c ⟪b2n a, b2n b⟫) 0 0 := by
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  rw [show Nat.pair 0 0 = 0 from rfl]
  simp
theorem c_bitwise_evp_0_m : evalp O (c_bitwise c) ⟪0, m+1⟫ = Nat.bitwise (fun a b => n2b $ evalp O c ⟪b2n a, b2n b⟫) 0 (m+1) := by
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  let k := ⟪0, m+1⟫ - 1
  have hkP1: k+1 = ⟪0, m+1⟫ := Nat.sub_add_cancel pair_nonzero_right_pos
  rw [← hkP1]
  -- more unfolding
  let (eq:=hinp) inp := evalp O (c_bitwise_aux c) ⟪17, k⟫
  let (eq:=hcri) cri := ⟪17, k, inp⟫
  unfold c_bitwise_aux at hinp; lift_lets at hinp
  simp [← hinp, ← hcri]
  -- simplify lets
  have hiP1 : evalp O iP1 cri = ⟪0,m+1⟫ := by simp [iP1, cri, hkP1]
  have hn : evalp O n cri = 0 := by simp [n, hiP1]
  have hm : evalp O m_1 cri = m+1 := by simp [m_1, hiP1]
  -- terminal simp
  simp [hn, hm, b2n]
theorem c_bitwise_evp_n_0 : evalp O (c_bitwise c) ⟪n+1, 0⟫ = Nat.bitwise (fun a b => n2b $ evalp O c ⟪b2n a, b2n b⟫) (n+1) 0 := by
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  let k := ⟪n+1, 0⟫ - 1
  have hkP1: k+1 = ⟪n+1, 0⟫ := Nat.sub_add_cancel pair_nonzero_left_pos
  rw [← hkP1]
  -- more unfolding
  let (eq:=hinp) inp := evalp O (c_bitwise_aux c) ⟪17, k⟫
  let (eq:=hcri) cri := ⟪17, k, inp⟫
  unfold c_bitwise_aux at hinp; lift_lets at hinp
  simp [← hinp, ← hcri]
  -- simplify lets
  have hiP1 : evalp O iP1 cri = ⟪n+1, 0⟫ := by simp [iP1, cri, hkP1]
  have hn : evalp O n_1 cri = n+1 := by simp [n_1, hiP1]
  have hm : evalp O m cri = 0 := by simp [m, hiP1]
  -- terminal simp
  simp [hn, hm, b2n]
theorem c_bitwise_evp_n_m : evalp O (c_bitwise c) ⟪n+1,m+1⟫ =
    (let n' := (n+1) / 2
    let m' := (m+1) / 2
    let b₁ := (n+1) % 2
    let b₂ := (m+1) % 2
    let r  := evalp O (c_bitwise c) ⟪n',m'⟫
    if n2b $ evalp O c ⟪b₁, b₂⟫ then
      r+r+1
    else
      r+r)
 := by
  lift_lets; extract_lets; expose_names
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  let k := ⟪n+1, m+1⟫ - 1
  have kP1_gt_0 : ⟪n+1, m+1⟫ > 0 := pair_nonzero_right_pos
  have hkP1: k+1 = ⟪n+1, m+1⟫ := by
    exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]

  let (eq:=hinp) inp := evalp O (c_bitwise_aux c) ⟪17, k⟫
  let (eq:=hcri) cri := ⟪17, k, inp⟫
  unfold c_bitwise_aux at hinp; lift_lets at hinp
  simp [← hinp, ← hcri]

  have hiP1 : evalp O iP1 cri = ⟪n+1,m+1⟫ := by simp [iP1, cri, hkP1]
  have hn : evalp O n_1 cri = n+1 := by simp [n_1, hiP1]
  have hm : evalp O m_1 cri = m+1 := by simp [m_1, hiP1]
  have hn' : evalp O n'_1 cri = n' := by simp [n'_1, hn, n']
  have hm' : evalp O m'_1 cri = m' := by simp [m'_1, hm, m']
  have hb₁ : evalp O b₁_1 cri = b₁ := by simp [b₁_1, hn, b₁]
  have hb₂ : evalp O b₂_1 cri = b₂ := by simp [b₂_1, hm, b₂]
  have hr : evalp O r_1 cri = r := by
    simp [r_1, lookup, comp_hist, hn', hm', cri, inp]
    simp [r]; unfold c_bitwise
    unfold c_bitwise_aux
    lift_lets
    have : ⟪n',m'⟫≤k := by
      simp [k]
      apply Nat.le_of_lt_succ
      simp [Nat.sub_add_cancel pair_nonzero_right_pos]
      exact c_bitwise_evp_rec_bounds
    simp [this]

  simp [hn, hm, hb₁, hb₂, hr]
lemma mod2 (h:¬ x%2=0) : x%2 =1 := by
  exact Nat.mod_two_ne_zero.mp h
@[simp] theorem c_bitwise_evp: evalp O (c_bitwise c) = Nat.unpaired2 (Nat.bitwise (fun a b => n2b $ evalp O c ⟪b2n a, b2n b⟫)) := by
  funext nm
  induction' nm using Nat.strong_induction_on with nm ih
  let n := nm.l
  let m := nm.r
  have nm_eq : nm = Nat.pair n m := by exact Eq.symm pair_lr
  rw [nm_eq]
  match hn_val:n, hm_val:m with
  | 0,    0    => simp [c_bitwise_evp_0_0]
  | 0,    m+1  => simp [c_bitwise_evp_0_m]
  | n+1,  0    => simp [c_bitwise_evp_n_0]
  | n+1,  m+1  =>
    simp [c_bitwise_evp_n_m]
    have b0 : ⟪(n+1)/2, (m+1)/2⟫ < nm := by
      simp [nm_eq]
      exact c_bitwise_evp_rec_bounds
    have ih0 := ih ⟪(n+1)/2, (m+1)/2⟫ b0
    have rw0 {x} : b2n (decide ((x + 1) % 2 = 1)) = (x + 1) % 2 := by
      cases Classical.em ((x + 1) % 2 = 1) with
      | inl h => simp [h, b2n]
      | inr h =>
        simp [h, b2n]
        exact (Nat.mod_two_ne_one.mp h).symm
    unfold Nat.bitwise
    simp [ih0]
    simp [rw0]
end Computability.Code
end bitwise

section lor
namespace Computability.Code
def c_lor := c_ifz.comp₃ left
  (c_ifz.comp₃ right zero (c_const 1))
  (c_const 1)
@[cp] theorem c_lor_prim : code_prim c_lor := by unfold c_lor; apply_cp
theorem c_lor_evp : evalp O c_lor ⟪a, b⟫ = b2n (n2b a || n2b b) := by
  simp [c_lor]
  simp [n2b, b2n]
  split
  next h => simp [h]
  next h => simp [h]
@[simp] theorem c_lor_evp' : (fun a b => n2b $ evalp O c_lor ⟪b2n a, b2n b⟫) = Bool.or := by
  simp [c_lor]
  funext a b;
  simp [n2b, b2n]
  split
  next h => simp [h]
  next h => simp [h]
end Computability.Code
end lor
section lxor
namespace Computability.Code
def c_lxor := c_ifz.comp₃ left
  (c_ifz.comp₃ right zero (c_const 1))
  (c_ifz.comp₃ right (c_const 1) zero)
@[cp] theorem c_lxor_prim : code_prim c_lxor := by unfold c_lxor; apply_cp
theorem c_lxor_evp : evalp O c_lxor ⟪a, b⟫ = b2n (n2b a ^^ n2b b) := by
  simp [c_lxor]
  simp [n2b, b2n]
  split
  next h => simp [h]
  next h => simp [h]
@[simp] theorem c_lxor_evp' : (fun a b => n2b $ evalp O c_lxor ⟪b2n a, b2n b⟫) = Bool.xor := by
  simp [c_lxor]
  funext a b;
  simp [n2b, b2n]
  split
  next h => simp [h]
  next h => simp [h]
end Computability.Code
end lxor
section land
namespace Computability.Code
def c_land := c_ifz.comp₃ left
  zero
  (c_ifz.comp₃ right zero (c_const 1))
@[cp] theorem c_land_prim : code_prim c_land := by unfold c_land; apply_cp
theorem c_land_evp : evalp O c_land ⟪a, b⟫ = b2n (n2b a && n2b b) := by
  simp [c_land]
  simp [n2b, b2n]
  split
  next h => simp [h]
  next h => simp [h]
@[simp] theorem c_land_evp' : (fun a b => n2b $ evalp O c_land ⟪b2n a, b2n b⟫) = Bool.and := by
  simp [c_land]
  funext a b;
  simp [n2b, b2n]
end Computability.Code
end land
section or
namespace Computability.Code
def c_or := c_bitwise (c_lor)
@[cp] theorem c_or_prim : code_prim c_or := by unfold c_or; apply_cp
@[simp] theorem c_or_evp: evalp O c_or ⟪x,y⟫ = (x ||| y) := by simp [c_or]; rfl
end Computability.Code
end or
section and
namespace Computability.Code
def c_and := c_bitwise (c_land)
@[cp] theorem c_and_prim : code_prim c_and := by unfold c_and; apply_cp
@[simp] theorem c_and_evp: evalp O c_and ⟪x,y⟫ = (x &&& y) := by simp [c_and]; rfl
end Computability.Code
end and
section xor
namespace Computability.Code
def c_xor := c_bitwise (c_lxor)
@[cp] theorem c_xor_prim : code_prim c_xor := by unfold c_xor; apply_cp
@[simp] theorem c_xor_evp: evalp O c_xor ⟪x,y⟫ = (x ^^^ y) := by simp [c_xor]; rfl
end Computability.Code
end xor

section fs_add
namespace Computability.Code
def c_fs_add := c_or.comp₂ left $ c_pow.comp₂ (c_const 2) right
@[cp] theorem c_fs_add_prim : code_prim c_fs_add := by unfold c_fs_add; apply_cp
@[simp] theorem c_fs_add_evp: evalp O c_fs_add ⟪x,y⟫ = (fs_add x y) := by
  simp [c_fs_add,evalp];
end Computability.Code
end fs_add

theorem evaln_dom_imp_x_le_s (h:(evaln O s c x).isSome) : x≤s := by
  contrapose h
  simp at h
  simp
  cases s with
  | zero => simp [evaln]
  | succ n => cases c <;> simp [evaln, not_le.mpr (Nat.lt_of_succ_lt h)];

-- compare to Simple.step
def c_step :=
  let s := left
  let i := left.comp right
  let prev := right.comp right

  let Aₚ := left.comp prev
  let Rₚ := right.comp prev
  let z21 := succ.comp $ c_mul.comp₂ (c_const 2) $ left.comp right
  c_ifz.comp₃ (c_sg'.comp $ c_fs_in.comp₂ Rₚ i)
  prev
  (
    let search := (c_bdd_search (right.comp right)).comp₂ ((pair s $ pair z21 i)) (s)
    let min := c_add.comp₂ z21 (left.comp $ c_pred.comp search)
    c_ifz.comp₃ search
    prev
    (pair (c_fs_add.comp₂ Aₚ min) (c_fs_add.comp₂ Rₚ i))
  )
@[cp] theorem c_step_prim : code_prim c_step := by
  unfold c_step
  lift_lets; extract_lets; expose_names
  have hs : code_prim s := by apply_cp
  have hi : code_prim i := by apply_cp
  have hprev : code_prim prev := by apply_cp
  have hAₚ : code_prim Aₚ := by apply_cp
  have hRₚ : code_prim Rₚ := by apply_cp
  have hz21 : code_prim z21 := by apply_cp
  have hsearch : code_prim search := by apply_cp
  have hmin : code_prim min := by apply_cp
  apply_cp 60
@[simp] theorem c_step_evp : evalp (χ ∅) c_step = λ x:ℕ ↦ Simple.step x.l x.r.l x.r.r := by
  funext x
  unfold Simple.step
  unfold c_step
  lift_lets; extract_lets; expose_names
  simp

  have hprev : (evalp (χ ∅) prev x) = x.r.r := by simp [prev]
  have hRp_1 : (evalp (χ ∅) Rₚ x) = Rₚ_1 := by simp [Rₚ, prev, Rₚ_1]
  have hAₚ_1 : (evalp (χ ∅) Aₚ x) = Aₚ_1 := by simp [Aₚ, prev, Aₚ_1]
  have hi : (evalp (χ ∅) i x) = x.r.l := by simp [i]
  have hs : (evalp (χ ∅) s x) = x.l := by simp [s]
  have hz21 : (evalp (χ ∅) z21 x) = 2*x.r.l+1 := by simp [z21]

  simp [hprev, hRp_1, hi, hAₚ_1]
  split; rotate_left
  next h0 =>
    simp [b2n] at h0
    simp [h0]
  next h0 =>
    simp [b2n] at h0
    simp [h0]
    clear h0
    split; rotate_left
    next h0 =>
      unfold search at h0
      simp [hs] at h0
      rcases c_bdd_aux h0 with ⟨z,r, hzr⟩
      simp [hi, hz21] at hzr
      rcases c_bdd_search_evp_1.mp hzr with ⟨hzr1, hzr2, hzr3⟩
      simp at hzr1 hzr2 hzr3
      have found_aux : (evalnSet ∅ x.l (n2c x.r.l) (2*x.r.l+1+z)).isSome = true ∧ (2*x.r.l+1+z) > 2 * x.r.l := by
        constructor
        simp [evalnSet]
        rw [hzr2]
        rfl
        omega
      have found : ∃ x_1, (evalnSet ∅ x.l (n2c x.r.l) x_1).isSome = true ∧ x_1 > 2 * x.r.l := by
        use 2*x.r.l+1+z
      simp [found]
      apply congrArg
      simp [min, search, hs,hi, hz21]
      simp [hnat_12 hzr]
      let (eq:=hnf) nf := Nat.find found
      have nf0 := @Nat.find_min _ _ found
      have nf1 := @Nat.find_spec _ _ found
      rw [←hnf] at nf0 nf1 ⊢

      have tri := lt_trichotomy (2 * x.r.l + 1 + z) nf
      cases tri with
      | inl h =>
        have := @nf0 (2 * x.r.l + 1 + z) h
        simp at this
        have := this found_aux.1
        omega
      | inr h =>
      cases h with
      | inl h => exact h
      | inr h =>
        have a2 : nf - 2*x.r.l-1 < z := by omega
        have a3 := hzr3 (nf - 2*x.r.l-1) a2
        have a4 : (2 * x.r.l + 1 + (nf - 2 * x.r.l - 1)) = nf := by omega
        simp [a4] at a3
        simp [evalnSet] at nf1
        simp [a3] at nf1
    next h0 =>
      simp [search, hz21, hi, hs] at h0
      have := c_bdd_search_evp_0.mp h0
      split; rotate_left
      next h1 => simp
      next h1 =>
        rcases h1 with ⟨h2,h3,h4⟩
        simp [evalnSet] at h3
        have a0 : h2 ≤ x.l := by exact evaln_dom_imp_x_le_s h3
        have a2 : h2-2*x.r.l-1 ≤ x.l := by omega
        have a1 := this (h2-2*x.r.l-1) a2
        simp at a1
        have a3 : (2 * x.r.l + 1 + (h2 - 2 * x.r.l - 1)) = h2 := by omega
        simp [a3] at a1
        simp [a1] at h3

@[simp] theorem c_step_evp' : evalp (χ ∅) c_step ⟪a,b,c⟫ = Simple.step a b c := by simp

def c_C :=
  (
    prec
    zero $
    let s := left.comp right
    let prev := right.comp right
    (c_list_foldr_param c_step).comp₃ s prev (c_list_reverse.comp $ c_list_range.comp s)
  ).comp₂ zero c_id

@[cp] theorem c_C_prim : code_prim c_C := by unfold c_C; apply_cp

@[simp] theorem c_C_evp : evalp (χ ∅) c_C = Simple.C := by
  funext x
  induction x with
  | zero =>
    unfold Simple.C
    simp [c_C]
    rfl
  | succ s ih =>
    unfold Simple.C
    rw [←ih]
    simp [c_C, -List.foldr_reverse]

def c_simple := dovetail $
  let x := left
  let s := right
  c_sg'.comp $ c_fs_in.comp₂ (left.comp $ c_C.comp s) x

theorem W_eq_iff_mem : W O c = A ↔ (∀ x, x∈A ↔ (evalSet O c x).Dom) := by
  simp [W]
  constructor
  intro h
  rw [←h]
  intro x
  simp only [PFun.mem_dom]
  exact Iff.symm Part.dom_iff_mem
  intro h
  refine Set.ext ?_
  exact fun x ↦ (fun {a b} ↦ iff_comm.mp) (h x)

theorem c_simple_ev : W ∅ c_simple = Simple.A := by
  apply W_eq_iff_mem.mpr
  simp [c_simple, Simple.A]
  intro x
  have : code_prim (c_sg'.comp (c_fs_in.comp₂ (left.comp (c_C.comp right)) left)) := by apply_cp
  simp [evalSet]
  constructor
  · intro h
    rcases h with ⟨s,hs⟩
    apply dovetail_ev_2.mpr
    use s
    simp [←evalp_eq_eval this]
    simp [hs, b2n]
  · intro h
    rcases dovetail_ev_2.mp h with ⟨s,hs⟩
    simp [←evalp_eq_eval this] at hs
    simp [b2n] at hs
    exact Exists.intro s hs


theorem exists_simple_set : ∃ A:Set ℕ, simpleIn ∅ A := by
  use Simple.A
  rw [←c_simple_ev]
  apply simpleInReq.mp
  constructor
  · rw [c_simple_ev]
    exact Simple.A_CoInfinite
  intro c inf
  have a0 := Simple.P c
  simp at a0
  have := a0 inf
  rw [c_simple_ev]
  exact Set.nonempty_iff_ne_empty.mp (a0 inf)
