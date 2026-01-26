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


/-
`c_bdd_search c` is a primrec code that, on input `⟪(s, a, i), l⟫`, evaluates:
  let e := [c](⟪(s, a, i), l⟫)
  `[e]ₛ(a+0)`
  `[e]ₛ(a+1)`
  ... up to
  `[e]ₛ(a+l)`,
  until one of the computations halt. Suppose `[e]ₛ(a+i)` is the first such computation.

  Then, `some ⟪i, [e](a+i)⟫` is returned.

  If no such value is found, `none` is returned.

  The code `c` must be total.
-/
def c_bdd_search (c:Code) := prec
  (
    let compt := c_evaln.comp₃ (left.comp right) (c) (left)
    c_ifz.comp₃ compt zero $
    succ.comp $ pair zero $ c_pred.comp compt
    -- pair zero $ c_evaln.comp₃ (pair left (c_const 0)) (c_const c) right
  ) -- abusing the fact that ⟪0,0⟫ = 0 = Option.none
  (
    let prev_comp := right.comp right
    let iP1 := succ.comp $ left.comp right
    -- let x := left.comp left
    let s := left.comp left
    let a := left.comp $ right.comp left
    let k := right.comp $ right.comp left
    let aPi := c_add.comp₂ a $ iP1
    let computation := c_evaln.comp₃ (aPi) (c.comp₃ s a k) s

    c_ifz.comp₃ prev_comp
    (c_ifz.comp₃ computation zero (succ.comp $ pair iP1 $ c_pred.comp computation))
    prev_comp
    -- pair zero $ c_eval.comp₂ c (pair c_id iP1)
  )
theorem c_bdd_search_evp_total (h:code_total O c) : code_total O (c_bdd_search c) := by
  sorry
theorem o2n_a0 : o2n x = 0 ↔ x = Option.none := by
  constructor
  · intro h
    contrapose h
    exact hnat_1 h
  · intro h
    simp [h]
theorem b2n_a0 : b2n x = 0 ↔ x = false := by simp [b2n]

theorem c_bdd_search_evp_0 :
  (evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, l⟫) = 0
  ↔
  ∀ i ≤ l, (evaln O s (evalp O c ⟪s,a,k⟫) (a+i)) = Option.none := by
  induction l with
  | zero =>
    simp [c_bdd_search]
    simp [ ← o2n_a0]
  | succ n ih =>
    unfold c_bdd_search
    lift_lets; extract_lets; expose_names
    -- simp only [evalp, Nat.unpaired, Nat.unpair_pair, -comp₃_evp, c_ifz_evp, pair_l, pair_r]
    simp [evalp]
    let (eq:=hinp) inp := ⟪⟪s,⟪a,k⟫⟫,⟪n,Nat.rec (if evalp O compt ⟪s,⟪a,k⟫⟫ = 0 then 0 else ⟪0,evalp O compt ⟪s,⟪a,k⟫⟫ - 1⟫ + 1)
                  (fun y IH ↦
                    if evalp O prev_comp ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫ = 0 then
                      if evalp O computation ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫ = 0 then 0
                      else ⟪evalp O iP1 ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫,evalp O computation ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫ - 1⟫ + 1
                    else evalp O prev_comp ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫)
                  n⟫⟫
    rw [←hinp]
    have hprev_comp : evalp O prev_comp inp = evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫ := by
      unfold c_bdd_search
      lift_lets;
      simp [prev_comp, inp]

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
          -- have := congrArg Nat.r h
          -- simp [Nat.r] at this
          -- simp [h3] at this
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
theorem hnat_10 (h : o2n x ≠ 0) : x.isSome := by
  have := hnat_6 h
  simp at this
  exact this
theorem hnat_11 {x:Option ℕ} (h : x.isSome) : x = some (o2n x - 1) := by
  rw [hnat_2 h]
  simp
theorem hnat_12 {x : ℕ} (h : n2o x = some a) : x-1 = a := by
  have : (n2o x).isSome := by exact Option.isSome_of_mem h
  have := hnat_11 this
  rw [this] at h
  simp at h
  assumption
theorem c_bdd_aux (h:x≠0) : ∃ y z, ⟪y, z⟫ ∈ n2o x := by
  use (x-1).l
  use (x-1).r
  simp
  exact hnat_to_opt_2 h
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
      simp_all only [add_zero, not_lt_zero', IsEmpty.forall_iff, implies_true, Encodable.encode_some,
        Encodable.encode_nat, Nat.succ_eq_add_one, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
        add_tsub_cancel_right, hnat_to_opt_0']
  | succ n ih =>
    unfold c_bdd_search
    lift_lets; extract_lets; expose_names
    -- simp only [evalp, Nat.unpaired, Nat.unpair_pair, -comp₃_evp, c_ifz_evp, pair_l, pair_r]
    simp [evalp]
    let (eq:=hinp) inp := ⟪⟪s,⟪a,k⟫⟫,⟪n,Nat.rec (if evalp O compt ⟪s,⟪a,k⟫⟫ = 0 then 0 else ⟪0,evalp O compt ⟪s,⟪a,k⟫⟫ - 1⟫ + 1)
                    (fun y IH ↦
                      if evalp O prev_comp ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫ = 0 then
                        if evalp O computation ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫ = 0 then 0
                        else ⟪evalp O iP1 ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫,evalp O computation ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫ - 1⟫ + 1
                      else evalp O prev_comp ⟪⟪s,⟪a,k⟫⟫,⟪y,IH⟫⟫)
                    n⟫⟫ 
    rw [←hinp]
    have hprev_comp : evalp O prev_comp inp = evalp O (c_bdd_search c) ⟪⟪s,a,k⟫, n⟫ := by
      unfold c_bdd_search
      lift_lets;
      simp [prev_comp, inp]

    have hs_1 : evalp O s_1 inp = s := by simp [s_1, inp]
    have ha_1 : evalp O a_1 inp = a := by simp [a_1, inp]
    have hk_1 : evalp O k_1 inp = k := by simp [k_1, inp]
    have hiP1 : evalp O iP1 inp = n+1 := by simp [iP1, inp]
    have haPi : evalp O aPi inp = a+(n+1) := by simp [aPi, ha_1, hiP1]
    simp [hprev_comp]
    have hcomputation : evalp O computation inp = o2n (evaln O s (evalp O c ⟪s,a,k⟫) (a+(n+1))) := by
      simp [computation, hs_1, haPi, ha_1, hk_1]
    simp [hcomputation, hiP1]
    split
    next h =>
      split
      next h2 =>
        simp
        intro hi h3
        have := c_bdd_search_evp_0.mp h
        cases Nat.eq_or_lt_of_le hi with
        | inl h4 =>
          simp [←h4] at h2
          simp [h3] at h2
        | inr h4 =>
          have := this i (Nat.le_of_lt_succ h4)
          simp [this] at h3

      next h2 =>
        simp
        constructor
        rintro ⟨h3,h4⟩
        rw [h3] at h2 h4 ⊢
        constructor
        · exact le_refl i
        constructor
        · have := hnat_10 h2
          simp [hnat_2 this] at h4
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
      intro h2
      rcases ih.mp h2 with ⟨h3,h4, h5⟩
      constructor
      exact Nat.le_succ_of_le h3
      constructor
      exact h4
      exact h5

      simp
      intro hi h2 h3
      apply ih.mpr
      simp
      constructor
      ·
        cases Nat.eq_or_lt_of_le hi with
        | inl h5 =>
          -- rw [h5] at ih
          -- simp at ih


          simp [h5]
          clear hi
          have a0 := c_bdd_aux h
          rcases a0 with ⟨y,z,hyz⟩
          rcases ih.mp hyz with ⟨h6,h7,h8⟩

          have := h3 y (by omega)
          simp [this] at h7



        | inr h => exact Nat.le_of_lt_succ h

      exact ⟨h2,h3⟩





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
  apply_rules (config := {maxDepth:=50, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp
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

theorem evaln_dom_imp_x_le_s (h:(evaln O s c x).isSome) : x≤s := by
  contrapose h
  simp at h
  simp
  cases s with
  | zero => simp [evaln]
  | succ n =>
    cases c <;> simp [evaln, not_le.mpr (Nat.lt_of_succ_lt h)];


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
  -- i inside search expr:
  -- let ii := c_comp.comp₂ (left.comp $ right.comp $ left) c_right

  let Aₚ := left.comp prev
  let Rₚ := right.comp prev
  let z21 := succ.comp $ c_mul.comp₂ (c_const 2) $ left.comp right
  c_ifz.comp₃ (c_sg'.comp $ c_fs_in.comp₂ Rₚ i)
  prev
  (
    -- search from [i]ₛ(0) to [i]ₛ(s)
    let search := (c_bdd_search (right.comp right)).comp₂ ((pair s $ pair (z21) i)) (s)
    let min := c_add.comp₂ z21 (left.comp $ c_pred.comp search)
    c_ifz.comp₃ (search)
    prev
    (pair (c_fs_add.comp₂ Aₚ min) (c_fs_add.comp₂ Rₚ i))
  )
@[simp] theorem c_step_evp : evalp (χ ∅) c_step = λ x:ℕ ↦ Simple.step x.l x.r.l x.r.r := by
  funext x
  unfold Simple.step
  unfold c_step
  lift_lets; extract_lets; expose_names
  simp
  -- simp [Rₚ, prev]

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
    -- have : fs_in Rₚ_1 x.r.l = false := by
    -- simp [this]
    split; rotate_left
    next h0 =>
      unfold search at h0
      simp [hs] at h0
      rcases c_bdd_aux h0 with ⟨z,r, hzr⟩
      simp [hi, hz21] at hzr
      have temp := c_bdd_search_evp_1.mp hzr
      -- simp [i] at temp
      rcases temp with ⟨hzr1, hzr2, hzr3⟩
      simp [hi] at hzr1 hzr2 hzr3
      -- simp [evaln] at hzr2
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
      have a0 := @Nat.find_min _ _ found
      have a1 := @Nat.find_spec _ _ found
      rw [←hnf] at a0 a1 ⊢

      have tri := lt_trichotomy (2 * x.r.l + 1 + z) nf
      cases tri with
      | inl h =>
        have := @a0 (2 * x.r.l + 1 + z) h
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
        simp [evalnSet] at a1
        simp [a3] at a1
      
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
