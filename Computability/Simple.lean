import Computability.SetOracles

import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Set.Finite.Basic

open Computability
open Computability.Code


def PFun.nat_graph (f : ℕ→.ℕ) : Set ℕ := { xy | xy.unpair.2 ∈ f xy.unpair.1 }
def total_graph (f : ℕ → ℕ) : Set ℕ := { xy | xy.unpair.2 = f xy.unpair.1 }
theorem partfun_eq_χgraph {f:ℕ→ℕ} : f ≡ᵀᶠ χ (total_graph f) := by sorry



/-- `CEin O A` means that `A` is c.e. in `O`. -/
def CEin (O:Set ℕ) (A:Set ℕ) : Prop := ∃ c:Code, A = W O c
@[simp] abbrev CE (A:Set ℕ) := CEin ∅ A
@[simp] theorem CEin_trivial : CEin O (W O a) := exists_apply_eq_apply' (W O) a
theorem CEIn_deg (h:CEin O A) : A ≤ᵀ O⌜ := by
  rcases h with ⟨c,h⟩
  rw [h]
  exact W_le_Jump c
theorem CEin_range : CEin O A ↔ ∃ c, A = WR O c := by
  simp only [CEin]
  constructor
  · intro h
    rcases h with ⟨c,hc⟩
    use c_dom_to_ran c
    rw [←dom_to_ran_prop]
    exact hc
  · intro h
    rcases h with ⟨c,hc⟩
    use ran_to_dom (χ O) c
    rw [←ran_to_dom_prop]
    exact hc

theorem reducible_imp_W : A≤ᵀB → ∃ c, W B c = A := by
  simp [reducible_iff_code]
  intro c
  intro h
  use c_ite c c_diverge zero
  have hc : code_total (χ B) c := by simp_all [code_total]
  simp [W, evalSet, PFun.Dom, c_ite_ev hc]
  simp [h, eval]
  unfold χ
  aesop

theorem Cin_iff_Cin' : A≤ᵀB ↔ Aᶜ≤ᵀB := by
  have main (A B) : A≤ᵀB → Aᶜ≤ᵀB := by
    intro h
    simp [reducible_iff_code] at *
    rcases h with ⟨c,hc⟩
    use c_sg'.comp c
    simp [eval]
    simp [hc]
    funext x
    unfold χ
    simp
    aesop

  constructor
  exact fun a ↦ main A B a
  have := fun a ↦ main Aᶜ B a
  simp at this
  exact this

theorem asdoai (p:Part ℕ) (d:p.Dom) (h:p.get d=x) : p = Part.some x := by
  exact Part.get_eq_iff_eq_some.mp h

theorem Cin_iff_CEin_CEin' : A≤ᵀB ↔ (CEin B A ∧ CEin B Aᶜ) := by
  constructor
  -- first, the trivial direction.
  · intro h
    simp [CEin]
    have h1 := reducible_imp_W h
    have h2 := reducible_imp_W $ Cin_iff_Cin'.mp h
    rcases h1 with ⟨c1, hc1⟩
    rcases h2 with ⟨c2, hc2⟩
    exact ⟨⟨c1, hc1.symm⟩,⟨c2, hc2.symm⟩⟩

  intro ⟨h1,h2⟩
  apply reducible_iff_code.mpr
  rcases h1 with ⟨c1,hc1⟩
  rcases h2 with ⟨c2,hc2⟩

  let d := (
    c_ite right
    (zero.comp $ c2.comp left) $
    c_if_eq_te' right (c_const 1)
    (zero.comp $ c1.comp left)
    c_diverge
  )
  /-
  d is a program that does the following.
  d(x,y):
    if y=0:
      run [c2](x)
      return 0
    elif y=1:
      run [c1](x)
      return 0
    else:
      diverge

  Note that dovetailing d, will return 0 if x∉A and 1 if x∈A.
  -/
  use dovetail d
  funext x

  -- a1,a2: to be supplied as arguments for c_if_eq_te'_ev
  have a1 : code_total (χ B) (right) := by exact fun x ↦ trivial
  have a2 : code_total (χ B) (c_const 1) := by simp [code_total]

  by_cases hx:x∈A
  ·
    have dvtthm := @dovetail_ev_0 (χ B) d x ?_
    extract_lets at dvtthm; expose_names
    all_goals
      have tc1 : (eval (χ B) c1 x).Dom := by
        simp [W, evalSet, PFun.Dom] at hc1
        simp [hc1] at hx
        exact hx
      have tc2 : (eval (χ B) c2 x) = Part.none := by
        have : ¬x∈Aᶜ := fun a ↦ a hx
        simp [W, evalSet, PFun.Dom] at hc2
        simp [hc2] at this
        exact Part.eq_none_iff'.mpr this
    rotate_left
    · apply dovetail_ev_2.mpr
      simp [d, c_if_eq_te'_ev a1 a2, eval, Part.Dom.bind $ tc1]
      exact ⟨1,rfl⟩
    ·
      simp [χ, hx]
      simp [d, c_if_eq_te'_ev a1 a2, eval, Part.Dom.bind $ tc1, tc2] at dvtthm

      have : dvt = 1 := by
        contrapose dvtthm
        simp [dvtthm]
      simp [dvt] at this
      exact Part.get_eq_iff_eq_some.mp this

  · -- essentialy the same as the x∈A case.
    have hx' : x∈Aᶜ := hx
    have dvtthm := @dovetail_ev_0 (χ B) d x ?_
    extract_lets at dvtthm; expose_names
    all_goals
      have tc1 : (eval (χ B) c2 x).Dom := by
        simp [W, evalSet, PFun.Dom] at hc2
        simp [hc2] at hx'
        exact hx'
      have tc2 : (eval (χ B) c1 x) = Part.none := by
        simp [W, evalSet, PFun.Dom] at hc1
        simp [hc1] at hx
        exact Part.eq_none_iff'.mpr hx
    rotate_left
    · apply dovetail_ev_2.mpr
      simp [d, c_if_eq_te'_ev a1 a2, eval, Part.Dom.bind $ tc1]
      exact ⟨0,fun a ↦ False.elim (a rfl)⟩
    ·
      simp [χ, hx]
      simp [d, c_if_eq_te'_ev a1 a2, eval, Part.Dom.bind $ tc1, tc2] at dvtthm

      have : dvt = 0 := by
        contrapose dvtthm
        simp [dvtthm]
      simp [dvt] at this
      exact Part.get_eq_iff_eq_some.mp this




/-- immuneIn O A := A is immune in O -/
def immuneIn (O:Set ℕ) (A:Set ℕ) : Prop := (A.Infinite) ∧ (∀c, (W O c).Infinite → ¬(W O c ⊆ A))
theorem immuneIn_not_CEIn : immuneIn O A → ¬ CEin O A := by
  intro h
  unfold CEin
  unfold immuneIn at h
  aesop
theorem immuneIn_not_CEIn_contrapositive :  CEin O A → ¬ immuneIn O A  := by
  contrapose
  simp
  exact fun a ↦ immuneIn_not_CEIn a
/-- simpleIn O A := A is simple in O -/
def simpleIn (O:Set ℕ) (A:Set ℕ) : Prop := (CEin O A) ∧ immuneIn O Aᶜ
abbrev simple := simpleIn ∅
theorem simpleIn_not_reducible (h:simpleIn O A): A ≰ᵀ O := by
  contrapose h
  simp at h
  unfold simpleIn
  simp
  intro _
  rcases Cin_iff_CEin_CEin'.mp h with ⟨h1,h2⟩
  exact immuneIn_not_CEIn_contrapositive h2

theorem simple_above_empty (h:simple A): ∅<ᵀA := ⟨empty_le A, simpleIn_not_reducible h⟩
theorem simpleInReq_aux {α} (A B : Set α) : A ∩ B ≠ ∅ ↔ ¬ A ⊆ Bᶜ := by
  constructor
  · intro h1
    have : ∃ a:α, a ∈ A ∧ a ∈ B := by
      contrapose h1
      simp_all
      ext x : 1
      simp_all
    contrapose this
    simp at this ⊢
    exact fun x a ↦ this a
  · intro h1
    have : ∃ a:α, a ∈ A ∧ a ∈ B := by
      contrapose h1
      simp_all
      exact h1
    exact Set.nonempty_iff_ne_empty.mp this
theorem simpleInReq : ((W O a)ᶜ.Infinite ∧ ∀ c, (W O c).Infinite → (W O c ∩ W O a ≠ ∅)) ↔ simpleIn O (W O a) := by
  constructor
  · intro ⟨h1,h2⟩
    unfold simpleIn
    constructor
    simp
    unfold immuneIn
    constructor
    exact h1
    intro c h3
    have := h2 c h3
    exact (simpleInReq_aux (W O c) (W O a)).mp (h2 c h3)
  intro h
  unfold simpleIn at h
  rcases h with ⟨h1,h2⟩
  unfold immuneIn at h2
  rcases h2 with ⟨h3,h4⟩
  constructor
  exact h3
  intro c h5
  have := h4 c h5
  exact (simpleInReq_aux (W O c) (W O a)).mpr (h4 c h5)


-- def c_bdd_total_search (c:Code) := zero
-- theorem c_bdd_total_search_evp : evalp O (c_bdd_total_search c) x = 0 ↔ ∀ y≤x, evalp O c y = 0 := by
--   sorry

#check Nat.bit
#check 0b00010
#eval Nat.testBit 0b00010 0
#eval Nat.bitIndices 0b100010
#eval 2^1
abbrev fs_in := Nat.testBit
abbrev fs_add : ℕ→ℕ→ℕ := λ a x ↦ a ||| (2^x)
#check Nat.pair

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

#check Nat.find
namespace Computability.Simple
-- def cond (s i : ℕ) : Prop := ∃ x ∈ Wn O i s, x > 2*i
#check Nat.iterate
-- /--
-- C stands for construction.
-- Input: stage `s`
-- Output: (natural representing the simple set A built so far, natural representing set of requirements satisfied so far)
-- -/
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
open Classical in
noncomputable def C : ℕ → ℕ := λ s ↦
match s with
| 0 => ⟪0, 0⟫
| s+1 =>
  let A := (C s).l
  let R := (C s).r

  -- let AR := {(x,i) : ℕ×ℕ |
  --   i ≤ s ∧
  --   ¬ fs_in R i ∧
  --   (if found : ∃ x ∈ Wn ∅ i (s+1), x > 2*i then x = Nat.find found else true)
  -- }
  -- 0

  List.foldr (step s) ⟪A,R⟫ (List.reverse $ List.range (s+1))

  -- if found : ∃ i ≤ s+1, ∃ x ∈ Wn ∅ i s, x > 2*i then
  --   let i := Nat.find found
  --   let hi := Nat.find_spec found
  --   let x := Nat.find hi.right
  --   ⟪fs_add Aₚ x, fs_add Rₚ i⟫
  -- else
  -- let search : Option ℕ := (eval Nat.fzero (c_bdd_search C_aux) ⟪⟪s,Rₚ⟫, s⟫).get (c_bdd_search_evp_total C_aux_total ⟪⟪s,Rₚ⟫, s⟫)
  -- if halts:search.isSome then
  --   let ⟨x,j⟩ := (search.get halts).unpair
  --   let Aₛ := fs_add Aₚ x
  --   let Rₛ := fs_add Rₚ j
  --   ⟪Aₛ, Rₛ⟫
  -- else
      -- ⟪Aₚ, Rₚ⟫
  -- 0
/-
  for each i ≤ s:
    1. check i is not already satisfied.
    2. now, check if there is a x ∈ W_i,s s.t. x>2i.
    3. if so:
      A = A ++ x
      R = R ++ i
  return Nat.pair A R
-/


theorem step_preserves_R_mem {j s i prev} (h:fs_in prev.r j) : fs_in (step s i prev).r j := by
  simp [step]; aesop
theorem step_preserves_A_mem {j s i prev} (h:fs_in prev.l j) : fs_in (step s i prev).l j := by
  simp [step]; aesop
theorem step_preserves_R_not_mem {j k s prev} (h:¬fs_in prev.r j) (hk:k<j) :
¬ fs_in (step s k prev).r j := by
  simp [step]
  -- aesop? says
  simp_all only [Bool.not_eq_true, gt_iff_lt]
  split
  next h_1 =>
    split
    next h_2 =>
      simp_all only [pair_r, Nat.testBit_or, Bool.false_or]
      simp_all only [gt_iff_lt]
      obtain ⟨w, h_2⟩ := h_2
      obtain ⟨left, right⟩ := h_2
      have : k≠j := by exact Nat.ne_of_lt hk
      exact Nat.testBit_two_pow_of_ne this
    next h_2 => simp_all only [gt_iff_lt, not_exists, not_and, not_lt]
  next h_1 => simp_all only [Bool.not_eq_false]

theorem split_upper (h:fs_in R j) : fs_in (List.foldr (step s) ⟪A,R⟫ l).r j := by
  induction l with
  | nil => simpa
  | cons head tail ih => exact step_preserves_R_mem ih

theorem split_lower (h:¬fs_in R j) (hk : k ≤ j):
¬ fs_in (List.foldr (step s) ⟪A,R⟫ (List.reverse $ List.range k)).r j := by
  induction k with
  | zero => simp at *; assumption
  | succ k ih =>
    simp [listrwgen, -List.foldr_reverse]
    have kk : k≤ j := by exact Nat.le_of_succ_le hk
    have kk2 : k< j := by exact hk
    have ih1 := ih kk; clear ih

    have := @step_preserves_R_not_mem j k s _ ih1 kk2
    simp at this
    simp
    exact this

theorem split_middle (h:¬fs_in R j) (h2: ∃ x ∈ Wn ∅ j s, x > 2*j) :
fs_in ((step s) j ⟪A,R⟫).r j := by
  simp at h2
  simp [step, h, h2]

theorem R_foldr (h:¬fs_in R j) (h2: ∃ x ∈ Wn ∅ j s, x > 2*j) (hs:j<s):
fs_in (List.foldr (step s) ⟪A,R⟫ (List.reverse $ List.range (s+1))).r j := by
  have : (List.reverse $ List.range (s+1)) = (List.range' (j+1) (s-j)).reverse ++ [j] ++ (List.range' 0 j).reverse := by
    simp
    have : j :: List.range' (j + 1) (s - j) = List.range' (0+j) (s - j +1) := by aesop
    rw [this]
    have : List.range (s + 1) = List.range' 0 (s + 1) := by exact List.range_eq_range'
    rw [this]
    have := @List.range'_append_1 0 j (s-j+1)
    rw [this]
    congr 1
    grind
  rw [this]
  simp [-List.foldr_reverse]

  rw [show List.range' 0 j = List.range j from by exact Eq.symm List.range_eq_range'] at *
  let fold_lower := (List.foldr (step s) ⟪A,R⟫ (List.range j).reverse)

  have a0 := @split_lower R j j s A h (Nat.le_refl j)
  rw [show  (List.foldr (step s) ⟪A,R⟫ (List.range j).reverse) = fold_lower from rfl] at ⊢ a0
  have a1 := @split_middle _ j s (fold_lower.l) a0 h2
  simp at a1

  have a2 := @split_upper _ _  s ((step s j fold_lower).l) ((List.range' (j + 1) (s - j)).reverse) a1

  simp at a2
  simp
  exact a2


def A : Set ℕ := {x | ∃ s, fs_in (C s).l x}

-- theorem RP : fs_in (C s).r x ↔

theorem inf_imp_mem {A:Set ℕ} (h:A.Infinite) : ∃ y, y ∈ A := by
  simpa using h.nonempty

theorem P (i:ℕ) : (W ∅ i).Infinite → (∃ s, fs_in (C s).r i ∧ ∃ y ∈ W ∅ i, fs_in (C s).l y) := by
  intro h
  -- induction' i using Nat.strong_induction_on with i ih

  -- sorry
-- theorem P {∅} (i:ℕ) : (W ∅ i).Infinite → (W ∅ i ∩ A ≠ ∅) := by
--   intro h
  /-
  the argument goes like this.
  suppose W_i is infinite.
  by infinitue of W_i, we can find some x>2i in it eventually.
  say x is in W_i by stage s.
  sp fs_in fails by stage s/s-1,
  then it will succeed in s+1/s
  -/
  -- sorry
--   -- i dont think doing induction on i like this works. we need to know that all things below i are exhausted in R
--   induction' i using Nat.strong_induction_on with i ih

  have : ∃ x ∈ W ∅ i, x > 2*i := by
    have : ((W ∅ i) \ {x | x ≤ 2*i}).Infinite := by
      have : {x | x ≤ 2*i}.Finite := by exact Set.finite_le_nat (2 * i)
      exact Set.Infinite.diff h this
    rcases inf_imp_mem this with ⟨y,hy1,hy2⟩
    exact ⟨y, hy1, Nat.gt_of_not_le hy2⟩

  rcases this with ⟨x, hx0, hx1⟩
  rcases Wn_complete.mp hx0 with ⟨s,hs⟩
  have si1 : s ≤ s+i+1 := by omega
  have si2 : i < s+i+1 := by omega
  have ex0 :  ∃ x ∈ Wn ∅ (n2c i) (s+i+1), x > 2 * i := by
    exact ⟨x,Wn_mono (si1) hs, hx1⟩
  use s+i+1+1
  unfold C
  constructor
  -- cases fs in prev R
  lift_lets; extract_lets; expose_names
  by_cases h1:fs_in R i
  ·
    exact split_upper h1
  ·
    have := @R_foldr _ _ _ A h1 ex0 si2
    exact this



--   have main : ∃ y, fs_in (C (s+i)).l y ∧ y ∈ W O i := by
--     sorry

--   suffices ∃ y ∈ W O i, ∃ s, fs_in (C s).l y from by exact Set.nonempty_iff_ne_empty.mp this
--   -- unfold A
--   -- unfold C

--   -- unfold A

--   -- have : ¬ fs_in R i := by sorry
  sorry
theorem N (i:ℕ) : (W O i).Infinite → (W O i ∩ W O a ≠ ∅) := by
  sorry

end Computability.Simple

theorem exists_simple_set : ∃ A:Set ℕ, simpleIn O A := by
  sorry



-- in cooper p.220 theres the requirement also that A≤ᵀjumpn 1 ∅. is this necessary?
def lowNIn (n:ℕ) (A O:Set ℕ) : Prop := jumpn n A = jumpn n O
def lowN (n:ℕ) (A:Set ℕ) : Prop := lowNIn n A ∅
abbrev low := lowN 1
abbrev lowIn := lowNIn 1

theorem low_below_K (h:lowN 1 A) : A<ᵀ∅⌜ := by
  simp [lowN, lowNIn, jumpn] at h
  have h0 : A⌜≡ᵀ∅⌜ := by exact Eq.antisymmRel (congrArg (toAntisymmetrization SetTuringReducible) h)
  have h1 : A<ᵀA⌜ := by exact Set_lt_SetJump A
  exact lt_of_lt_of_eq h1 (congrArg (toAntisymmetrization SetTuringReducible) h)

theorem exists_low_simple_set (O : Set ℕ) : ∃ A:Set ℕ, simpleIn O A ∧ lowIn O A := by
  sorry

theorem posts_problem_solution (O : Set ℕ) : ∃ A:Set ℕ, CEin O A ∧ O<ᵀA ∧ A<ᵀO⌜ := by
  rcases (exists_low_simple_set O) with ⟨A,h0,h1⟩
  use A
  constructor
  · sorry
  constructor
  · exact simpleIn_above_oracle h0
  · exact low_below_K h1
