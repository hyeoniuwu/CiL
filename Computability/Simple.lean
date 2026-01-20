import Computability.SetOracles

import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Defs

open Computability
open Computability.Code
open List

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

/-
Proof sketch:

Let A≤ᵀB via `c`.

Then, the function:
λ x ↦ 0 if (c B x)↓ else ↑ has domain A.
-/
theorem reducible_imp_W : A≤ᵀB → ∃ c, W B c = A := by
  intro h
  rcases reducible_iff_code.mp h with ⟨c,h⟩
  use c_ite c c_diverge zero
  have c_total : code_total (χ B) c := by simp_all [code_total]
  simp [W, evalSet, PFun.Dom, c_ite_ev c_total, h, eval]
  unfold χ
  aesop

theorem Cin_iff_Cin' : A≤ᵀB ↔ Aᶜ≤ᵀB := by
  /-
  proof sketch; if A≤ᵀB via c, then Aᶜ≤ᵀB via Nat.sg' c.
  -/
  have main (A B) : A≤ᵀB → Aᶜ≤ᵀB := by
    intro h
    simp only [reducible_iff_code] at *
    rcases h with ⟨c,hc⟩
    use c_sg'.comp c
    funext x
    simp [eval, hc]; unfold χ
    aesop

  constructor
  exact fun a ↦ main A B a
  have := fun a ↦ main Aᶜ B a
  simp only [compl_compl] at this
  exact this

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

  /-
  We wish to show that if both A and its complement is computably enumerable from B,
  then A is reducible to B.

  Proof sketch:

  Let CEin B A and CEin B Aᶜ via codes `c1` and `c2` respectively.

  We will construct χ A by constructing the following function `d`:

  d(x,y):
    if y=0:
      run [c2](x)
      return 0
    elif y=1:
      run [c1](x)
      return 0
    else:
      diverge

  Then, the behaviour of `dovetail d` on input `x` will be as follows:

  · if `x∈A`, then `d(x,y)` only halts if `y=1`, and diverges for all other `y`. Thus, `dovetail d` will return `1`.
  · if `x∉A`, then `d(x,y)` only halts if `y=0`, and diverges for all other `y`. Thus, `dovetail d` will return `0`.

  Note that dovetailing d will return 0 if x∉A and 1 if x∈A.
  -/

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
  use dovetail d
  funext x

  -- aux0, aux1: trivial helpers needed as arguments later for c_if_eq_te'_ev
  have aux0 : code_total (χ B) (right) := by exact fun x ↦ trivial
  have aux1 : code_total (χ B) (c_const 1) := by simp [code_total]

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
      simp [d, c_if_eq_te'_ev aux0 aux1, eval, Part.Dom.bind $ tc1]
      exact ⟨1, rfl⟩
    · simp [χ, hx]
      simp [d, c_if_eq_te'_ev aux0 aux1, eval, Part.Dom.bind $ tc1, tc2] at dvtthm
      have : dvt = 1 := by contrapose dvtthm; simp [dvtthm]
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
      simp [d, c_if_eq_te'_ev aux0 aux1, eval, Part.Dom.bind $ tc1]
      exact ⟨0, λ a ↦ False.elim (a rfl)⟩
    · simp [χ, hx]
      simp [d, c_if_eq_te'_ev aux0 aux1, eval, Part.Dom.bind $ tc1, tc2] at dvtthm
      have : dvt = 0 := by contrapose dvtthm; simp [dvtthm]
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
  simp only [not_not]
  exact fun a ↦ immuneIn_not_CEIn a

/-- simpleIn O A := A is simple in O -/
def simpleIn (O:Set ℕ) (A:Set ℕ) : Prop := (CEin O A) ∧ immuneIn O Aᶜ
abbrev simple := simpleIn ∅
theorem simpleIn_not_reducible (h:simpleIn O A): A ≰ᵀ O := by
  contrapose h
  simp only [NotSetTuringDegreeNLE_SetTuringDegreeLE] at h
  unfold simpleIn
  simp only [not_and]
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
/-
Alternative characterisation of simplicity of a set; a set is simple iff if it is co-infinite, computable enumerable, and is such that its
complements admits no infinite computable enumerable subset.
-/
theorem simpleInReq : ((W O a)ᶜ.Infinite ∧ ∀ c, (W O c).Infinite → (W O c ∩ W O a ≠ ∅)) ↔ simpleIn O (W O a) := by
  constructor
  · intro ⟨h1,h2⟩
    exact ⟨CEin_trivial, h1, λ c h3 ↦ (simpleInReq_aux (W O c) (W O a)).mp (h2 c h3)⟩
  rintro ⟨_, h3, h4⟩;
  exact ⟨h3, λ c h5 ↦ (simpleInReq_aux (W O c) (W O a)).mpr (h4 c h5)⟩

section fs
/-
We define functions to treat naturals as finite sets.
-/
abbrev fs_in := Nat.testBit
/-
Examples:
fs_in 0b0010 0 = false
fs_in 0b0010 1 = true
fs_in 0b0010 2 = false
fs_in 0b0010 3 = false
-/

/-- `fs_add a x` gives the natural representing the set with `x` added to `a` interpreted as a finite set. -/
abbrev fs_add : ℕ→ℕ→ℕ := λ a x ↦ a ||| (2^x)

/-- `fs_add a` gives the the size of `a` interepreted as a finite set. -/
def fs_size := List.length.comp Nat.bitIndices
/-
Examples:
fs_size 0b010 = 1
fs_size 0b111 = 3
fs_size 0b011000111 = 5
-/

theorem fs_in_singleton {x y}: fs_in (2^y) x ↔ x=y := by grind
theorem fs_in_singleton': Nat.testBit (2^y) x = false ↔ y≠x := by grind
end fs

section Computability.Simple
open Classical
/-
We specify the construction procedure for a simple set here.

We roughly follow the procedure outlined in Computability Theory [Cooper] (2004), page 91.

In each step of the construction, we keep track of:

`A`: the simple set being built
`R`: the list of (positive) requirements that have been satisfied so far.

At stage `s` of the construction, we do the following:
  for each i < s:
    1. check i is not already satisfied.
    2. now, check if there is a x ∈ W_i,s s.t. x>2i.
      if so, then set:
        A = A ++ x
        R = R ++ i
      otherwise, move on.

  We also note here that step 2 can be done computably, as W_i is finite (elements are bounded by i.)
-/

noncomputable def step (s:ℕ) := λ i prev ↦
  let Aₚ := prev.l
  let Rₚ := prev.r
  if ¬ fs_in Rₚ i then
    if found : ∃ x ∈ Wn ∅ i s, x > 2*i then
      let x := Nat.find found
      ⟪fs_add Aₚ x, fs_add Rₚ i⟫
    else prev
  else prev

/--
C stands for construction.
Input: stage `s`
Output: (natural representing the simple set A built so far, natural representing set of requirements satisfied so far)
-/
noncomputable def C : ℕ → ℕ := λ s ↦
match s with
| 0 => ⟪0, 0⟫
| s+1 => foldr (step s) (C s) (range s).reverse

/-- The simple set built by our construction procedure. -/
def A : Set ℕ := {x | ∃ s, fs_in (C s).l x}

theorem step_preserves_A_mem {j s i X} (h:fs_in X.l j) : fs_in (step s i X).l j := by
  simp [step]; aesop
theorem step_preserves_R_mem {j s i X} (h:fs_in X.r j) : fs_in (step s i X).r j := by
  simp [step]; aesop
theorem step_preserves_R_not_mem {j k s X} (h:¬fs_in X.r j) (hk:k<j) : ¬ fs_in (step s k X).r j := by
  simp [step]
  -- aesop? says
  simp_all only [Bool.not_eq_true]
  split
  next h_1 =>
    split
    next h_2 =>
      simp_all only [pair_r, Nat.testBit_or, Bool.false_or]
      exact Nat.testBit_two_pow_of_ne (Nat.ne_of_lt hk)
    next h_2 => exact h
  next h_1 => exact h
theorem fold_preserves_R_mem {j s X l} (h:fs_in X.r j) : fs_in (foldr (step s) X l).r j := by
  induction l with
  | nil => simpa
  | cons head tail ih => exact step_preserves_R_mem ih
theorem fold_preserves_R_mem2 {s ywit} (h:fs_in (C s).r ywit) : ∀ i, fs_in (C (s+i)).r ywit := by
  intro i
  induction i with
  | zero => simpa
  | succ i ih =>
    simp [C, -foldr_reverse]
    have := @fold_preserves_R_mem _ (s+i) (C (s + i)) (range (s + i)).reverse ih
    simpa using this
theorem fold_preserves_R_mem3 {s ywit} (h:fs_in (C s).r ywit) : ∀ s2≥s, fs_in (C (s2)).r ywit := by
  intro s2 hs2
  have a0 : s2 = s+(s2-s) := by grind
  have := fold_preserves_R_mem2 h (s2-s)
  rw [← a0] at this
  exact this
theorem fold_preserves_A_mem {j s X l} (h:fs_in X.l j) : fs_in (foldr (step s) X l).l j := by
  induction l with
  | nil => simpa
  | cons head tail ih => exact step_preserves_A_mem ih

/-
if `j∉X.r`, then applying `step i` to `X` for `i≤j` will not change the non-membership
-/
theorem split_lower {j k s X} (h : ¬ fs_in X.r j) (hk : k ≤ j):
¬ fs_in (foldr (step s) X (range k).reverse).r j := by
  induction k with
  | zero => simp at *; assumption
  | succ k ih =>
    simp [listrwgen, -foldr_reverse]
    have kk : k ≤ j := Nat.le_of_succ_le hk
    have kk2 : k< j := hk
    have := @step_preserves_R_not_mem _ k s _ (ih kk) kk2
    simpa using this
theorem split_middle (h:¬fs_in X.r j) (h2: ∃ x ∈ Wn ∅ j s, x > 2*j) :
fs_in ((step s) j X).r j := by
  simp at h2; simp [step, h, h2]
theorem range_3_way_split {s j} (hs:j+1≤ s) : (range s).reverse = (range' (j+1) (s-1-j)).reverse ++ [j] ++ (range j).reverse := by
  simp only [append_assoc, cons_append, nil_append, reverse_eq_append_iff, reverse_cons,
    reverse_reverse]
  have : j :: range' (j + 1) (s-1 - j) = range' (0+j) (s-1 - j +1) := by aesop
  rw [this]
  have : range (s) = range' 0 s := by exact range_eq_range'
  rw [this]
  rw [range_eq_range']
  have := @range'_append_1 0 j (s-1-j+1)
  rw [this]
  congr 1
  omega

/--
`R_foldr` states that when conditions are met, `j` will be added to `R` when executing the main foldr loop.
-/
theorem R_foldr (h:¬fs_in X.r j) (h2: ∃ x ∈ Wn ∅ j s, x > 2*j) (hs:j+1≤s):
fs_in (foldr (step s) X (range s).reverse).r j := by
  rw [range_3_way_split hs]
  simp [-foldr_reverse]
  have a0 := @split_lower j j s X h (Nat.le_refl j)
  let fold_lower := (foldr (step s) X (range j).reverse)
  rw [show (foldr (step s) X (range j).reverse) = fold_lower from rfl] at ⊢ a0
  have a1 := @split_middle j s fold_lower a0 h2
  exact fold_preserves_R_mem a1

/--
RiA establishes a relationship between the sets A and R.

Where X represents the output of the construction at some stage `s`, RiA X asserts that:
if some `j` was added to R, that must mean some element of `Wn ∅ (n2c j) s`
was added to A.
-/
def RiA (X s : ℕ) := ∀ j, fs_in X.r j → ∃ x ∈ Wn ∅ (n2c j) s, fs_in X.l x

theorem RiA_step (X s : ℕ) : RiA X s → ∀ k, RiA (step s k X) s := by
  simp [RiA, step]

  -- proved by doing aesop?, then manually resolving dangling cases
  intro h0
  intro k j a
  split
  next h =>
    simp_all only [↓reduceIte]
    split
    next h_1 =>
      simp_all only [↓reduceDIte, pair_r, Nat.testBit_or, Bool.or_eq_true, pair_l]
      cases a with
      | inl h_3 => exact (h0 j h_3).elim λ x hx ↦ ⟨x, @evaln_mono_dom (χ ∅) s s j x (Nat.le_refl s) hx.1, Or.inl hx.2⟩
      | inr h_2 =>
        have kj : k=j := by contrapose h_2; simp [h_2]
        let x := Nat.find h_1
        let hx := Nat.find_spec h_1
        rw [show Nat.find h_1 = x from rfl] at hx ⊢
        simp [kj] at hx ⊢
        use x
        constructor
        exact @evaln_mono_dom (χ ∅) s s j x (Nat.le_refl s) (hx.1)
        simp only [Nat.testBit_two_pow_self, or_true]
    next h_1 => simp_all only [↓reduceDIte, not_exists, not_and, not_lt]
  next h => simp_all only [Bool.true_eq_false, ↓reduceIte, Bool.not_eq_false]

theorem RiA_foldr {X s} : RiA X s → ∀ j, RiA (foldr (step s) X (range j).reverse) s := by
  intro h j
  induction j with
  | zero => simpa
  | succ j ih =>
    simp [listrwgen, -foldr_reverse]
    exact RiA_step _ s ih j

theorem RiA_C : ∀ s, RiA (C s) s := by
  intro s
  induction s with
  | zero => simp [C, RiA]
  | succ s ih =>
    simp [C, RiA, -foldr_reverse]
    intro j h
    rcases @RiA_foldr (C s) s ih s j h with ⟨x,hx0,hx1⟩
    exact ⟨x, @evalnSet_mono_dom ∅ s (s+1) j x (Nat.le_add_right s 1) hx0, hx1⟩

theorem inf_imp_inhabited {A:Set ℕ} (h:A.Infinite) : ∃ y, y ∈ A := by
  simpa using h.nonempty


/--
Auxiliary theorem for theorem `P`, which asserts the positive requirement of the proof.

`P_aux i` states that if `W ∅ i` is infinite, there is a stage at which it shares some element
with `(C s).l`.

the argument goes like this.
  1. suppose W_i is infinite.
  2. by infinitue of W_i, we can find some x>2i in it eventually.
  3. say x is enumerated into W_i by stage s.
  4. Now, we argue about what happens in (C (s+i+2+1)).
     The high stage number is used to ensure that at this stage, x is enumerated into W_i, and
     also that index `i` is considered in the foldr loop.
  5. We ask. Was `i` in R the previous stage?
  5A. If it was, we can use the "preserves" theorems above to show that the desired properties will hold.
  5B. If not, the conditions are set up exactly for `i` to enumerated into `R`, by above theorems.
-/
lemma P_aux (i:ℕ) : (W ∅ i).Infinite → (∃ s, fs_in (C s).r i ∧ ∃ y ∈ W ∅ i, fs_in (C s).l y) := by
  intro h -- 1.
  -- 2.
  have : ∃ x ∈ W ∅ i, x > 2*i := by
    have : ((W ∅ i) \ {x | x ≤ 2*i}).Infinite := by
      have : {x | x ≤ 2*i}.Finite := by exact Set.finite_le_nat (2 * i)
      exact Set.Infinite.diff h this
    rcases inf_imp_inhabited this with ⟨y,hy1,hy2⟩
    exact ⟨y, hy1, Nat.gt_of_not_le hy2⟩
  rcases this with ⟨x, hx0, hx1⟩
  -- 3.
  rcases Wn_complete.mp hx0 with ⟨s,hs⟩
  have si1 : s ≤ s+i+2 := by omega
  have si2 : i+1 ≤ s+i+2 := by omega
  have ex0 : ∃ x ∈ Wn ∅ (n2c i) (s+i+2), x > 2 * i := by
    exact ⟨x, Wn_mono si1 hs, hx1⟩
  -- 4.
  use s+i+2+1
  unfold C
  by_cases h1:fs_in (C (s + i + 2)).r i -- 5.
  · -- 5A
    have a0 := @fold_preserves_R_mem _ (s+i+2) _ (range (s + i + 2)).reverse h1
    constructor
    exact a0
    have := @RiA_foldr (C (s + i + 2)) (s+i+2) (RiA_C (s + i + 2)) (s+i+2)
    exact (this i a0).elim (λ w ⟨hw0,hw1⟩ ↦ ⟨w, Wn_sound hw0, hw1⟩)
  · -- 5B
    have a0 := @R_foldr _ _ _ h1 ex0 si2
    constructor
    exact a0
    have := @RiA_foldr (C (s + i + 2)) (s+i+2) (RiA_C (s + i + 2)) (s+i+2)
    exact (this i a0).elim (λ w ⟨hw0,hw1⟩ ↦ ⟨w, Wn_sound hw0, hw1⟩)

/-- `P i` asserts the `i`th positive requirement. -/
theorem P (i:ℕ) : (W ∅ i).Infinite → (W ∅ i ∩ A).Nonempty := by
  intro h
  rcases P_aux i h with ⟨s, _, hs1⟩
  unfold A
  exact Set.inter_nonempty.mpr $ hs1.elim (λ x hx ↦ ⟨x,hx.1,by simp; use s; exact hx.2⟩)

/--
Asserts that if the foldr loop loops over a list whose elements are all `< ywit`, ywit can never be enumerate into R.
-/
theorem aux3 {s ywit l}
(h : ¬fs_in (C s).r ywit)
(hl : ∀ x, x∈l → x<ywit)
:
¬fs_in (foldr (step s) (C s) l).r ywit := by
  induction l with
  | nil => simp; simp at h; exact h
  | cons head tail ih =>
    simp
    have ih1 := ih ?_; clear ih
    rotate_left
    · intro x a
      simp_all only [Bool.not_eq_true, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp]
    have := @step_preserves_R_not_mem ywit head s _ ih1 (hl head mem_cons_self)
    exact Eq.symm ((fun {a b} ↦ Bool.not_not_eq.mp) fun a ↦ this (id (Eq.symm a)))

theorem A_step_middle {j s x} {X : ℕ}
(h2 : x ∈ Wn ∅ (n2c j) s ∧ x > 2 * j)
(h3 : ∀ t < x, ¬(fun t ↦ t ∈ Wn ∅ (n2c j) s ∧ t > 2 * j) t)
(h4 : ¬fs_in X.r j)
: fs_in (step s j X).l x := by
  have found : ∃ x, (evalnSet ∅ s (n2c j) x).isSome = true ∧ x > 2 * j :=
    Exists.intro x h2
  unfold step
  simp [h4, found]
  apply Or.inr
  apply fs_in_singleton.mpr
  have a0 : Nat.find found ≤ x := Nat.find_min' found h2
  have a1 : x ≤ Nat.find found := by
    contrapose h3
    simp
    use Nat.find found
    exact ⟨Nat.gt_of_not_le h3, Nat.find_spec found⟩
  exact Nat.le_antisymm a1 a0

/--
NaA gives the exact conditions under which `x` is enumerated into `A`.

The reverse direction is easy, by using the above theorems.

For the forward direction, suppose x ∈ A.

That is to say, ∃ s, x ∈ (C s).l.

Let `s` be the smallest such stage.

This then, is the exact stage in which `x` was enumerated. (this is lemma `hx`.)

We can dissect further, and determine the exact *step* in the foldr loop in which `x` was enumerated.

Let i := the exact step. (We define this by noting it must've been enumerated at some step (lemma hstep), and let i be the smallest such one.)

The minimality of `i` is then used to prove the goal.
-/
theorem NaA {x} : x ∈ A ↔ ∃ i s:ℕ, ( ¬fs_in (C s).r i ∧ i+1≤s ∧
  let cond t := t ∈ Wn ∅ i s ∧ t > 2*i
  cond x ∧ ∀ t<x, ¬ cond t
) := by
  constructor
  ·
    intro h
    simp [A] at h
    let s := Nat.find h
    have hs := Nat.find_spec h
    rw [show Nat.find h = s from rfl] at hs
    have a0 : s > 0 := by
      contrapose hs
      simp at hs
      simp [C, hs]
    let sM1 := s-1
    have a1 : s = sM1+1 := by exact (Nat.sub_eq_iff_eq_add a0).mp rfl
    rw [a1] at hs
    simp [C, -foldr_reverse] at hs

    have hx : ¬ fs_in (C sM1).l x := @Nat.find_min _ _ h sM1 (Nat.sub_one_lt_of_lt a0)
    have sM1G1 : sM1 > 0 := by contrapose hs; simp at hs; simp [hs, C]

    have hstep : ∃ j, j+1≤sM1 ∧
    fs_in (foldr (step sM1) (C sM1) ((range' (j + 1) (sM1 - 1 - j)).reverse ++ [j] ++ (range j).reverse)).l x
    ∧
    fs_in (step sM1 j (foldr (step sM1) (C sM1) (range j).reverse)).l x
    := by
      use sM1-1
      have a2 : sM1-1+1 ≤ sM1 := le_of_eq (Nat.sub_add_cancel sM1G1)

      have a3 := range_3_way_split a2
      have a4 : fs_in (foldr (step sM1) (C sM1) ((range' ((sM1-1) + 1) (sM1 - 1 - (sM1-1))).reverse ++ [(sM1-1)] ++ (range (sM1-1)).reverse)).l x := by
        rw [←a3]
        exact hs
      exact ⟨a2,a4, by
        simp only [tsub_self, range'_zero, reverse_nil, nil_append, cons_append, foldr_cons] at a4
        exact a4⟩

    let  i   := Nat.find hstep
    have hi  := Nat.find_spec hstep
    have him := @Nat.find_min _ _ hstep
    rw [show Nat.find hstep = i from rfl] at hi him
    use i
    use sM1
    let sM2 := sM1 - 1
    have sM1rw : sM1 = sM2 + 1 := by exact Eq.symm (Nat.sub_add_cancel sM1G1)

    cases hi2:i with
    | zero =>
      simp only [hi2] at *
      simp [-foldr_reverse] at hi
      have a7 := hi.2.2
      simp [step] at a7
      -- simp at a7

      have r0 : (C sM1).r % 2 = 0 := by
        contrapose a7
        simp [a7]
        exact Eq.symm ((fun {a b} ↦ Bool.not_not_eq.mp) fun a ↦ hx (id (Eq.symm a)))
      simp [r0] at a7

      constructor
      · simp; exact r0
      constructor
      · exact sM1G1

      split at a7
      next hn =>
        have a10 : x = Nat.find hn := by
          simp [hx] at a7
          exact fs_in_singleton.mp a7
        simp [a10]
        have a11 := Nat.find_spec hn
        constructor
        · exact a11.1
        · exact λ t ht ↦ λ a ↦ ht t (Nat.le_refl t) a
      next hn =>
        contrapose hn
        simp at hn ⊢
        exact False.elim (hx a7)

    | succ iM1 =>
    have him1 := @him iM1 (by simp [hi2])
    simp [-foldr_reverse] at him1
    have hi22 := hi.2.2
    have him2 := him1 ?_ ?_
    rotate_left
    · have := hi.1
      rw [hi2] at this
      omega
    · have := hi.2.1
      simp [-foldr_reverse] at this
      have a12 : iM1+1 ≤ sM1 := by omega
      have a13 := range_3_way_split a12
      have hs2 := hs
      simp [a13, -foldr_reverse] at hs2
      exact hs2
    have a12 : iM1+1 ≤ i := by exact Nat.le_of_eq (id (Eq.symm hi2))
    have a13 := range_3_way_split a12
    -- rw [range_eq_range'] at a13
    rw [a13] at hi22
    simp [-foldr_reverse] at hi22
    have : i - 1 - iM1 = 0 := by omega
    simp [this, -foldr_reverse] at hi22
    clear this a13 a12 him1 him sM1rw sM2

    let prev := (step sM1 iM1 (foldr (step sM1) (C sM1) (range iM1).reverse))
    rw [show (step sM1 iM1 (foldr (step sM1) (C sM1) (range iM1).reverse)) = prev from rfl] at hi22 him2

    have a16 : ¬ fs_in prev.r i := by
      simp [step] at hi22
      contrapose hi22
      simp at hi22
      simp [hi22]
      exact him2
    simp [step, a16] at hi22

    constructor
    · contrapose hi22
      simp at hi22
      rw [←hi2] at hi22
      have a14 : fs_in (foldr (step sM1) (C sM1) (range iM1).reverse).r i := by
        have := @fold_preserves_R_mem _ sM1 (C sM1) (range iM1).reverse hi22
        simp [-foldr_reverse] at this
        exact this
      exact fun _ ↦ a16 (step_preserves_R_mem a14)
    constructor
    · omega
    simp only []
    split at hi22
    next hh =>
      have a18 := Nat.find_spec hh
      have a19 := @Nat.find_min _ _ hh
      have a17 : x = Nat.find hh := by
        simp at hi22
        simp [him2] at hi22
        exact fs_in_singleton.mp hi22
      rw [←a17] at a18 a19
      rw [←hi2]
      exact ⟨a18, λ t ht ↦ a19 ht⟩
    next hh => simp [him2] at hi22

  -- the reverse direction.
  · intro h
    rcases h with ⟨j,s,h0,h1,h2,h3⟩
    simp [A]
    use (s+1)
    simp [C, -foldr_reverse]
    rw [range_3_way_split h1]
    simp [-foldr_reverse]
    let fold_lower := (foldr (step s) (C s) (range j).reverse)
    have a0 := @split_lower j j s (C s) h0 (Nat.le_refl j)
    by_cases h : fs_in fold_lower.l x
    · exact fold_preserves_A_mem (@step_preserves_A_mem x s j fold_lower h)
    · exact fold_preserves_A_mem (A_step_middle h2 h3 a0)

theorem aux0 (hx:x∈A) : (NaA.mp hx).choose ≤ x/2 := by
  have hxs := (NaA.mp hx).choose_spec
  let xwit := (NaA.mp hx).choose
  rw [show (NaA.mp hx).choose = xwit from rfl] at *
  let s := hxs.choose
  let hs := hxs.choose_spec
  rw [show hxs.choose=s from rfl] at hs

  have := hs.2.2.1.2
  clear hs s hxs
  omega

theorem hl : ∀ x, x∈(range ywit).reverse → x<ywit := by
  simp [mem_reverse, mem_range]
theorem cst
(hs21 : ywit + 1 ≤ s)
(hs1 : ¬fs_in (C s).r ywit)
(hs221 : (fun t ↦ t ∈ Wn ∅ (Code.n2c ywit) s ∧ t > 2 * ywit) x)
: fs_in (C (s+1)).r ywit := by
  simp [C, range_3_way_split hs21, -foldr_reverse]
  have a2 := aux3 hs1 hl
  let prev := (foldr (step s) (C s) (range ywit).reverse)
  rw [show (foldr (step s) (C s) (range ywit).reverse) = prev from rfl] at a2 ⊢
  have a3 : fs_in (step s ywit prev).r ywit := by
    simp [step]
    simp [a2]
    have h : ∃ x, (evalnSet ∅ s (Code.n2c ywit) x).isSome = true ∧ 2 * ywit < x := ⟨x, hs221⟩
    simp [h]
  have := @fold_preserves_R_mem _ s (step s ywit prev) (range' (ywit + 1) (s - 1 - ywit)).reverse a3
  simp at this; simpa

open Classical Nat in
theorem aux1 (hx:x∈A) (hy:y∈A) (hxy:x≠y) : choose (NaA.mp hx) ≠ choose (NaA.mp hy) := by

  have hxs := choose_spec (NaA.mp hx)
  have hys := choose_spec (NaA.mp hy)
  let xwit := choose (NaA.mp hx)
  let ywit := choose (NaA.mp hy)
  rw [show choose (NaA.mp hx) = xwit from rfl] at *
  rw [show choose (NaA.mp hy) = ywit from rfl] at *

  contrapose hxy
  simp at hxy
  rw [hxy] at hxs

  let s := choose hxs
  let hs := choose_spec hxs
  rw [show choose hxs=s from rfl] at hs

  let s2 := choose hys
  let hs2 := choose_spec hys
  rw [show choose hys=s2 from rfl] at hs2

  have ss2 : s2 = s := by

    -- we show that at step s+1, R contains ywit.
    -- But this contradicts ~.
    have cs := cst hs.2.1 hs.1 hs.2.2.1
    have cs2 := cst hs2.2.1 hs2.1 hs2.2.2.1

    have tri := lt_trichotomy s2 s
    cases tri with
    | inl h =>
      have c0 := fold_preserves_R_mem3 cs2 s h
      have c1 := hs.1
      exact False.elim (c1 c0)
    | inr h =>
    cases h with
    | inl h => exact h
    | inr h =>
      have c0 := fold_preserves_R_mem3 cs s2 h
      have c1 := hs2.1
      exact False.elim (c1 c0)

  rw [ss2] at hs2
  have hs := hs.2.2
  have hs2 := hs2.2.2
  extract_lets at hs hs2; expose_names

  have tri := lt_trichotomy x y
  cases tri with
  | inl h =>
    have a0 := (hs2.2 x h)
    have a1 := hs.1
    exact False.elim (a0 a1)
  | inr h =>
  cases h with
  | inl h => exact fun a ↦ a h
  | inr h =>
    have a0 := (hs.2 y h)
    have a1 := hs2.1
    exact False.elim (a0 a1)

noncomputable def f {i} : {x // x ∈ A ∧ x ≤ 2*i} → ℕ := fun x => (NaA.mp x.property.left).choose
theorem hf_inj : ∀ i, Function.Injective (@f i) :=
by
  intro i x y h
  unfold f at h
  contrapose h
  have := aux1 x.property.left y.property.left
  simp at this
  have := this ?_
  · simp at this ⊢
    exact this

  aesop? says
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨left, right⟩ := property
    obtain ⟨left_1, right_1⟩ := property_1
    simp_all only [Subtype.mk.injEq, not_false_eq_true, forall_const]

theorem hf_le : ∀ x, @f i x ≤ i :=
by
  intro x
  have a0 := aux0 x.property.left
  have a1 := x.property.right
  unfold f
  simp at a0 ⊢
  have : ↑x/2 ≤  i := by omega
  linarith

theorem hf_SetInj : Set.InjOn (@f i) ({x | ↑x∈A ∧ x ≤ 2*i}) := by
  refine Function.Injective.injOn (hf_inj i)

-- #check Set.ncard_le_ncard_of_injOn _ hf_SetInj

theorem setrange_card (i : ℕ) : {x | x ≤ i}.ncard = i + 1 := by
  have h_interval : {x | x ≤ i} = Set.Iio (i + 1) := by
    ext x
    simp [Nat.lt_succ_iff]
  rw [h_interval]
  rw [← Finset.coe_range (i + 1)]
  rw [Set.ncard_coe_finset]
  exact Finset.card_range (i + 1)

theorem Na (i:ℕ) :  Set.ncard (A ∩ {x | x ≤ 2*i}) ≤ i+1 := by
  have a0 := @Set.ncard_le_ncard_of_injOn _ _ _ ({x | x ≤ i}) (@f i) ?_ (@hf_SetInj i) ?_

  -- have a1 : (A ∩ {x | x ≤ 2*i}) = ↑(@setOf { x // x ∈ A ∧ x ≤ 2 * i } fun x ↦ ↑x ∈ A ∧ ↑x ≤ 2 * i) := by sorry
  let s : Set {x // x ∈ A ∧ x ≤ 2*i} := (@setOf { x // x ∈ A ∧ x ≤ 2 * i } fun x ↦ ↑x ∈ A ∧ ↑x ≤ 2 * i)
  rw [show (@setOf { x // x ∈ A ∧ x ≤ 2 * i } fun x ↦ ↑x ∈ A ∧ ↑x ≤ 2 * i) = s from rfl] at a0
  let t : Set ℕ := A ∩ {x | x ≤ 2*i}
  rw [show A ∩ {x | x ≤ 2*i} = t from rfl]
  let f : (a : {x // x ∈ A ∧ x ≤ 2*i}) → a ∈ s → ℕ := λ  a _ => a
  have h₁ :
  ∀ (a : {x // x ∈ A ∧ x ≤ 2*i}) (ha : a ∈ s),
    f a ha ∈ t :=
  by
    intro a ha
    exact a.property
  have h₂ :
  ∀ (a b : {x // x ∈ A ∧ x ≤ 2*i})
    (ha : a ∈ s) (hb : b ∈ s),
    f a ha = f b hb → a = b :=
  by
    intro a b ha hb h
    cases a
    cases b
    cases h
    rfl
  have h₃ :
  ∀ b ∈ t, ∃ a, ∃ ha : a ∈ s, f a ha = b :=
    by
      intro b hb
      refine ⟨⟨b, hb⟩, ?_, rfl⟩
      exact h₁ ⟨b, hb⟩ (h₁ ⟨b, hb⟩ (h₁ ⟨b, hb⟩ (h₁ ⟨b, hb⟩ hb)))
      -- the remaining goal is `⟨b, hb⟩ ∈ s`, which is definitionally true
  have :
    s.ncard = t.ncard := Set.ncard_congr f h₁ h₂ h₃
  rw [←this]


  have a2 : {x | x ≤ i}.ncard = i+1 := by
    exact setrange_card i
  exact le_of_le_of_eq a0 a2

  · simp [hf_le]

  exact Set.finite_le_nat i

theorem Na2 (i:ℕ) : Set.ncard (Aᶜ ∩ {x | x ≤ 2*i}) ≥ i := by
  have a1 := Na i
  have a0 := Set.le_ncard_diff (A ∩ {x | x ≤ 2 * i}) {x | x ≤ 2*i}
  simp at a0

  have a2 : (Aᶜ ∩ {x | x ≤ 2 * i}) = ({x | x ≤ 2 * i} \ A) := by
    aesop
  simp [a2]; clear a2
  have a3 :  {x | x ≤ 2 * i}.ncard  = 2*i+1 := by exact setrange_card (2 * i)
  rw [a3] at a0; clear a3

  let x := (A ∩ {x | x ≤ 2 * i}).ncard
  rw [show (A ∩ {x | x ≤ 2 * i}).ncard = x from rfl] at *
  let y := ({x | x ≤ 2 * i} \ A).ncard
  rw [show ({x | x ≤ 2 * i} \ A).ncard = y from rfl] at *
  omega

theorem Na4 {i} {A : Set ℕ} : A.ncard > i → ∃ y ∈ A, y ≥ i := by
  contrapose
  simp
  intro h
  have a0 : A ⊆ {x | x < i} := by
    aesop
  have a1 := Set.ncard_diff_add_ncard_of_subset a0
  have a2 :  {x | x < i}.ncard = i := by
    cases i with
    | zero => simp
    | succ i =>
      have : {x | x < i + 1} = {x | x ≤ i} := by grind
      rw [this]
      exact setrange_card i
  rw [a2] at a1
  linarith

theorem infinite_iff_unbounded {A : Set ℕ} : Set.Infinite A ↔ (∀ x, ∃ y∈A, y≥x) := by
  constructor
  · intro h x
    contrapose h
    simp at h
    simp
    exact Finite.Set.subset {i | i < x} h

  · intro h
    classical
    by_contra hfin
    simp at hfin
    have hA : Finite A := hfin
    have hne : A.Nonempty := by
      obtain ⟨y, hy, _⟩ := h 0
      exact ⟨y, hy⟩
    let m := (Set.Finite.toFinset hA).max' ((Set.Finite.toFinset_nonempty hA).mpr hne)
    let hm := Finset.le_max' (Set.Finite.toFinset hA)
    obtain ⟨y, hyA, hy⟩ := h (m+1+1)
    have : y ≤ m := hm y ((Set.Finite.mem_toFinset hA).mpr hyA)
    have a1 : y < m+1 := by exact Order.lt_add_one_iff.mpr this
    exact lt_asymm hy a1

theorem NC : Set.Infinite (Aᶜ) := by
  apply infinite_iff_unbounded.mpr
  intro x
  have := Na4 (Na2 (x+1))
  aesop

def c_simple := zero
theorem c_simple_ev : W ∅ c_simple = A := by sorry

theorem exists_simple_set : ∃ A:Set ℕ, simpleIn ∅ A := by
  use A
  rw [←c_simple_ev]
  apply simpleInReq.mp
  constructor
  ·
    rw [c_simple_ev]
    exact NC
  intro c inf
  have a0 := P c
  simp at a0
  have := a0 inf
  rw [c_simple_ev]
  exact Set.nonempty_iff_ne_empty.mp (a0 inf)

end Computability.Simple

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
