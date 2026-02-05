/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.SetOracles
import Computability.Helper.Sets

/-!
# Simple.lean

In this file we specify the construction procedure of a simple set, roughly following Cooper 2004, proving that it satisfies the positive and negative requirements `P` and `N`.

For the explicit construction of the specification given here, see Constructions/Simple.lean.

## Main declarations

- `simpleIn`: defines simplicity of a set relative to a set oracle, in terms of immunity.
- `Simple.C`: the construction procedure for our simple set.
- `Simple.A`: the simple set built by `C`.
- `Simple.P`: the positive requirement of the simplicity proof, asserting that `A` intersects every infinite c.e. set.
- `Simple.N`: the negative requirement of the simplicity proof, asserting that `A` is coinfinite.

## Notation/quirks

 - Where `x`, `y` are naturals, `⟪x, y⟫ = Nat.pair x y`.

## References

* Cooper 2004, Computability Theory p.91
-/

open Computability
open Computability.Code
open List

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
/-
Alternative characterisation of simplicity of a set; a set is simple iff if it is co-infinite, computable enumerable, and is such that its
complements admits no infinite computable enumerable subset.
-/
theorem simpleInReq : ((W O a)ᶜ.Infinite ∧ ∀ c, (W O c).Infinite → (W O c ∩ W O a ≠ ∅)) ↔ simpleIn O (W O a) := by
  constructor
  · intro ⟨h1,h2⟩
    exact ⟨CEin_trivial, h1, λ c h3 ↦ (nonempt_int_iff_not_subset_compl (W O c) (W O a)).mp (h2 c h3)⟩
  rintro ⟨_, h3, h4⟩;
  exact ⟨h3, λ c h5 ↦ (nonempt_int_iff_not_subset_compl (W O c) (W O a)).mpr (h4 c h5)⟩

section Computability.Simple
namespace Simple
/-! ### Construction of a simple set

#### Structure of proof
We split the proof into 4 main sections;
  · the definition of the construction procedure
  · section step_lemmas: basic lemmas about the main loop in the procedure, detailing when membership in the constructed sets change
  · section positive_requirements: proves `P`.
  · section negative_requirements: proves `N`, by defining a function `f` which maps elements in `A` to the requirement which enumerated them. The bulk of work in this section is dedicated to showing that this function is injective.

-/

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

We implement the main loop via a foldr. The step function is given below.
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
Output:
  ⟪A, R⟫, where
  A = natural representing the simple set A built so far
  R = natural representing set of requirements satisfied so far
-/
noncomputable def C : ℕ → ℕ := λ s ↦
match s with
| 0 => ⟪0, 0⟫
| s+1 => foldr (step s) (C s) (range s).reverse

/-- The simple set built by our construction procedure. -/
def A : Set ℕ := {x | ∃ s, fs_in (C s).l x}

#check List.range'
-- def fmax' (f : ℕ → ℕ) (r : ℕ) := (List.max? (List.map f $ List.range (r+1)))
-- #eval range 5
-- #eval 0 :: range' 1 4
-- theorem fmax'_some : (fmax' f r).isSome := by
--   simp [fmax']
--   have : range (r+1) = 0 :: range' 1 r := by
--     simp [range_eq_range']
--     exact rfl
--   rw [this]
--   simp
-- def fmax (f : ℕ → ℕ) (r : ℕ) := (fmax' f r).get (fmax'_some)
-- def fmax (f : ℕ → ℕ) (r : ℕ) := List.foldl Nat.max (0) (List.range' 1 (r-1))
lemma range_3_way_split_2 {i r : ℕ} (hi : i ≤ r) : (range (r+1)) = range i ++ [i] ++ (range' (i+1) (r-i)) := by
  simp
  -- simp only [append_assoc, cons_append, nil_append, reverse_eq_append_iff, reverse_cons,
    -- reverse_reverse]
  have : i :: range' (i + 1) (r - i) = range' (i) (r - i + 1) := by
    aesop
  rw [this]
  simp [range_eq_range']
  have := @range'_append_1 0 i (r - i + 1)
  simp at this
  rw [this]
  have : r + 1 = i + (r - i + 1) := by
    omega
  rw [←this]
def fmax (f : ℕ → ℕ) (r : ℕ) := List.foldl Nat.max (0) (List.map f $ List.range (r+1))
theorem foldl_max_base : b ≤ foldl Nat.max b l := by
  induction l generalizing b with
  | nil => simp
  | cons head tail ih =>
    simp
    have := @ih (b.max head)
    have : b ≤ b.max head := by exact Nat.le_max_left b head
    exact Nat.le_trans this ih
theorem fmax_max : ∀ i ≤ r, f i ≤ fmax f r := by
  simp [fmax]
  intro i hi

  have := @range_3_way_split_2 i r hi
  rw [this]
  simp only [map_append]
  simp
  apply Nat.le_trans ?_ foldl_max_base
  exact Nat.le_max_right ?_ ?_
  -- have := foldl_max_base

#exit
section step_lemmas
lemma step_preserves_A_mem {j s i X} (h:fs_in X.l j) : fs_in (step s i X).l j := by
  simp [step]; aesop
lemma step_preserves_R_mem {j s i X} (h:fs_in X.r j) : fs_in (step s i X).r j := by
  simp [step]; aesop
lemma step_preserves_R_not_mem {j k s X} (h:¬fs_in X.r j) (hk:k<j) : ¬ fs_in (step s k X).r j := by
  simp [step]
  -- proof mostly generated by aesop?
  simp_all only [Bool.not_eq_true]
  split
  next h_1 =>
    split
    next h_2 =>
      simp_all only [pair_r, Nat.testBit_or, Bool.false_or]
      exact Nat.testBit_two_pow_of_ne (Nat.ne_of_lt hk)
    next h_2 => exact h
  next h_1 => exact h
lemma fold_preserves_R_mem {j s X l} (h:fs_in X.r j) : fs_in (foldr (step s) X l).r j := by
  induction l with
  | nil => simpa
  | cons head tail ih => exact step_preserves_R_mem ih
lemma fold_preserves_R_mem2 {s ywit} (h:fs_in (C s).r ywit) : ∀ i, fs_in (C (s+i)).r ywit := by
  intro i
  induction i with
  | zero => simpa
  | succ i ih =>
    simp [C, -foldr_reverse]
    have := @fold_preserves_R_mem _ (s+i) (C (s + i)) (range (s + i)).reverse ih
    simpa using this
lemma fold_preserves_R_mem3 {s ywit} (h:fs_in (C s).r ywit) : ∀ s2≥s, fs_in (C (s2)).r ywit := by
  intro s2 hs2
  have a0 : s2 = s+(s2-s) := by grind
  have := fold_preserves_R_mem2 h (s2-s)
  rw [← a0] at this
  exact this
lemma fold_preserves_A_mem {j s X l} (h:fs_in X.l j) : fs_in (foldr (step s) X l).l j := by
  induction l with
  | nil => simpa
  | cons head tail ih => exact step_preserves_A_mem ih

/--
Asserts that if the foldr loop loops over a list whose elements are all `< j`,  then `j` can never be enumerate into R.
-/
lemma split_lower {j k s X} (h : ¬ fs_in X.r j) (hk : k ≤ j):
¬ fs_in (foldr (step s) X (range k).reverse).r j := by
  induction k with
  | zero => simp at *; assumption
  | succ k ih =>
    simp [rr_indt, -foldr_reverse]
    have kk : k ≤ j := Nat.le_of_succ_le hk
    have kk2 : k< j := hk
    have := @step_preserves_R_not_mem _ k s _ (ih kk) kk2
    simpa using this
lemma split_middle (h:¬fs_in X.r j) (h2: ∃ x ∈ Wn ∅ j s, x > 2*j) :
fs_in ((step s) j X).r j := by
  simp at h2; simp [step, h, h2]
/--
This lemma is used to rewrite the list in the foldr loop in `C`.

By choosing `j` to be the step in which `x` gets enumerated into `A`, we can neatly segment the
foldr loop into the "lower" section (i.e. `(range j).reverse`) whereby `x` is not enumerated, the "middle" section (i.e. `[j]`) where `x` becomes enumerated in a single step, and the upper section where membership of `x` in `A` is maintained.
-/
lemma range_3_way_split {s j} (hs:j+1≤ s) : (range s).reverse = (range' (j+1) (s-1-j)).reverse ++ [j] ++ (range j).reverse := by
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
lemma R_foldr (h:¬fs_in X.r j) (h2: ∃ x ∈ Wn ∅ j s, x > 2*j) (hs:j+1≤s):
fs_in (foldr (step s) X (range s).reverse).r j := by
  rw [range_3_way_split hs]
  simp [-foldr_reverse]
  have a0 := @split_lower j j s X h (le_refl j)
  let fold_lower := (foldr (step s) X (range j).reverse)
  rw [show (foldr (step s) X (range j).reverse) = fold_lower from rfl] at ⊢ a0
  have a1 := @split_middle j s fold_lower a0 h2
  exact fold_preserves_R_mem a1

/--
RiA establishes a relationship between the sets A and R.

Where X represents the output of the construction at some stage `s`, `RiA X` asserts the following:
if some `j` was added to R, that must mean some element of `Wn ∅ (n2c j) s`
was added to A.
-/
def RiA (X s : ℕ) := ∀ j, fs_in X.r j → ∃ x ∈ Wn ∅ (n2c j) s, fs_in X.l x
lemma RiA_step (X s : ℕ) : RiA X s → ∀ k, RiA (step s k X) s := by
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
      | inl h_3 => exact (h0 j h_3).elim λ x hx ↦ ⟨x, @evaln_mono_dom (χ ∅) s s j x (le_refl s) hx.1, Or.inl hx.2⟩
      | inr h_2 =>
        have kj : k=j := by contrapose h_2; simp [h_2]
        let x := Nat.find h_1
        let hx := Nat.find_spec h_1
        rw [show Nat.find h_1 = x from rfl] at hx ⊢
        simp [kj] at hx ⊢
        use x
        constructor
        exact @evaln_mono_dom (χ ∅) s s j x (le_refl s) (hx.1)
        simp only [Nat.testBit_two_pow_self, or_true]
    next h_1 => simp_all only [↓reduceDIte, not_exists, not_and, not_lt]
  next h => simp_all only [Bool.true_eq_false, ↓reduceIte, Bool.not_eq_false]
lemma RiA_foldr {X s} : RiA X s → ∀ j, RiA (foldr (step s) X (range j).reverse) s := by
  intro h j
  induction j with
  | zero => simpa
  | succ j ih =>
    simp [rr_indt, -foldr_reverse]
    exact RiA_step _ s ih j
lemma RiA_C : ∀ s, RiA (C s) s := by
  intro s
  induction s with
  | zero => simp [C, RiA]
  | succ s ih =>
    simp [C, RiA, -foldr_reverse]
    intro j h
    rcases @RiA_foldr (C s) s ih s j h with ⟨x,hx0,hx1⟩
    exact ⟨x, @evalnSet_mono_dom ∅ s (s+1) j x (Nat.le_add_right s 1) hx0, hx1⟩

end step_lemmas

section positive_requirement
/--
Auxiliary theorem for theorem `P`, which asserts the positive requirement of the proof.

`P_aux i` states that if `W ∅ i` is infinite, there is a stage at which it shares some element
with `(C s).l`.

the argument goes like this.
  1. suppose W_i is infinite.
  2. by infinitude of W_i, we can find some `x>2i` in it eventually.
  3. say `x` is enumerated into W_i by stage `s`.
  4. Now, we argue about what happens in `C (s+i+2+1)`.
     The high stage number is used to ensure that at this stage, `x` is enumerated into W_i, and
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
end positive_requirement

section negative_requirement
-- lemma for `mem_A_iff_enumerated`
lemma A_step_middle {j s x} {X : ℕ}
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
mem_A_iff_enumerated gives the exact conditions under which `x` is enumerated into `A`.

The reverse direction is easy, by using the above theorems.

For the forward direction, suppose x ∈ A.

That is to say, ∃ s, x ∈ (C s).l.

Let `s` be the smallest such stage.

This then, is the exact stage in which `x` was enumerated. (this is lemma `hx`.)

We can dissect further, and determine the exact *step* in the foldr loop in which `x` was enumerated.

Let i := the exact step. (We define this by noting it must've been enumerated at some step (lemma hstep), and let i be the smallest such one.)

The minimality of `i` is then used to prove the goal.
-/
theorem mem_A_iff_enumerated {x} : x ∈ A ↔ ∃ i s:ℕ, ( ¬fs_in (C s).r i ∧ i+1≤s ∧
  let cond t := t ∈ Wn ∅ i s ∧ t > 2*i
  cond x ∧ ∀ t<x, ¬ cond t
) := by
  constructor
  · intro h
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
    fs_in (foldr (step sM1) (C sM1) ((range' (j + 1) (sM1 - 1 - j)).reverse ++ [j] ++ (range j).reverse)).l x ∧
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
    have hi_prop  := Nat.find_spec hstep
    have hi_min := @Nat.find_min _ _ hstep
    rw [show Nat.find hstep = i from rfl] at hi_prop hi_min
    use i; use sM1

    -- we split cases on whether `i` is 0 or not here as the latter case
    -- requires setting up conditions about the `i-1` step of the foldr loop.
    cases hi_val:i with
    | zero =>
      simp only [hi_val] at *
      simp [-foldr_reverse] at hi_prop
      have a7 := hi_prop.2.2
      simp [step] at a7
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
        · exact λ t ht ↦ λ a ↦ ht t (le_refl t) a
      next hn =>
        contrapose hn
        simp at hn ⊢
        exact False.elim (hx a7)

    | succ iM1 =>
    rw [←hi_val]
    have him_temp := @hi_min iM1 (by simp [hi_val])
    simp [-foldr_reverse] at him_temp
    -- h_iM1: x is not enumerated by the (i-1)ᵗʰ step of the foldr loop.
    have h_iM1 := him_temp ?_ ?_; clear him_temp hi_min
    -- h_i: x is enumerated by the iᵗʰ step of the foldr loop.
    have h_i := hi_prop.2.2
    rotate_left
    · have := hi_prop.1
      rw [hi_val] at this
      omega
    · have := hi_prop.2.1
      simp [-foldr_reverse] at this
      have a12 : iM1+1 ≤ sM1 := by omega
      have a13 := range_3_way_split a12
      simp [a13, -foldr_reverse] at hs
      exact hs
    have a12 : iM1+1 ≤ i := by exact Nat.le_of_eq (id (Eq.symm hi_val))
    have a13 := range_3_way_split a12
    rw [a13] at h_i
    simp [-foldr_reverse] at h_i
    have : i - 1 - iM1 = 0 := by omega
    simp [this, -foldr_reverse] at h_i
    clear this a13 a12

    let prev := (step sM1 iM1 (foldr (step sM1) (C sM1) (range iM1).reverse))
    rw [show (step sM1 iM1 (foldr (step sM1) (C sM1) (range iM1).reverse)) = prev from rfl] at h_i h_iM1

    -- h_iM1_R: `i` is not enumerated into R by the (i-1)ᵗʰ step of the foldr loop.
    have h_iM1_R : ¬ fs_in prev.r i := by
      simp [step] at h_i
      contrapose h_i
      simp at h_i
      simp [h_i]
      exact h_iM1
    simp [step, h_iM1_R] at h_i

    constructor
    · contrapose h_iM1_R 
      -- the goal now becomes, if `i∈R` by stage `s-1`, it will be in R later.
      simp at h_iM1_R ⊢
      exact step_preserves_R_mem (@fold_preserves_R_mem _ sM1 (C sM1) (range iM1).reverse h_iM1_R)
    constructor
    · omega
    simp only []
    split at h_i
    next h_found =>
      have a18 := Nat.find_spec h_found
      have a19 := @Nat.find_min _ _ h_found
      have a17 : x = Nat.find h_found := by
        simp at h_i
        simp [h_iM1] at h_i
        exact fs_in_singleton.mp h_i
      rw [←a17] at a18 a19
      exact ⟨a18, λ t ht ↦ a19 ht⟩
    next hh => simp [h_iM1] at h_i

  -- the reverse direction.
  · intro h
    rcases h with ⟨j,s,h0,h1,h2,h3⟩
    simp [A]
    use (s+1)
    simp [C, -foldr_reverse]
    rw [range_3_way_split h1]
    simp [-foldr_reverse]
    let fold_lower := (foldr (step s) (C s) (range j).reverse)
    have a0 := @split_lower j j s (C s) h0 (le_refl j)
    by_cases h : fs_in fold_lower.l x
    · exact fold_preserves_A_mem (@step_preserves_A_mem x s j fold_lower h)
    · exact fold_preserves_A_mem (A_step_middle h2 h3 a0)
/--
`N_aux_0` asserts that if `x∈A`, the requirement that enumerated `x` into `A` is `≤ x/2`.
This is only used as a helper lemma for `N_aux_1`.
-/
lemma N_aux_0 (hx:x∈A) : (mem_A_iff_enumerated.mp hx).choose ≤ x/2 := by
  have := (mem_A_iff_enumerated.mp hx).choose_spec.choose_spec.2.2.1.2
  omega
/-- `N_aux_2` states that under the specified conditions, `ywit` will be enumerated into `R`. -/
lemma N_aux_2 {ywit s x}
(hs21 : ywit + 1 ≤ s)
(hs1 : ¬fs_in (C s).r ywit)
(hs221 : (fun t ↦ t ∈ Wn ∅ (Code.n2c ywit) s ∧ t > 2 * ywit) x)
: fs_in (C (s+1)).r ywit := by
  simp [C, range_3_way_split hs21, -foldr_reverse]
  have a2 := @split_lower ywit ywit s _ hs1 (le_refl ywit)
  let prev := (foldr (step s) (C s) (range ywit).reverse)
  rw [show (foldr (step s) (C s) (range ywit).reverse) = prev from rfl] at a2 ⊢
  have a3 : fs_in (step s ywit prev).r ywit := by
    simp [step, a2]
    have h : ∃ x, (evalnSet ∅ s (Code.n2c ywit) x).isSome = true ∧ 2 * ywit < x := ⟨x, hs221⟩
    simp [h]
  have := @fold_preserves_R_mem _ s (step s ywit prev) (range' (ywit + 1) (s - 1 - ywit)).reverse a3
  simp at this; simpa
/-- We show that `f` is injective. -/
lemma hf_injective_aux (hx:x∈A) (hy:y∈A) (hxy:x≠y) : choose (mem_A_iff_enumerated.mp hx) ≠ choose (mem_A_iff_enumerated.mp hy) := by

  have hxs := choose_spec (mem_A_iff_enumerated.mp hx)
  have hys := choose_spec (mem_A_iff_enumerated.mp hy)
  let xwit := choose (mem_A_iff_enumerated.mp hx)
  let ywit := choose (mem_A_iff_enumerated.mp hy)
  rw [show choose (mem_A_iff_enumerated.mp hx) = xwit from rfl] at *
  rw [show choose (mem_A_iff_enumerated.mp hy) = ywit from rfl] at *

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
    -- we show that at step s+1, R contains ywit, a contradiction.
    have cs := N_aux_2 hs.2.1 hs.1 hs.2.2.1
    have cs2 := N_aux_2 hs2.2.1 hs2.1 hs2.2.2.1

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
/-- `f` maps `x∈A` to the requirement which enumerated it. -/
noncomputable def f {i} : {x // x ∈ A ∧ x ≤ 2*i} → ℕ := fun x => (mem_A_iff_enumerated.mp x.property.left).choose
theorem hf_injective : ∀ i, Function.Injective (@f i) :=
by
  intro i x y h
  unfold f at h
  contrapose h
  have := hf_injective_aux x.property.left y.property.left
  simp at this
  have := this ?_
  · simpa using this

  aesop? says
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨left, right⟩ := property
    obtain ⟨left_1, right_1⟩ := property_1
    simp_all only [Subtype.mk.injEq, not_false_eq_true, forall_const]
theorem hf_le : ∀ x, @f i x ≤ i :=
by
  intro x
  have a0 := N_aux_0 x.property.left
  have a1 := x.property.right
  unfold f
  simp at a0 ⊢
  have : ↑x/2 ≤  i := by omega
  linarith
theorem hf_SetInj : Set.InjOn (@f i) ({x | ↑x∈A ∧ x ≤ 2*i}) := Function.Injective.injOn (hf_injective i)


/--
`N i` is the `i`th negative requirement, stating that `A` is "sparse" enough, which is used to prove that it is coinfinite later.

The proof is standard, given we have already shown that `f` is an injection from `A ∩ {x | x ≤ 2*i}` to `{x | x ≤ i}`.
-/
theorem N (i:ℕ) :  Set.ncard (A ∩ {x | x ≤ 2*i}) ≤ i+1 := by
  have a0 := @Set.ncard_le_ncard_of_injOn _ _ _ ({x | x ≤ i}) (@f i) ?_ (@hf_SetInj i) ?_

  let s : Set {x // x ∈ A ∧ x ≤ 2*i} := (@setOf { x // x ∈ A ∧ x ≤ 2 * i } fun x ↦ ↑x ∈ A ∧ ↑x ≤ 2 * i)
  let t : Set ℕ := A ∩ {x | x ≤ 2*i}
  let f : (a : {x // x ∈ A ∧ x ≤ 2*i}) → a ∈ s → ℕ := λ  a _ => a

  have : s.ncard = t.ncard := Set.ncard_congr f ?_ ?_ ?_
  rotate_left
  · exact fun a ha ↦ ha
  · exact fun a b ha hb a_1 ↦ Subtype.eq a_1
  · exact fun b hb ↦ ⟨⟨b, hb⟩, hb, rfl⟩
  · simp [hf_le]
  · exact Set.finite_le_nat i
  rw [←this]
  exact le_of_le_of_eq a0 (setrange_card i)

-- a more useful rephrasing of the theorem `N` above.
lemma N_alternate (i:ℕ) : Set.ncard (Aᶜ ∩ {x | x ≤ 2*i}) ≥ i := by
  have a1 := N i
  have a0 := Set.le_ncard_diff (A ∩ {x | x ≤ 2 * i}) {x | x ≤ 2*i}
  simp at a0

  have a2 : (Aᶜ ∩ {x | x ≤ 2 * i}) = ({x | x ≤ 2 * i} \ A) := by aesop
  simp [a2]; clear a2
  have a3 := setrange_card (2 * i)
  rw [a3] at a0; clear a3

  omega

theorem A_CoInfinite : Set.Infinite (Aᶜ) := by
  apply infinite_iff_unbounded.mpr
  intro x
  have := big_imp_big_wit (N_alternate (x+1))
  aesop
end negative_requirement

end Simple
end Computability.Simple
