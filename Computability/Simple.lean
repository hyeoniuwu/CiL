import Computability.SetOracles

import Mathlib.Data.Nat.BitIndices

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

def C_aux (R:ℕ) : Code := zero
theorem C_aux_evp_0 : Nat.pair x j ∈ (evalp Nat.fzero (C_aux R) s : Option ℕ) → j ≤ s ∧ Nat.testBit R j ∧  x ∈ Wn ∅ j s ∧ x > 2*j := by
  sorry
theorem C_aux_evp_2 : (∃ j ≤ s, Nat.testBit R j ∧ ∃ x ∈ Wn ∅ j s, x ≤ 2*j) → (evalp Nat.fzero (C_aux R) s : Option ℕ).isSome := by
  sorry
theorem C_aux_evp_1 : evalp Nat.fzero (C_aux R) s = 0 ↔ (∀ j ≤ s, Nat.testBit R j → ∀ x ∈ Wn ∅ j s, x ≤ 2*j) := by
  sorry

namespace Computability.Simple
-- /--
-- C for construction.
-- Input: stage `s`
-- Output: (natural representing the simple set A built so far, natural representing set of requirements satisfied so far)
-- -/
noncomputable def C : ℕ→ℕ := λ s ↦
match s with
| 0 => Nat.pair 0 0
| s+1 =>
  have Aₚ := (C s).l
  have Rₚ := (C s).r

  let search : Option ℕ := evalp Nat.fzero (C_aux Rₚ) s
  if halts:search.isSome then
    -- let ⟨x,i⟩ := search.get halts
    let rf := search.get halts
    let Aₛ := fs_add Aₚ rf.l
    let Rₛ := fs_add Rₚ rf.r
    Nat.pair Aₛ Rₛ
  else
    Nat.pair Aₚ Rₚ

  -- search for all i ≤ s:
  -- check i is not already satisfied.
  -- -- first, let i be the smallest unsatisfied requirement P.
  -- now, check if there is a x ∈ W_i,s s.t. x>2i.
  -- if so:
  -- Aₛ = Aₚ + x
  -- Rₛ = Rₚ + i
  -- return Nat.pair Aₛ Rₛ
  -- 0

def A : Set ℕ := ∅
theorem P (i:ℕ) : (W O i).Infinite → (W O i ∩ W O a ≠ ∅) := by
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
