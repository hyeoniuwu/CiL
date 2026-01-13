import Computability.SetOracles

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
  ·
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
def immuneIn (O:Set ℕ) (A:Set ℕ) : Prop := (A.Infinite) ∧ (∀c:ℕ, (W O c).Infinite → ¬(W O c ⊆ A))
theorem immuneIn_not_CEIn (h:immuneIn O A) : ¬ CEin O A := by
  unfold CEin
  unfold immuneIn at h
  aesop
/-- simpleIn O A := A is simple in O -/
def simpleIn (O:Set ℕ) (A:Set ℕ) : Prop := (CEin O A) ∧ immuneIn O Aᶜ
abbrev simple := simpleIn ∅
theorem simpleIn_not_reducible (h:simpleIn O A): A ≰ᵀ O := by
  contrapose h
  simp at h
  unfold simpleIn
  simp
  intro h2
  unfold immuneIn
  simp

theorem simple_above_empty (h:simple A): ∅<ᵀA := by sorry
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
theorem simpleInReq : ((W O a)ᶜ.Infinite ∧ ∀ c:ℕ, (W O c).Infinite → (W O c ∩ W O a ≠ ∅)) ↔ simpleIn O (W O a) := by
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

/--`[c_ran_to_dom_aux](x)=0 if x.1.2+1=[x.1.1:O,x.2.2](x.2.1) else 0`-/
noncomputable def c_simple_aux (O:Set ℕ) := c_if_eq'.comp (pair (succ.comp $ right.comp left) ((c_evalnSet₁ O).comp (pair (left.comp left) right)))
@[simp] theorem c_simple_aux_evp (O:Set ℕ) : evalp (χ O) (c_simple_aux O) ab = if (Nat.succ ab.l.r=evalnSet₁ O (Nat.pair ab.l.l ab.r)) then 0 else 1 := by
  simp [c_simple_aux, evalp]
@[simp]theorem c_simple_aux_prim : code_prim (c_simple_aux O) := by
  simp only [c_simple_aux]
  repeat constructor
  exact c_evalnSet₁_prim
  repeat constructor
theorem c_simple_aux_ev : eval (χ O) (c_simple_aux O) ab = if (Nat.succ ab.l.r=evalnSet₁ O (Nat.pair ab.l.l ab.r)) then 0 else 1 := by
  rw [←@evalp_eq_eval (c_simple_aux O) (χ O) c_simple_aux_prim]
  simp only [PFun.coe_val, c_simple_aux_evp]
  exact apply_ite Part.some (ab.l.r.succ = evalnSet₁ O (Nat.pair ab.l.l ab.r)) 0 1
def f_simple_ran (O:Set ℕ) : ℕ→ℕ := fun c => curry (c_rfind (c_ifevaleq (ef $ c_evalnSet₁ O))) c
#check c_ef
/-
rfind $ code for function that when given input (e,config):
  runs (evaln e config; if halt, return configinput+1 else 0), and checks: 1. it is non-zero; 2. it is larger than 2e)
  i.e. output >= 2e+1
find the smallest input x which halts when dovetailing e, and such that also x≥2e
-/


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
