import Computability.SetOracles

open Computability
open Nat.RecursiveIn.Code


def PFun.nat_graph (f : ℕ→.ℕ) : Set ℕ := { xy | xy.unpair.2 ∈ f xy.unpair.1 }
def total_graph (f : ℕ → ℕ) : Set ℕ := { xy | xy.unpair.2 = f xy.unpair.1 }
theorem partfun_eq_χgraph {f:ℕ→ℕ} : f ≡ᵀᶠ χ (total_graph f) := by sorry



/-- `CEin O A` means that `A` is c.e. in `O`. -/
def CEin (O:Set ℕ) (A:Set ℕ) : Prop := ∃ c:ℕ, A = W O c
@[simp] abbrev CE (A:Set ℕ) := CEin ∅ A
theorem CEin_range : CEin O A ↔ ∃ c:ℕ, A = WR O c := by
  simp only [CEin]
  constructor
  · intro h
    rcases h with ⟨c,hc⟩
    use dom_to_ran O c
    rw [←dom_to_ran_prop]
    exact hc
  · intro h
    rcases h with ⟨c,hc⟩
    use ran_to_dom O c
    rw [←ran_to_dom_prop]
    exact hc

theorem Cin_iff_CEin_CEin' : A≤ᵀB ↔ (CEin B A ∧ CEin B Aᶜ) := by sorry


/-- immuneIn O A := A is immune in O -/
def immuneIn (O:Set ℕ) (A:Set ℕ) : Prop := (A.Infinite) ∧ (∀c:ℕ, (W O c).Infinite → ¬(W O c ⊆ A))
/-- simpleIn O A := A is simple in O -/
def simpleIn (O:Set ℕ) (A:Set ℕ) : Prop := (CEin O A) ∧ immuneIn O Aᶜ
abbrev simple := simpleIn ∅
theorem simple_above_empty (h:simple A): ∅<ᵀA := by sorry

/--`[c_ran_to_dom_aux](x)=0 if x.1.2+1=[x.1.1:O,x.2.2](x.2.1) else 0`-/
noncomputable def c_simple_aux (O:Set ℕ) := c_if_eq'.comp (pair (succ.comp $ right.comp left) ((c_evalnSet₁ O).comp (pair (left.comp left) right)))
@[simp] theorem c_simple_aux_evp (O:Set ℕ) : eval_prim (χ O) (c_simple_aux O) ab = if (Nat.succ ab.l.r=evalnSet₁ O (Nat.pair ab.l.l ab.r)) then 0 else 1 := by
  simp [c_simple_aux, eval_prim]
@[simp]theorem c_simple_aux_ev_pr : code_prim (c_simple_aux O) := by
  simp only [c_simple_aux]
  repeat constructor
  exact c_evalnSet₁_ev_pr
  repeat constructor
theorem c_simple_aux_ev : eval (χ O) (c_simple_aux O) ab = if (Nat.succ ab.l.r=evalnSet₁ O (Nat.pair ab.l.l ab.r)) then 0 else 1 := by
  rw [←@eval_prim_eq_eval (c_simple_aux O) (χ O) c_simple_aux_ev_pr]
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
def lowN (n:ℕ) (A:Set ℕ) : Prop := jumpn n A = jumpn n ∅
abbrev low := lowN 1

theorem low_below_K (h:lowN 1 A) : A<ᵀ∅⌜ := by
  simp [lowN, jumpn] at h
  have h0 : A⌜≡ᵀ∅⌜ := by exact Eq.antisymmRel (congrArg (toAntisymmetrization SetTuringReducible) h)
  have h1 : A<ᵀA⌜ := by exact Set_lt_SetJump
  exact lt_of_lt_of_eq h1 (congrArg (toAntisymmetrization SetTuringReducible) h)

theorem exists_low_simple_set : ∃ A:Set ℕ, simple A ∧ low A := by
  sorry

theorem posts_problem_solution : ∃ A:Set ℕ, CE A ∧ ∅<ᵀA ∧ A<ᵀ∅⌜ := by
  rcases exists_low_simple_set with ⟨A,hA⟩
  use A
  have ⟨h0,h1⟩ := hA
  constructor
  · sorry
  constructor
  · exact simple_above_empty h0
  · exact low_below_K h1
