import Computability.Jump
import Computability.Rin
import Computability.Constructions.Eval
import Computability.Constructions.Dovetail
import Computability.Use
import Computability.EvalString
import Mathlib.Order.Basic

import Computability.Constructions.CovRec

open Nat
open scoped Computability
open Classical
open Computability.Code
namespace Computability

-- definitions
noncomputable def χ (O:Set ℕ) : ℕ→ℕ := fun x ↦ if x ∈ O then 1 else 0
theorem χsimp {O} : χ O = fun x ↦ if x ∈ O then 1 else 0 := by exact rfl
@[simp] abbrev SetRecursiveIn (O:Set ℕ) (f:ℕ→.ℕ) : Prop := RecursiveIn (χ O) f
@[simp] abbrev SetTuringReducible (A O:Set ℕ) : Prop := RecursiveIn (χ O) (χ A)
@[simp] abbrev SetTuringReducibleStrict (A O:Set ℕ) : Prop := RecursiveIn (χ O) (χ A) ∧ ¬ RecursiveIn (χ A) (χ O)
@[simp] abbrev SetTuringEquivalent (O A:Set ℕ) : Prop := AntisymmRel SetTuringReducible O A
noncomputable def evalSet (O:Set ℕ) : Code → ℕ→.ℕ := eval (χ O)
@[simp] noncomputable def evalSet₁ (O:Set ℕ) : ℕ→.ℕ := eval₁ (χ O)
@[simp] noncomputable def evalnSet₁ (O:Set ℕ) : ℕ→ℕ := evaln₁ (χ O)
theorem prim_evalnSet₁:Nat.PrimrecIn (χ O) (evalnSet₁ O) := by simp only [evalnSet₁]; exact prim_evaln₁
def SetK0 (A:Set ℕ) := {ex:ℕ | (evalSet A ex.l ex.r).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (evalSet A x x).Dom}
abbrev SetJump := SetK
def jumpn : ℕ → Set ℕ → Set ℕ
| 0 => id
| i+1 => SetJump ∘ jumpn i

-- Order between sets is written in the way below, to be able to make use of automation with ordering thms.
-- that is why we don't write: scoped[Computability] infix:50 "≤ᵀ" => SetTuringReducible
protected theorem SetTuringReducible.refl (A:Set ℕ) : SetTuringReducible A A := by exact RecursiveIn.oracle
protected theorem SetTuringReducible.rfl (A:Set ℕ) : SetTuringReducible A A := SetTuringReducible.refl _
instance : IsRefl (Set ℕ) SetTuringReducible where refl _ := by (expose_names; exact SetTuringReducible.refl x)
theorem SetTuringReducible.trans {A B C:Set ℕ} (hg : SetTuringReducible A B) (hh : SetTuringReducible B C) : SetTuringReducible A C := by
  simp only [SetTuringReducible] at *
  exact TuringReducible.trans hg hh
instance : IsTrans (Set ℕ) SetTuringReducible := ⟨@SetTuringReducible.trans⟩
instance : IsPreorder (Set ℕ) SetTuringReducible where refl := .refl
theorem SetTuringEquivalent.equivalence : Equivalence SetTuringEquivalent := (AntisymmRel.setoid _ _).iseqv
@[refl] protected theorem SetTuringEquivalent.refl (f : Set ℕ) : SetTuringEquivalent f f := Equivalence.refl equivalence f
@[symm] theorem SetTuringEquivalent.symm {f g : Set ℕ} (h : SetTuringEquivalent f g) : SetTuringEquivalent g f := Equivalence.symm equivalence h
@[trans] theorem SetTuringEquivalent.trans (f g h : Set ℕ) (h₁ : SetTuringEquivalent f g) (h₂ : SetTuringEquivalent g h) : SetTuringEquivalent f h := Equivalence.trans equivalence h₁ h₂
instance : IsPreorder (Set ℕ) SetTuringReducible where refl := SetTuringReducible.refl ; trans := @SetTuringReducible.trans
-- Turing degrees are the equivalence classes of sets of naturals under Turing equivalence.
abbrev TuringDegree := Antisymmetrization (Set ℕ) SetTuringReducible
private instance : Preorder (Set ℕ) where
  le := SetTuringReducible
  le_refl := .refl
  le_trans _ _ _ := SetTuringReducible.trans
  lt := SetTuringReducibleStrict
instance TuringDegree.PO : PartialOrder TuringDegree := instPartialOrderAntisymmetrization
notation:100 A"⌜" => SetJump A
def SetTuringDegreeLE (A B : Set ℕ) : Prop := TuringDegree.PO.le ⟦A⟧ ⟦B⟧
def SetTuringDegreeNLE (A B : Set ℕ) : Prop := ¬ TuringDegree.PO.le ⟦A⟧ ⟦B⟧
def SetTuringDegreeLT (A B : Set ℕ) : Prop := TuringDegree.PO.lt ⟦A⟧ ⟦B⟧
def SetTuringDegreeEQ (A B : Set ℕ) : Prop := AntisymmRel TuringDegree.PO.le ⟦A⟧ ⟦B⟧
def SetTuringDegreeIN (A B : Set ℕ) : Prop := (¬TuringDegree.PO.le ⟦A⟧ ⟦B⟧)∧(¬TuringDegree.PO.le ⟦B⟧ ⟦A⟧)
scoped[Computability] infix:50 "≤ᵀ" => SetTuringDegreeLE
scoped[Computability] infix:50 "≰ᵀ" => SetTuringDegreeNLE
scoped[Computability] infix:50 "<ᵀ" => SetTuringDegreeLT
scoped[Computability] infix:50 "≡ᵀ" => SetTuringDegreeEQ
scoped[Computability] infix:50 "|ᵀ" => SetTuringDegreeIN
@[simp] theorem NotSetTuringDegreeNLE_SetTuringDegreeLE : ¬ A ≰ᵀ B ↔ A ≤ᵀ B := by
  unfold SetTuringDegreeNLE
  unfold SetTuringDegreeLE
  simp
section evalSettheorems
theorem exists_code_for_evalSet (O:Set ℕ) (f:ℕ→.ℕ) : SetRecursiveIn O f ↔ ∃ c:Computability.Code, evalSet O c = f := Computability.exists_code
private theorem exists_code_for_evalSet₁ {O:Set ℕ} : ∃ c:Computability.Code, evalSet O c = evalSet₁ O := by apply ((exists_code_for_evalSet O (evalSet₁ O)).mp) rec_eval₁
noncomputable def c_evalSet₁ (O:Set ℕ) := choose (@exists_code_for_evalSet₁ O)
@[simp] theorem c_evalSet₁_ev : evalSet O (c_evalSet₁ O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁
@[simp] theorem c_evalSet₁_ev2 : Computability.eval (χ O) (c_evalSet₁ O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁

private theorem exists_code_for_evalnSet₁ {O:Set ℕ} : ∃ c:Computability.Code, evalSet O c = evalnSet₁ O := by apply ((exists_code_for_evalSet O (evalnSet₁ O)).mp) (Nat.RecursiveIn.of_primrecIn prim_evaln₁)
private theorem exists_prim_code_for_evalnSet₁ : ∃ c, c.code_prim ∧ evalnSet₁ O = evalp (χ O) c := by exact code_prim_of_primrecIn prim_evalnSet₁
noncomputable def c_evalnSet₁ (O:Set ℕ) := choose (@exists_prim_code_for_evalnSet₁ O)
@[simp] theorem c_evalnSet₁_evp : evalp (χ O) (c_evalnSet₁ O) = evalnSet₁ O := by exact (choose_spec exists_prim_code_for_evalnSet₁).right.symm
@[simp] theorem c_evalnSet₁_prim : code_prim (c_evalnSet₁ O) := by exact (choose_spec exists_prim_code_for_evalnSet₁).left
@[simp] theorem c_evalnSet₁_ev2 : eval (χ O) (c_evalnSet₁ O) = evalnSet₁ O := by rw [←@evalp_eq_eval (c_evalnSet₁ O) (χ O) c_evalnSet₁_prim]; simp
@[simp] theorem c_evalnSet₁_ev : evalSet O (c_evalnSet₁ O) = evalnSet₁ O := by simp [evalSet]

private theorem exists_code_for_eval₁ {O:ℕ→ℕ} : ∃ c:Computability.Code, eval O c = eval₁ O := by apply (exists_code.mp) rec_eval₁
noncomputable def c_eval₁ (O:ℕ→ℕ) := choose (@exists_code_for_eval₁ O)
@[simp] theorem c_eval₁_ev : eval O (c_eval₁ O) = eval₁ O := by exact choose_spec exists_code_for_eval₁
-- @[simp] theorem eval₁_code_prop2 : eval (χ O) (eval₁_code O) = eval₁ O := by exact choose_spec exists_code_for_eval₁
end evalSettheorems

-- lemmas
lemma χ_eq_0or1 : (χ O x = 0) ∨ (χ O x = 1) := by
  rw [χsimp]
  cases Classical.em (x ∈ O) with
  | inl h => simp only [h, ↓reduceIte, one_ne_zero, or_true]
  | inr h => simp only [h, ↓reduceIte, zero_ne_one, or_false]
lemma some_comp_simp (a:Part ℕ) {f:ℕ→ℕ} {h:a.Dom}:  (Part.some (f (a.get h)) = a >>= (f:ℕ→.ℕ)) := by
  simp only [bind]
  rw [Part.bind]
  exact Eq.symm (Part.assert_pos h)

namespace Code
section SetJumpTheorems
theorem χ_leq_χSetK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (χ O) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) ex.l ex.r).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl

  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0

  have hg : Nat.RecursiveIn (χ O) g := by exact Nat.RecursiveIn.ite Nat.RecursiveIn.oracle Nat.RecursiveIn.none Nat.RecursiveIn.zero

  have exists_index_for_g : ∃ c : ℕ, eval (χ O) c = g := by exact exists_code_nat.mp hg
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  let f':ℕ→.ℕ := fun x => χK0 (Nat.pair index_g x)

  have f_eq_f': (χ O) = f' := by
      simp only [f']
      funext xs
      simp only [χK0]
      simp only [PFun.coe_val, pair_l, pair_r, Part.coe_some, Part.some_inj]
      rw [index_g_is_g]
      simp only [g]

      cases Classical.em (χ O xs = 0) with
      | inl h => simp [h]
      | inr h =>
        simp only [h]
        simp only [↓reduceIte, Part.some_dom]
        cases χ_eq_0or1
        · (expose_names; exact False.elim (h h_1))
        · (expose_names; exact h_1)

  have f'_recIn_χK0 : Nat.RecursiveIn (χK0) f' := by
    simp only [f']
    refine Nat.RecursiveIn.someTotal (↑χK0) (fun x ↦ χK0 (Nat.pair index_g x)) ?_
    refine Nat.RecursiveIn.totalComp' ?_ ?_
    · exact Nat.RecursiveIn.oracle
    · apply Nat.RecursiveIn.of_primrecIn Nat.PrimrecIn.pair_proj

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK0
theorem χSetK0_leq_K0χ {O:Set ℕ} : Nat.RecursiveIn (K0 (χ O)) (χ (SetK0 O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) ex.l ex.r).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl

  let construction := Nat.sg ∘ K0 (χ O)
  have construction_eq_goal : χK0 = construction := by
    funext xs
    simp only [construction, χK0]
    simp only [Function.comp_apply, Nat.sg, K0, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, ite_not]
  have construction_constructible : Nat.RecursiveIn (K0 (χ O)) construction := by
    simp only [construction]
    exact Nat.RecursiveIn.totalComp (Nat.RecursiveIn.of_primrecIn Nat.PrimrecIn.sg) Nat.RecursiveIn.oracle

  rw [h0]
  rw [construction_eq_goal]
  exact construction_constructible
theorem K0χ_leq_χSetK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (K0 (χ O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) ex.l ex.r).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl
  have h1 (ex:ℕ) : (χK0 ex = 0) = ¬(eval (χ O) ex.l ex.r).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (ex:ℕ) : ¬χK0 ex = 0 = (eval (χ O) ex.l ex.r).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]

  have h3 : (jump (χ O) : ℕ→.ℕ) = (fun ex => if (χK0 ex = 0) then Part.some 0 else (eval (χ O) ex.l ex.r) >>= (Nat.succ:ℕ→.ℕ) :ℕ→.ℕ) := by
    funext xs
    cases Classical.em (χK0 xs = 0) with
    | inl h =>
      simp only [h]
      simp only [↓reduceIte]
      simp only [(h1 xs)] at h
      simp [h]
    | inr h =>
      simp only [h]
      simp only [↓reduceIte]
      rw [χsimp]

      simp only [(h2 xs)] at h
      rw [χsimp] at h
      simp only [PFun.coe_val, jump]
      simp [h]
      -- simp only [h]
      -- simp only [↓reduceDIte]

      apply some_comp_simp

  have h5 : Nat.RecursiveIn (χ O) (fun n ↦ eval (χ O) n.l n.r) := by exact Code.Computability.eval

  rw [h0]
  rw [h3]
  apply Nat.RecursiveIn.ite
  · exact Nat.RecursiveIn.oracle
  · exact Nat.RecursiveIn.zero
  · apply Nat.RecursiveIn.comp
    · exact Nat.RecursiveIn.succ
    · apply TuringReducible.trans' h5 χ_leq_χSetK0
theorem K0χ_eq_χSetK0 (O:Set ℕ) : (K0 (χ O)) ≡ᵀᶠ (χ (SetK0 O)) := ⟨K0χ_leq_χSetK0, χSetK0_leq_K0χ⟩
theorem χSetK0_eq_K0χ (O:Set ℕ) : (χ (SetK0 O)) ≡ᵀᶠ (K0 (χ O)) := (K0χ_eq_χSetK0 O).symm
-- the next two theorems are more or less equivalent to some of the above, with minor tweaks.
theorem χ_leq_χSetK (O:Set ℕ) : Nat.RecursiveIn (χ (SetK O)) (χ O) := by
  let χK : ℕ→ℕ := fun x ↦ if (eval (χ O) (n2c x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = χK := by exact rfl

  -- let compute := (K O) ∘ c_evconst
  -- let h:ℕ→.ℕ := (compute)

  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0

  have hg : Nat.RecursiveIn (χ O) g := by exact Nat.RecursiveIn.ite Nat.RecursiveIn.oracle Nat.RecursiveIn.none Nat.RecursiveIn.zero

  have exists_index_for_g : ∃ c : ℕ, eval (χ O) c = g := by exact exists_code_nat.mp hg
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  let f':ℕ→.ℕ := fun x => χK (c_evconst $ Nat.pair index_g x)

  have f_eq_f': (χ O) = f' := by
    simp only [f']
    funext xs
    simp [χK, c_evconst_ev]

    rw [index_g_is_g]
    simp only [g]

    cases Classical.em (χ O xs = 0) with
    | inl h => simp [h]
    | inr h =>
      simp [h]
      cases χ_eq_0or1
      · (expose_names; exact False.elim (h h_1))
      · (expose_names; exact h_1)

  have f'_recIn_χK : Nat.RecursiveIn (χK) f' := by
    simp only [f']
    refine Nat.RecursiveIn.someTotal (↑χK) (fun x ↦ χK (c_evconst (Nat.pair index_g x))) ?_
    refine Nat.RecursiveIn.totalComp' ?_ ?_
    · exact Nat.RecursiveIn.oracle
    ·
      apply exists_code.mpr
      use (c_ev_const.comp₂ (c_const index_g) c_id)
      simp [Seq.seq, c_evconst]
      exact rfl

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK
theorem Kχ_leq_χSetK (O:Set ℕ) : Nat.RecursiveIn (χ (SetK O)) (K (χ O)) := by
  let χK : ℕ→ℕ := fun x ↦ if (eval (χ O) (n2c x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = χK := by exact rfl
  have h1 (x:ℕ) : (χK x = 0) = ¬(eval (χ O) (n2c x) x).Dom := by
    simp only [χK]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (x:ℕ) : ¬χK x = 0 = (eval (χ O) (n2c x) x).Dom := by
    simp only [χK]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]

  have h3 : (K (χ O) : ℕ→.ℕ) = (fun x => if (χK x = 0) then 0 else (eval (χ O) x x) >>= (Nat.succ:ℕ→.ℕ) :ℕ→.ℕ) := by
    funext xs
    cases Classical.em (χK xs = 0) with
    | inl h =>
      simp only [h]
      simp only [↓reduceIte]
      simp only [(h1 xs)] at h
      simp only [PFun.coe_val, K, h, ↓reduceDIte]
      exact rfl
    | inr h =>
      simp only [h]
      simp only [↓reduceIte]
      rw [χsimp]
      simp only [(h2 xs)] at h
      rw [χsimp] at h
      simp only [PFun.coe_val, K, h, ↓reduceDIte, Part.bind_eq_bind]
      apply some_comp_simp

  have h5 : Nat.RecursiveIn (χ O) (fun x ↦ eval (↑(χ O)) (n2c x) x) := by

    apply Nat.RecursiveIn.eval_K_computable

  rw [h0]
  rw [h3]
  apply Nat.RecursiveIn.ite
  · exact Nat.RecursiveIn.oracle
  · exact Nat.RecursiveIn.zero
  · apply Nat.RecursiveIn.comp
    · exact Nat.RecursiveIn.succ
    · apply TuringReducible.trans' h5 (χ_leq_χSetK O)
theorem χSetK_leq_χSetK0 (O:Set ℕ) : Nat.RecursiveIn (χ (SetK0 O)) (χ (SetK O)) := by
  have main : (χ (SetK O)) = (χ (SetK0 O)) ∘ fun x=> Nat.pair x x := by
    funext xs
    simp only [χ, SetK, Set.mem_setOf_eq, SetK0, Function.comp_apply]
    simp
  rw [main]
  exact Nat.RecursiveIn.totalComp Nat.RecursiveIn.oracle (Nat.RecursiveIn.of_primrecIn (Nat.PrimrecIn.pair Nat.PrimrecIn.id Nat.PrimrecIn.id))
theorem χSetK_eq_Kχ (O:Set ℕ) : (χ (SetK O)) ≡ᵀᶠ (K (χ O)) := ⟨trans (χSetK_leq_χSetK0 O) $ trans (χSetK0_leq_K0χ) $ trans (K0_leq_K (χ O)) $ Nat.RecursiveIn.oracle , Kχ_leq_χSetK O⟩
theorem Kχ_eq_χSetK (O:Set ℕ) : (K (χ O)) ≡ᵀᶠ (χ (SetK O)) := (χSetK_eq_Kχ O).symm
-- #check χK_eq_Kχ
-- why does the below fail?
-- #check K0_eq_K.le

theorem χSetK0_eq_χSetK (O:Set ℕ) : (χ (SetK0 O)) ≡ᵀᶠ (χ (SetK O)) := TuringEquivalent.trans (χSetK0_eq_K0χ O) $ .trans (@K0_eq_K (χ O)) (Kχ_eq_χSetK O)
theorem SetK0_eq_SetK (O:Set ℕ) : (SetK0 O) ≡ᵀ (SetK O) := ⟨(χSetK0_eq_χSetK O).le, (χSetK0_eq_χSetK O).ge⟩
theorem Set_leq_SetK (O:Set ℕ) : O ≤ᵀ (SetK O) := χ_leq_χSetK O

theorem χSetK_eq_K0χ (O:Set ℕ) : (χ (SetK O)) ≡ᵀᶠ (K0 (χ O)) := TuringEquivalent.trans (χSetK_eq_Kχ O) K_eq_K0
theorem K0χ_eq_χSetK (O:Set ℕ) : (K0 (χ O)) ≡ᵀᶠ (χ (SetK O)) := (χSetK_eq_K0χ O).symm

theorem TR_Set_iff_Fn {O₁ O₂} : O₁ ≤ᵀ O₂ ↔ (χ O₁) ≤ᵀᶠ (χ O₂) := Eq.to_iff rfl

theorem SetK0_eq_Jump (O:Set ℕ) : SetK0 O ≡ᵀ O⌜ := SetK0_eq_SetK O

theorem SetJump_not_leq_Set (O:Set ℕ) : ¬O⌜≤ᵀO := by
  intro h
  simp only [SetJump] at h
  apply K_nle_O
  exact .trans (Kχ_leq_χSetK O) h
theorem Set_lt_SetJump (O:Set ℕ) : O<ᵀO⌜ := by
  constructor
  · exact Set_leq_SetK O
  · exact SetJump_not_leq_Set O
end SetJumpTheorems

theorem reducible_iff_code : A≤ᵀB ↔ ∃ c, eval (χ B) c = χ A := by
  simp [TR_Set_iff_Fn, exists_code]

/-- `W O e` := domain of e^th oracle program -/
abbrev W (O:Set ℕ) (e : Code) := (evalSet O e).Dom
/-- `WR O e` := range of e^th oracle program -/
abbrev WR (O:Set ℕ) (e : Code) := (evalSet O e).ran

theorem W_le_SetK0 : ∀ c, W O c ≤ᵀ SetK0 O := by
  intro c
  unfold W
  apply reducible_iff_code.mpr
  use oracle.comp $ pair (c_const c) c_id
  funext x
  simp [evalSet, eval, Seq.seq, SetK0, χ]
  have : ((eval (χ O) c x).Dom) ↔ (∃ y, y ∈ eval (χ O) c x) := Part.dom_iff_mem
  exact if_ctx_congr this (congrFun rfl) (congrFun rfl)

theorem W_le_Jump : ∀ c, W O c ≤ᵀ O⌜ := by
  intro c
  have := @W_le_SetK0 O c
  have h2 := SetK0_eq_Jump O
  exact LE.le.trans_antisymmRel this h2

section dom_to_ran
def c_dom_to_ran (e:Code) := c_ifdom (c_eval.comp₂ (c_const e) c_id) c_id
theorem dom_to_ran_prop : (W O e) = (WR O (c_dom_to_ran e)) := by
  ext xs
  simp [c_dom_to_ran]
  constructor
  · intro h
    simp [evalSet] at h
    rcases h with ⟨y,hy⟩
    use xs
    simp [evalSet, Seq.seq, Part.mem_imp_dom hy]

  ·
    intro h
    simp [PFun.ran] at h
    rcases h with ⟨h0,h1⟩
    simp [evalSet] at h1
    simp [Seq.seq] at h1

    have : xs=h0 := by
      contrapose h1
      split
      next h => simp [h1]
      next h => exact Part.notMem_none xs
    rw [←this] at h1
    split at h1
    · (expose_names; exact Part.dom_iff_mem.mp h)
    · simp_all only [Part.notMem_none]
end dom_to_ran

section ran_to_dom
noncomputable def ran_to_dom (O:ℕ→ℕ) : (Code→Code) := fun c => dovetail (c_if_eq'.comp₂ left ((c_eval₁ O).comp₂ (c_const c) right))
theorem ran_to_dom_ev : (eval O (ran_to_dom O c) y).Dom ↔ ∃ x, y ∈ eval O c x := by
  constructor
  ·
    intro h
    have := dovetail_ev_0 h
    let dvt := ((eval O (c_if_eq'.comp₂ left ((c_eval₁ O).comp₂ (c_const c) right)).dovetail y).get h)
    rw [show ((eval O (c_if_eq'.comp₂ left ((c_eval₁ O).comp₂ (c_const c) right)).dovetail y).get h) = dvt from rfl] at this
    simp at this
    simp [eval] at this
    simp [Seq.seq] at this
    have s1 : ((eval₁ O (Nat.pair c dvt))).Dom := by
      contrapose this
      simp [Part.eq_none_iff'.mpr this]
    simp [Part.Dom.bind s1] at this
    simp [eval₁] at this s1
    use dvt

    suffices y = (eval O c dvt).get s1 from by
      exact (@Part.get_eq_iff_mem ℕ (eval O c dvt) y s1).mp this.symm
    exact this

  ·
    intro h
    rcases h with ⟨h1,h2⟩
    unfold ran_to_dom
    apply dovetail_ev_2.mpr
    use h1
    simp [eval, Seq.seq, eval₁]
    simp [Part.bind_of_mem h2]

theorem ran_to_dom_prop : (WR O e) = (W O (ran_to_dom (χ O) e)) := by
  ext xs
  constructor

  · intro h
    simp at h
    rcases h with ⟨y,hy⟩
    rw [W]
    have halts := ran_to_dom_ev.mpr (Exists.intro y hy)
    simp
    use (eval (χ O) (ran_to_dom (χ O) e) xs).get halts
    exact Part.get_mem halts
  ·
    intro h
    simp at h
    rcases h with ⟨y,hy⟩
    rw [WR]
    have := ran_to_dom_ev.mp (Part.mem_imp_dom hy)
    exact this
end ran_to_dom

section join

def join (A B : Set ℕ) : Set ℕ := {2*x | x∈A} ∪ {2*x+1 | x∈B}
scoped[Computability] infix:50 "∨" => join

theorem even_odd_1 : (1 + y * 2 = x * 2) ↔ False := by grind
theorem even_odd_2 : (y * 2 = 1 + x * 2) ↔ False := by grind

theorem join_upper (A B : Set ℕ) : A ≤ᵀ (A ∨ B) ∧ B ≤ᵀ (A ∨ B) := by
  constructor
  apply reducible_iff_code.mpr
  use oracle.comp c_mul2
  unfold χ
  funext x
  simp [eval, join]
  ac_nf; simp [even_odd_1]

  apply reducible_iff_code.mpr
  use oracle.comp (succ.comp c_mul2)
  unfold χ
  funext x
  simp [eval, join]
  ac_nf; simp [even_odd_2]

theorem bodd_false_mod2 (h:n.bodd=false) : n%2=0 := by
  rw [← codes_aux_aux_0 h]
  exact mul_mod_right 2 n.div2
theorem bodd_true_mod2 (h:n.bodd=true) : n%2=1 := by
  rw [← codes_aux_aux_1 h]
  omega
theorem join_least (A B C : Set ℕ) : A ≤ᵀ C ∧ B ≤ᵀ C → (A ∨ B) ≤ᵀ C := by
  intro ⟨h1,h2⟩
  rcases reducible_iff_code.mp h1 with ⟨c1,hc1⟩
  rcases reducible_iff_code.mp h2 with ⟨c2,hc2⟩
  apply reducible_iff_code.mpr

  use c_ifz.comp₃ (c_mod.comp₂ c_id (c_const 2)) (c1.comp c_div2) (c2.comp c_div2)

  simp [Seq.seq, eval, hc1, hc2]
  unfold χ; simp [join]
  funext x; simp

  cases hx:x.bodd
  ·
    rw [← codes_aux_aux_0 hx]; simp
    ac_nf
    simp [even_odd_1]
  ·
    rw [← codes_aux_aux_1 hx]; simp
    ac_nf
    simp [even_odd_2]

end join
