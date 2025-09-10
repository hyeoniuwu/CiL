import Computability.Jump
import Computability.Constructions.Eval
import Computability.Use
import Mathlib.Order.Basic

open scoped Computability
open Classical
open Nat.RecursiveIn.Code
-- namespace Computability

-- definitions
noncomputable def χ (O:Set ℕ) : ℕ→ℕ := fun x ↦ if x ∈ O then 1 else 0
theorem χsimp {O} : χ O = fun x ↦ if x ∈ O then 1 else 0 := by exact rfl
@[simp] abbrev SetRecursiveIn (O:Set ℕ) (f:ℕ→.ℕ): Prop := Nat.RecursiveIn (χ O) f
@[simp] abbrev SetTuringReducible (A O:Set ℕ) : Prop := Nat.RecursiveIn (χ O) (χ A)
@[simp] abbrev SetTuringReducibleStrict (A O:Set ℕ) : Prop := Nat.RecursiveIn (χ O) (χ A) ∧ ¬ Nat.RecursiveIn (χ A) (χ O)
@[simp] abbrev SetTuringEquivalent (O A:Set ℕ) : Prop := AntisymmRel SetTuringReducible O A
@[simp] noncomputable def evalSet (O:Set ℕ) : Nat.RecursiveIn.Code → ℕ→.ℕ := eval (χ O)
@[simp] noncomputable def evalSet₁ (O:Set ℕ) : ℕ→.ℕ := eval₁ (χ O)
@[simp] noncomputable def evalnSet₁ (O:Set ℕ) : ℕ→ℕ := evaln₁ (χ O)
theorem prim_evalnSet₁:Nat.PrimrecIn (χ O) (evalnSet₁ O) := by simp only [evalnSet₁]; exact prim_evaln₁
def SetK0 (A:Set ℕ) := {ex:ℕ | (evalSet A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (evalSet A x x).Dom}
abbrev SetJump := SetK
def jumpn : ℕ → Set ℕ → Set ℕ
| 0 => id
| i+1 => SetJump ∘ jumpn i

-- from TuringDegree.lean
protected theorem SetTuringReducible.refl (A:Set ℕ) : SetTuringReducible A A := by exact Nat.RecursiveIn.oracle
protected theorem SetTuringReducible.rfl (A:Set ℕ) : SetTuringReducible A A := SetTuringReducible.refl _
instance : IsRefl (Set ℕ) SetTuringReducible where refl _ := by (expose_names; exact SetTuringReducible.refl x)
theorem SetTuringReducible.trans {A B C:Set ℕ} (hg : SetTuringReducible A B) (hh : SetTuringReducible B C) : SetTuringReducible A C := by
  simp only [SetTuringReducible, SetRecursiveIn] at *
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
@[reducible,simp] def SetTuringDegreeLE (A B : Set ℕ) : Prop := TuringDegree.PO.le ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeLT (A B : Set ℕ) : Prop := TuringDegree.PO.lt ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeEQ (A B : Set ℕ) : Prop := AntisymmRel TuringDegree.PO.le ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeIN (A B : Set ℕ) : Prop := (¬TuringDegree.PO.le ⟦A⟧ ⟦B⟧)∧(¬TuringDegree.PO.le ⟦B⟧ ⟦A⟧)
@[reducible,simp] scoped[Computability] infix:50 "≤ᵀ" => SetTuringDegreeLE
@[reducible,simp] scoped[Computability] infix:50 "<ᵀ" => SetTuringDegreeLT
@[reducible,simp] scoped[Computability] infix:50 "≡ᵀ" => SetTuringDegreeEQ
@[reducible,simp] scoped[Computability] infix:50 "|ᵀ" => SetTuringDegreeIN

section evalSettheorems
theorem exists_code_for_evalSet (O:Set ℕ) (f:ℕ→.ℕ) : SetRecursiveIn O f ↔ ∃ c:Nat.RecursiveIn.Code, evalSet O c = f := by exact exists_code
private theorem exists_code_for_evalSet₁ : ∃ c:Nat.RecursiveIn.Code, evalSet O c = evalSet₁ O := by apply ((exists_code_for_evalSet O (evalSet₁ O)).mp) rec_eval₁
noncomputable def c_evalSet₁ (O:Set ℕ) := choose (@exists_code_for_evalSet₁ O)
@[simp] theorem c_evalSet₁_ev : evalSet O (c_evalSet₁ O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁
@[simp] theorem c_evalSet₁_ev2 : eval (χ O) (c_evalSet₁ O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁

private theorem exists_code_for_evalnSet₁ : ∃ c:Nat.RecursiveIn.Code, evalSet O c = evalnSet₁ O := by apply ((exists_code_for_evalSet O (evalnSet₁ O)).mp) (Nat.RecursiveIn.of_primrecIn prim_evaln₁)
private theorem exists_prim_code_for_evalnSet₁ : ∃ c, c.code_prim ∧ evalnSet₁ O = eval_prim (χ O) c := by exact code_prim_of_primrecIn prim_evalnSet₁
noncomputable def c_evalnSet₁ (O:Set ℕ) := choose (@exists_prim_code_for_evalnSet₁ O)
@[simp] theorem c_evalnSet₁_evp : eval_prim (χ O) (c_evalnSet₁ O) = evalnSet₁ O := by exact (choose_spec exists_prim_code_for_evalnSet₁).right.symm
@[simp] theorem c_evalnSet₁_ev_pr : code_prim (c_evalnSet₁ O) := by exact (choose_spec exists_prim_code_for_evalnSet₁).left
@[simp] theorem c_evalnSet₁_ev2 : eval (χ O) (c_evalnSet₁ O) = evalnSet₁ O := by rw [←@eval_prim_eq_eval (c_evalnSet₁ O) (χ O) c_evalnSet₁_ev_pr]; simp
@[simp] theorem c_evalnSet₁_ev : evalSet O (c_evalnSet₁ O) = evalnSet₁ O := by simp

private theorem exists_code_for_eval₁ : ∃ c:Nat.RecursiveIn.Code, eval O c = eval₁ O := by apply (exists_code.mp) rec_eval₁
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

section SetJumpTheorems
theorem χ_leq_χK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (χ O) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
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
      simp only [PFun.coe_val, Nat.unpair_pair, Part.coe_some, Part.some_inj]
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
    · apply Nat.RecursiveIn.of_primrec Nat.Primrec.pair_proj

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK0
theorem χK0_leq_K0χ {O:Set ℕ} : Nat.RecursiveIn (K0 (χ O)) (χ (SetK0 O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl

  let construction := Nat.sg ∘ K0 (χ O)
  have construction_eq_goal : χK0 = construction := by
    funext xs
    simp only [construction, χK0]
    simp only [Function.comp_apply, Nat.sg, jump.eq_1, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, ite_not]
  have construction_constructible : Nat.RecursiveIn (K0 (χ O)) construction := by
    simp only [construction]
    exact Nat.RecursiveIn.totalComp (Nat.RecursiveIn.of_primrec Nat.Primrec.sg) Nat.RecursiveIn.oracle

  rw [h0]
  rw [construction_eq_goal]
  exact construction_constructible
theorem K0χ_leq_χK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (K0 (χ O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl
  have h1 (ex:ℕ) : (χK0 ex = 0) = ¬(eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (ex:ℕ) : ¬χK0 ex = 0 = (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]

  have h3 : (jump (χ O) : ℕ→.ℕ) = (fun ex => if (χK0 ex = 0) then 0 else (eval (χ O) ex.unpair.1 ex.unpair.2) >>= (Nat.succ:ℕ→.ℕ) :ℕ→.ℕ) := by
    funext xs
    cases Classical.em (χK0 xs = 0) with
    | inl h =>
      simp only [h]
      simp only [↓reduceIte]
      simp only [(h1 xs)] at h
      simp only [PFun.coe_val, jump, h, ↓reduceDIte]
      exact rfl
    | inr h =>
      simp only [h]
      simp only [↓reduceIte]
      rw [χsimp]

      simp only [(h2 xs)] at h
      rw [χsimp] at h
      simp only [PFun.coe_val, jump, Nat.succ_eq_add_one]
      simp only [h]
      simp only [↓reduceDIte]

      apply some_comp_simp

  have h5 : Nat.RecursiveIn (χ O) (fun n ↦ eval (↑(χ O)) (decodeCode (Nat.unpair n).1) (Nat.unpair n).2) := by
    exact RecursiveIn.nat_iff.mp eval_part

  rw [h0]
  rw [h3]
  apply Nat.RecursiveIn.ite
  · exact Nat.RecursiveIn.oracle
  · exact Nat.RecursiveIn.zero
  · apply Nat.RecursiveIn.comp
    · exact Nat.RecursiveIn.succ
    · apply TuringReducible.trans' h5 χ_leq_χK0
theorem K0χ_eq_χK0 {O:Set ℕ} : (K0 (χ O)) ≡ᵀᶠ (χ (SetK0 O)) := ⟨K0χ_leq_χK0, χK0_leq_K0χ⟩
theorem χK0_eq_K0χ {O:Set ℕ} : (χ (SetK0 O)) ≡ᵀᶠ (K0 (χ O)) := K0χ_eq_χK0.symm
-- the next two theorems are more or less equivalent to some of the above, with minor tweaks.
theorem χ_leq_χK {O:Set ℕ} : Nat.RecursiveIn (χ (SetK O)) (χ O) := by
  let χK : ℕ→ℕ := fun x ↦ if (eval (χ O) (decodeCode x) x).Dom then 1 else 0
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
    simp only [χK, c_evconst_ev]
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
    · refine Nat.RecursiveIn.totalComp' ?_ ?_
      · apply Nat.RecursiveIn.of_primrecIn c_evconst_pr
      · apply Nat.RecursiveIn.of_primrec Nat.Primrec.pair_proj

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK
theorem Kχ_leq_χK {O:Set ℕ} : Nat.RecursiveIn (χ (SetK O)) (K (χ O)) := by
  let χK : ℕ→ℕ := fun x ↦ if (eval (χ O) (decodeCode x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = χK := by exact rfl
  have h1 (x:ℕ) : (χK x = 0) = ¬(eval (χ O) (decodeCode x) x).Dom := by
    simp only [χK]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (x:ℕ) : ¬χK x = 0 = (eval (χ O) (decodeCode x) x).Dom := by
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
      simp only [PFun.coe_val, K, h, ↓reduceDIte, Nat.succ_eq_add_one, Part.bind_eq_bind]
      apply some_comp_simp

  have h5 : Nat.RecursiveIn (χ O) (fun x ↦ eval (↑(χ O)) (decodeCode x) x) := by
    apply Nat.RecursiveIn.eval_K_computable

  rw [h0]
  rw [h3]
  apply Nat.RecursiveIn.ite
  · exact Nat.RecursiveIn.oracle
  · exact Nat.RecursiveIn.zero
  · apply Nat.RecursiveIn.comp
    · exact Nat.RecursiveIn.succ
    · apply TuringReducible.trans' h5 χ_leq_χK
theorem χK_leq_χK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (χ (SetK O)) := by
  have main : (χ (SetK O)) = (χ (SetK0 O)) ∘ fun x=> Nat.pair x x := by
    funext xs
    simp only [χ, SetK, Set.mem_setOf_eq, SetK0, Function.comp_apply, Nat.unpair_pair]
  rw [main]
  exact Nat.RecursiveIn.totalComp Nat.RecursiveIn.oracle (Nat.RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id))
theorem Kχ_eq_χK {O:Set ℕ} : (χ (SetK O)) ≡ᵀᶠ (K (χ O)) := by
  constructor
  · apply TuringReducible.trans (χK_leq_χK0)
    apply TuringReducible.trans (χK0_leq_K0χ)
    apply TuringReducible.trans (K0_leq_K (χ O))
    exact Nat.RecursiveIn.oracle
  · exact Kχ_leq_χK

-- why does the below fail?
-- #check K0_eq_K.le

theorem χK0_eq_χK {O:Set ℕ} : (χ (SetK0 O)) ≡ᵀᶠ (χ (SetK O)) := by
  apply TuringEquivalent.trans
  · exact χK0_eq_K0χ
  · apply TuringEquivalent.trans
    · exact K0_eq_K.symm
    · exact Kχ_eq_χK.symm
theorem SetK0_eq_SetK {O:Set ℕ} : (SetK0 O) ≡ᵀ (SetK O) := by
  constructor
  · exact χK0_eq_χK.le
  · exact χK0_eq_χK.ge
theorem Set_leq_SetK {O:Set ℕ} : O ≤ᵀ (SetK O) := χ_leq_χK

theorem SetJump_not_leq_Set {O:Set ℕ} : ¬O⌜≤ᵀO := by
  intro h
  simp only [SetJump] at h
  apply TuringReducible.trans (Kχ_leq_χK) at h
  apply K_not_leq_f
  exact h
theorem Set_lt_SetJump {O:Set ℕ} : O<ᵀO⌜ := by
  constructor
  · exact Set_leq_SetK
  · exact SetJump_not_leq_Set
end SetJumpTheorems


/-- `W O e` := domain of e^th oracle program -/
abbrev W (O:Set ℕ) (e : ℕ) := (evalSet O e).Dom
/-- `WR O e` := range of e^th oracle program -/
abbrev WR (O:Set ℕ) (e : ℕ) := (evalSet O e).ran

section dom_to_ran


theorem code_ef_dom_iff_code_dom : (eval O (c_ef c) x).Dom ↔ (eval O c x).Dom := by
  constructor
  · contrapose
    simp [c_ef]
    intro h
    simp [eval]
    simp [Seq.seq]
    exact h
  · simp [c_ef]
    intro h
    simp [eval]
    simp [Seq.seq]
    exact h
/-- Given a code `e`, returns a code whose range is the domain of `e`. -/
noncomputable def dom_to_ran (O:Set ℕ) : (ℕ→ℕ) := fun e => curry ((comp) (right.comp left) (c_ef (c_evalSet₁ O))) e
-- the internal expression, (comp) (right.comp left) (code_to_code_ef (c_evalSet₁ O)), takes a pair ex as input.
-- code_to_code_ef (c_evalSet₁ O) ex = (ex, [e](x)).
-- piping it into right.comp left returns x.
-- we curry bc we want eval (dom_to_ran e) x = ~

theorem dom_to_ran_prop : (W O e) = (WR O (dom_to_ran O e)) := by
  ext xs
  constructor
  · intro h
    simp at h
    rcases h with ⟨y,hy⟩
    simp [WR]
    simp only [dom_to_ran]
    simp only [decodeCode_encodeCode]
    have h0 : (eval (χ O) e xs).Dom := by
      apply Part.dom_iff_mem.mpr
      exact Exists.intro y hy
    have h5234 : (eval (χ O) (decodeCode (c_evalSet₁ O)) (Nat.pair e xs)).Dom := by
      simp? says simp only [decodeCode_encodeCode, c_evalSet₁_ev2, evalSet₁]
      simp [eval₁]
      exact h0


    rw [PFun.ran]
    simp only [eval_curry, Set.mem_setOf_eq]
    use xs
    simp only [eval, Part.coe_some, Part.bind_eq_bind]
    rw [c_ef_ev]

    apply Part.dom_iff_mem.mp at h5234
    rcases h5234 with ⟨y',hy'⟩
    apply Part.eq_some_iff.mpr at hy'
    rw [hy']

    simp [Seq.seq]

  · contrapose
    intro h
    simp at h
    -- rcases h with ⟨y,hy⟩
    simp [WR]
    simp only [dom_to_ran]
    simp only [decodeCode_encodeCode]
    have h0 : ¬(eval (χ O) e xs).Dom := by
      refine Part.eq_none_iff'.mp ?_
      exact Part.eq_none_iff.mpr h
    have h5234 : ¬(eval (χ O) (decodeCode (c_evalSet₁ O)) (Nat.pair e xs)).Dom := by
      simp [evalSet₁]
      simp [eval₁]
      exact h0

    rw [PFun.ran]
    simp only [eval_curry, Set.mem_setOf_eq]
    simp
    intro x
    simp only [eval, Part.coe_some, Part.bind_eq_bind]
    rw [c_ef_ev]

    cases Classical.em ((eval (χ O) (decodeCode (c_evalSet₁ O)) (Nat.pair e x)).Dom) with
    | inl h' =>
      have h123: ¬ x=xs  := by
        intro hxx
        rw [hxx] at h'
        contradiction
      apply Part.dom_iff_mem.mp at h'
      rcases h' with ⟨y',hy'⟩
      apply Part.eq_some_iff.mpr at hy'
      rw [hy']
      simp [Seq.seq]
      exact fun a ↦ h123 (id (Eq.symm a))
    | inr h' =>
      apply Part.eq_none_iff'.mpr at h'
      rw [h']
      simp [Seq.seq]


private lemma prim_dom_to_ran_aux : Primrec ((right.comp left).comp (decodeCode (c_ef (c_evalSet₁ O)))).curry := by
  refine Primrec.projection ?_
  apply PrimrecIn.PrimrecIn₂_iff_Primrec₂.mp
  exact fun O ↦ curry_prim
theorem Nat.Primrec.prim_dom_to_ran : Nat.Primrec (dom_to_ran O) := by
  unfold dom_to_ran
  refine Primrec.nat_iff.mp ?_
  apply prim_dom_to_ran_aux


end dom_to_ran



theorem rfind'_eqv_rfind : ((Nat.unpaired fun a m => (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) (Nat.pair x 0)) = (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair x n)) := by
-- theorem rfind'_eqv_rfind : ((Nat.unpaired fun a m => (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) ∘ (Nat.pair <$> (fun (n:ℕ)=>n) <*> Part.some 0)) x = (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair x n)) := by
  simp only [Nat.unpaired]
  simp only [Nat.unpair_pair, add_zero, Part.map_eq_map]
  exact rfl


/--`[code_rfind c](x)=smallest n s.t. [c](x,n)=0.`-/
-- def c_rfind : ℕ→ℕ := fun c => comp (rfind' c) (pair Nat.RecursiveIn.Code.id zero)
def c_rfind : Nat.RecursiveIn.Code→Nat.RecursiveIn.Code := fun c => comp (rfind' c) (pair Nat.RecursiveIn.Code.id zero)


/-- Given a code `c` -/
abbrev rfind (O:ℕ→ℕ) : ℕ→ℕ→.ℕ := fun c => fun a=> Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a n)
theorem c_rfind_prop : eval O (c_rfind c) a = (rfind O c a) := by
  unfold c_rfind
  unfold rfind
  rw [←rfind'_eqv_rfind]
  simp? says simp only [decodeCode_encodeCode, Nat.unpaired, Nat.unpair_pair, add_zero, Part.map_eq_map]
  simp only [eval]
  simp only [eval_id]
  simp only [pure]
  simp only [PFun.pure]
  simp only [Seq.seq]
  simp


section ran_to_dom
namespace Nat.RecursiveIn.Code
-- #check evaln₁
/--
Given a code `c`, `dovetail c` gives the code to the function which, on input n,
returns `y` s.t. `[c](n,y)=0`.
-/
-- noncomputable def dovetail_aux (c:Code) : Code := c_evaln.comp₃ (left) c right
-- noncomputable def dovetail (c:Code) : Code := (c_rfind (c_evaln.comp₃ (pair left (left.comp right)) (c_const c) (right.comp right)))
noncomputable def dovetail (c:Code) : Code :=
  c_rfind $
  c_if_eq'.comp₂
  (c_evaln.comp₃ (pair left (left.comp right)) (c_const c) (right.comp right))
  (c_const 1)
-- noncomputable def dovetail (c:Code) : Code := (rfind' (c_evaln.comp₃ (pair left (right.comp left)) (c_const c) (right.comp right))).comp₂ c_id zero
-- theorem dovetail_evp_0 (hc:code_prim c) : y∈eval O (dovetail c) x → eval O c (Nat.pair x y)=0 := by sorry
-- theorem dovetail_evp_0' (hc:code_prim c) (h:(eval O (dovetail c) x).Dom) : eval_prim O c (Nat.pair x ((eval O (dovetail c) x).get h))=0 := by sorry
-- theorem dovetail_evp_1 (hc:code_prim c) : eval O (dovetail c) x=Part.none ↔ ∀ y, eval_prim O c (Nat.pair x y)=0 := by sorry
-- theorem dovetail_ev_0 : y∈eval O (dovetail c) x → eval O c (Nat.pair x y)=0 := by sorry
theorem dovetail_ev_0 (h:(eval O (dovetail c) x).Dom) :
let dvt := (eval O (dovetail c) x).get h
evaln O dvt.r c (Nat.pair x (dvt.l))=Option.some 0 := by
  extract_lets
  expose_names

  unfold dovetail at h
  simp [] at h

  have dvtrw : (eval O
    (c_rfind
      (c_if_eq'.comp
        ((c_evaln.comp ((left.pair (left.comp right)).pair ((c_const c.encodeCode).pair (right.comp right)))).pair
          (c_const 1))))
    x) = (eval O c.dovetail x) := by rfl
  let temprw := (eval O
    (c_rfind
      (c_if_eq'.comp
        ((c_evaln.comp ((left.pair (left.comp right)).pair ((c_const c.encodeCode).pair (right.comp right)))).pair
          (c_const 1))))
    x).get
    h
  have temprwrw : (eval O
    (c_rfind
      (c_if_eq'.comp
        ((c_evaln.comp ((left.pair (left.comp right)).pair ((c_const c.encodeCode).pair (right.comp right)))).pair
          (c_const 1))))
    x).get
    h = temprw := rfl

  have := Part.get_mem h
  rw [temprwrw] at this
  simp [c_rfind_prop] at this
  simp [eval] at this

  rcases this with ⟨⟨h2,h3,h4⟩,h5⟩; clear h5
  simp [Seq.seq] at h3
  rw [h3] at h4; clear h3
  simp at h4
  have temprw_eq_dvt : temprw = dvt := by exact temprwrw
  rw [temprw_eq_dvt] at h4
  have := Part.eq_some_iff.mpr h4; clear h4
  simp at this
  simp [o2n] at this
  apply Encodable.encode_inj.mp
  exact this
theorem dovetail_ev_0' (h:(eval O (dovetail c) x).Dom) :
let dvt := (eval O (dovetail c) x).get h
eval O c (Nat.pair x (dvt.l))=Part.some 0 := by
  have := dovetail_ev_0 h
  extract_lets
  expose_names
  extract_lets at this
  exact Part.eq_some_iff.mpr (evaln_sound this)
-- theorem dovetail_ev_0'' (h:(eval O (dovetail c) x).Dom) : ∃ y, eval O c (Nat.pair x y)=Part.some 0 := by sorry
-- let dvt := (eval O (dovetail c) x).get h
-- evaln O dvt.r c (Nat.pair x (dvt.l))=Option.some 0
theorem dovetail_ev_1' : eval O (dovetail c) x=Part.none ↔ ∀ s y, evaln O s c (Nat.pair x y)≠Option.some 0 := by
  constructor
  · 
    contrapose
    simp
    intro s y
    intro h
    apply Part.not_none_iff_dom.mpr

    unfold dovetail
    simp []
    simp only [c_rfind_prop]
    simp
    use Nat.pair y s
    simp [eval]
    simp [Seq.seq]
    constructor
    · 
      aesop? says
        simp_all only [Encodable.encode_some, Encodable.encode_nat, succ_eq_add_one, zero_add, ↓reduceIte,
        Part.mem_some_iff]
    aesop? says
      intro m a
      split
      next h_1 => simp_all only [Part.some_dom]
      next h_1 => simp_all only [Part.some_dom]

  · 
    contrapose
    intro h
    simp
    have hh := Part.not_none_iff_dom.mp h
    have := dovetail_ev_0 hh

    aesop? says
      apply Exists.intro
      apply Exists.intro
      exact this

theorem dovetail_ev_1_aux : (∀ s y, evaln O s c (Nat.pair x y)≠Option.some 0) ↔ ∀ y, eval O c (Nat.pair x y)≠Part.some 0 := by
  
  constructor
  contrapose
  simp
  intro y
  intro h
  have := evaln_complete.mp (Part.eq_some_iff.mp h)
  aesop

  contrapose
  simp
  intro s y
  intro h
  use y
  exact Part.eq_some_iff.mpr (evaln_sound h)
  
theorem dovetail_ev_1 : eval O (dovetail c) x=Part.none ↔ ∀ y, eval O c (Nat.pair x y)≠Part.some 0 := by
  exact Iff.trans dovetail_ev_1' dovetail_ev_1_aux
theorem dovetail_ev_2 : (eval O (dovetail c) x).Dom ↔ ∃ y, eval O c (Nat.pair x y)=Part.some 0 := by
  have := (@dovetail_ev_1 O c x).not
  simp at this
  exact Iff.trans (Iff.symm Part.not_none_iff_dom) this

theorem Part.eq_some_imp_dom {p:Part ℕ} : p=Part.some x → p.Dom := by
  intro a
  subst a
  exact trivial
theorem Part.mem_imp_dom {p:Part ℕ} : x∈p → p.Dom := λ h ↦ Part.eq_some_imp_dom (Part.eq_some_iff.mpr h)
noncomputable def ran_to_dom (O:ℕ→ℕ) : (ℕ→Code) := fun c => dovetail (c_if_eq'.comp₂ left ((c_eval₁ O).comp₂ (c_const c) right))


theorem ran_to_dom_ev : (eval O (ran_to_dom O c) y).Dom ↔ ∃x,y∈eval O c x := by
  constructor
  ·
    intro h
    -- unfold ran_to_dom at h
    have := dovetail_ev_0' h
    -- rcases this with ⟨dvt,this⟩
    let dvt := ((eval O (c_if_eq'.comp₂ left ((c_eval₁ O).comp₂ (c_const c) right)).dovetail y).get h)
    rw [show ((eval O (c_if_eq'.comp₂ left ((c_eval₁ O).comp₂ (c_const c) right)).dovetail y).get h) = dvt from rfl] at this
    -- rotate_left
    -- ·
    --   repeat (first|assumption|simp|constructor)
    simp at this
    simp [eval] at this
    simp [Seq.seq] at this
    have s1 : ((eval₁ O (Nat.pair c dvt.l))).Dom := by
      contrapose this
      simp [Part.eq_none_iff'.mpr this]
    simp [Part.Dom.bind s1] at this
    simp [eval₁] at this s1
    use dvt.l
    -- set_option diagnostics true in
    suffices y = (eval O (decodeCode c) dvt.l).get s1 from by
      exact (@Part.get_eq_iff_mem ℕ (eval O (decodeCode c) dvt.l) y s1).mp this.symm
    exact this

  ·
    intro h
    rcases h with ⟨h1,h2⟩
    unfold ran_to_dom
    apply dovetail_ev_2.mpr
    use h1
    simp [eval, Seq.seq, eval₁]
    simp [Part.bind_of_mem h2]

theorem asd {p:Part ℕ} (h1:p.Dom) : p.get h1 ∈ p := by exact Part.get_mem h1
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

end Nat.RecursiveIn.Code

end ran_to_dom







namespace Nat.RecursiveIn.Code
def encodeCode_oraclereplacement (o:ℕ) : Code → ℕ
| Code.zero        => 0
| Code.succ        => 1
| Code.left        => 2
| Code.right       => 3
| Code.oracle      => o
| Code.pair cf cg  => 2*(2*(Nat.pair (encodeCode cf) (encodeCode cg))  )   + 5
| Code.comp cf cg  => 2*(2*(Nat.pair (encodeCode cf) (encodeCode cg))  )+1 + 5
| Code.prec cf cg  => 2*(2*(Nat.pair (encodeCode cf) (encodeCode cg))+1)   + 5
| Code.rfind' cf   => 2*(2*(encodeCode cf                            )+1)+1 + 5
end Nat.RecursiveIn.Code

def code_total {O c} := ∀x,(eval O c x).Dom
-- def eval_comp_oracle (h:code_total ∅ oex.l) : ℕ→ℕ := fun oex => eval (eval (Nat.fzero) oex.l) oex.r.l oex.r.r

-- Given a code c, returns a new code which on every oracle query, instead queries the code o.
namespace Nat.RecursiveIn.Code
def c_eval_custom_oracle (o:ℕ) : Code→Code := fun c => encodeCode_oraclereplacement o c
def c_eval_custom_oracle₁ : Code := zero
def c_eval_custom_oracle₁_aux : Code := zero
-- theorem c_eval_custom_oracle₁_ev (code_total Nat.fzero oex.l) : eval O c_eval_custom_oracle₁ oex = eval ()
theorem c_eval_pr_oracle₁_ev (h:code_prim oex.l) : eval O c_eval_custom_oracle₁ oex = eval (eval_prim Nat.fzero oex.l) oex.r.l oex.r.r := by sorry
theorem c_eval_pr_oracle₁_ev_aux : eval_prim O c_eval_custom_oracle₁_aux oe = encodeCode_oraclereplacement oe.l oe.r := by
  unfold c_eval_custom_oracle₁_aux
  sorry
-- eval. but ensures that every query to the oracle is strictly below `use`
-- def eval_clamped
-- (use:ℕ)
-- (O : (n:ℕ) → (n<use) → ℕ)
-- : Code → ℕ →. ℕ
-- | zero => pure 0
-- | succ => fun n => some (n + 1)
-- | left => fun n => some (Nat.unpair n).1
-- | right => fun n => some (Nat.unpair n).2
-- | oracle => fun n => if h:n<use then O n h else Part.none
-- | pair cf cg =>
--     fun n => Nat.pair <$> eval_clamped use O cf n <*> eval_clamped use O cg n
-- | comp cf cg =>
--     fun n => eval_clamped use O cg n >>= eval_clamped use O cf
-- | prec cf cg =>
--     Nat.unpaired fun a n =>
--       n.rec (eval_clamped use O cf a) fun y IH => do
--         let i ← IH
--         eval_clamped use O cg (Nat.pair a (Nat.pair y i))
-- | rfind' cf =>
--     Nat.unpaired fun a m =>
--       (Nat.rfind fun n => (fun x => x = 0) <$> eval_clamped use O cf (Nat.pair a (n + m))).map (· + m)
def eval_clamped
(O : ℕ  → ℕ)
(use:ℕ)
: Code → ℕ →. ℕ
| zero => pure 0
| succ => fun n => some (n + 1)
| left => fun n => some (Nat.unpair n).1
| right => fun n => some (Nat.unpair n).2
| oracle => fun n => if n<use then O n else Part.none
| pair cf cg =>
    fun n => Nat.pair <$> eval_clamped O use cf n <*> eval_clamped O use cg n
| comp cf cg =>
    fun n => eval_clamped O use cg n >>= eval_clamped O use cf
| prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval_clamped O use cf a) fun y IH => do
        let i ← IH
        eval_clamped O use cg (Nat.pair a (Nat.pair y i))
| rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun x => x = 0) <$> eval_clamped O use cf (Nat.pair a (n + m))).map (· + m)
def n2b (n:ℕ) : Bool := if n=0 then false else true
def b2n (b:Bool) : ℕ := if b then 1 else 0

-- theorem eval_clamped_prop': y∈eval_clamped O u c x → y∈eval O c x := by sorry
theorem eval_clamped_prop': eval_clamped O u c x=Part.some y → eval O c x=Part.some y := by sorry
theorem eval_clamped_prop''_aux (h:eval_clamped O u c x=Part.some y): (use O c x).Dom := e2u (Part.eq_some_imp_dom (eval_clamped_prop' h))
-- theorem eval_clamped_prop''_aux' (h:y∈eval_clamped O u c x): (use O c x).Dom := e2u (Part.mem_imp_dom (eval_clamped_prop' h))
theorem eval_clamped_prop'' (h:eval_clamped O u c x=Part.some y): y∈eval O c x ∧ (use O c x).get (eval_clamped_prop''_aux h)≤u := by sorry
theorem eval_clamped_prop''_rev(h:(eval O c x).Dom) (h0:(use O c x).get (e2u h)≤u): eval_clamped O u c x=Part.some ((eval O c x).get h) := by sorry
theorem eval_clamped_prop''_rev2: (use O c x).get h≤u ↔ (eval_clamped O u c x).Dom := by sorry
theorem eval_clamped_prop''_rev3: (∀y,y∈(use O c x)→y≤u) ↔ (eval_clamped O u c x).Dom := by sorry
-- def eval_string (σ:List ℕ) (c:Code) (x:ℕ):= eval_clamped (fun e=> σ.getD e 999) σ.length c x
-- def eval_string (σ:List ℕ) (c:Code) (x:ℕ):= eval_clamped (fun e=> Nat.sg $ σ.getD e 999) σ.length c x
def eval_string (σ:List ℕ) (c:Code) (x:ℕ):= eval_clamped (fun e=> b2n $ n2b $ σ.getD e 999) σ.length c x
end Nat.RecursiveIn.Code
-- theorem asdasd : Primrec c_eval_custom_oracle

-- def D : ℕ→Finset ℕ := fun a => {x | (BSMem (Nat.pair a x))=1}
-- def D : ℕ→Set ℕ := fun a => {x | (BSMem (Nat.pair a x))=1}
set_option linter.dupNamespace false
namespace KP54

#check Finset
-- χ (SetJump ∅)



#check List.Vector
#check List.concat
/-
bsunion doesnt work bc it changes prev values
it should actually just be... join!
so itd be convenient to use lists of bool
but i defined c_list functions for list of naturals...
which is fine. (i think i remember doing that on purpose, because you can interpret the natural that you get from the list afterwards.)
and here i can just directly work with a list of nat anyways, interpreting 0 as false and anything else as true.
-/
-- the proofs later however are simplified if A_s,B_s are treated as List Bool...
-- /mnt/Q/Mathematics/LaTeX/Writings/Computability.pdf
-- c_kp54_aux check if x.r+1 is a finite extension to A for the computation [i](n).
def c_kp54_aux (A i n:ℕ) := zero
theorem c_kp54_aux_evp :
  -- evalSet ∅ (c_kp54_aux A i n) x
  eval fzero (c_kp54_aux A i n) x
    =
  if (eval_string ((n2l A) ++ (n2l (x.r+1))) i n).Dom then Part.some 0 else Part.some 1
:= by
  sorry
theorem c_kp54_aux_2 (halts:(eval fzero (dovetail (c_kp54_aux Aₚ i lb)) 17).Dom) :
  let rf := (eval fzero (dovetail (c_kp54_aux Aₚ i lb)) 17).get halts
  (eval_string ((n2l Aₚ) ++ (n2l (rf+1))) i lb).Dom := by
    extract_lets
    expose_names

    sorry


open Nat List in
/--
Input: stage `s`
Output: (code for `Aₛ`, code for `Bₛ`)
-/
noncomputable def KP54 : ℕ→ℕ := λ s ↦
  if s=0 then Nat.pair 0 0 else

  let i:=(s-1).div2
  let Aₚ := (KP54 (s-1)).l
  let Bₚ := (KP54 (s-1)).r
  let lb := List.length (n2l Bₚ)
  let la := List.length (n2l Aₚ)

  if s%2=0 then
    -- then s=2i+2, and we will work on Rᵢ.
    -- shouldnt be rfind, but dovetail!!!
    let dvt := eval fzero (dovetail (c_kp54_aux Aₚ i lb)) 17
    if halts:dvt.Dom then
      let rf := dvt.get halts
      -- rf is the smallest natural such that
      -- (eval_string ((n2l A) ++ (n2l rf)) i n).Dom
      -- if such rf doesn't exist, that means that there is no (finite) extension of A s.t.
      -- the computation `[i](n)` halts with use ≰ n.
      let Aₛ := (n2l Aₚ) ++ (n2l (rf+1))
      -- let A_result := (eval fzero (c_kp54_aux Aₚ i lb) (Nat.pair 999 rf)).get (sorry)
      let A_result := (eval_string (Aₛ) i lb).get (c_kp54_aux_2 halts)
      Nat.pair Aₛ ((n2l Bₚ).concat (Nat.sg' A_result))
    else
      -- Nat.pair Aₚ (l2n $ (n2l Bₚ).concat 0)
      Nat.pair (l2n $ (n2l Aₚ).concat 0) (l2n $ (n2l Bₚ).concat 0)

  else
    -- then s=2i+1, and we will work on Sᵢ.
    let dvt := eval fzero (dovetail (c_kp54_aux Bₚ i la)) 17
    if halts:dvt.Dom then
      let rf := dvt.get halts
      let Bₛ := (n2l Bₚ) ++ (n2l (rf+1))
      let B_result := (eval_string (Bₛ) i la).get (c_kp54_aux_2 halts)
      -- let B_result := (eval fzero (c_kp54_aux Bₚ i la) rf).get (sorry)
      Nat.pair ((n2l Aₚ).concat (Nat.sg' B_result)) Bₛ
    else
      -- Nat.pair Bₚ (l2n $ (n2l Bₚ).concat 0)
      Nat.pair (l2n $ (n2l Aₚ).concat 0) (l2n $ (n2l Bₚ).concat 0)
    -- Nat.pair 0 0
/-
so we can assert that
A=(KP54 2i).l
B=(KP54 2i).r
Then
evalSet A i ≠ χ B, by using lb
Also remark that the use of evalSet A is below lb
-/



/-
`KP54(s)=(a,b)` where `D a, D b` correspond to sets `A` and `B` at stage `s`.
We note that:
 · by stage 2n,   `χ_B(n)` is bound to be defined.
 · by stage 2n+1, `χ_A(n)` is bound to be defined.

actually now i changed it so that i think
 · by stage n,   `χ_B(n)` is bound to be defined.
 · by stage n,   `χ_A(n)` is bound to be defined.
-/

-- private def A := {x | x ∈ D (KP54 (2*x+1)).l}
-- private def B := {x | x ∈ D (KP54 (2*x)).r}
-- private def A := {x | Nat.BSMem (Nat.pair x (KP54 (2*x+1)).l) = 1}
-- private def B := {x | Nat.BSMem (Nat.pair x (KP54 (2*x)).r)   = 1}
private noncomputable def As (s:ℕ) := n2l (KP54 s).l
private noncomputable def Bs (s:ℕ) := n2l (KP54 s).r
-- private def A := {x | (As x)[x]? = some 1}



#check List.IsPrefix
theorem ABgetsextended : (As i) <+: (As (i+1)) ∧ (Bs i) <+: (Bs (i+1)) := by
  unfold As
  unfold Bs
  rw (config:={occs:=.pos [2,3]}) [KP54]
  simp (config := { zeta := false }) [-Nat.rfind_dom]
  lift_lets
  extract_lets
  expose_names
  if h0:(i + 1) % 2 = 0 then
    simp [h0,-Nat.rfind_dom]
    aesop
  else
    simp [h0,-Nat.rfind_dom]
    aesop
theorem ABgetsextended2 : (As i) <+: (As (i+j)) ∧ (Bs i) <+: (Bs (i+j)) := by
  induction j with
  | zero => simp_all
  | succ jM1 ihj =>
    rw [←add_assoc]
    constructor
    exact List.IsPrefix.trans ihj.left (@ABgetsextended (i + jM1)).left
    exact List.IsPrefix.trans ihj.right (@ABgetsextended (i + jM1)).right
theorem ABgetsextended3 (h:i≤j) : (As i) <+: (As j) ∧ (Bs i) <+: (Bs j) := by
  rw [Eq.symm (Nat.add_sub_of_le h)]
  exact ABgetsextended2
theorem Agetsextended4
(hi:k<(As i).length)
(hh:k<(As j).length)
: (As i)[k] = (As j)[k] := by
  cases Classical.em (i≤j) with
  | inl h =>
    have := (ABgetsextended3 h).left
    exact List.IsPrefix.getElem this hi
  | inr h =>
    simp at h
    have := (ABgetsextended3 (Nat.le_of_succ_le h)).left
    exact Eq.symm (List.IsPrefix.getElem this hh)
theorem Bgetsextended4
(hi:k<(Bs i).length)
(hh:k<(Bs j).length)
: (Bs i)[k] = (Bs j)[k] := by
  cases Classical.em (i≤j) with
  | inl h =>
    have := (ABgetsextended3 h).right
    exact List.IsPrefix.getElem this hi
  | inr h =>
    simp at h
    have := (ABgetsextended3 (Nat.le_of_succ_le h)).right
    exact Eq.symm (List.IsPrefix.getElem this hh)
theorem Agetsextended5
(hii : ii < (As (j)).length)
(asz : ii < (As (k)).length)
:
((As (j))[ii]?.getD smth) = (As (k))[ii] := by
  have : ((As (j))[ii]?.getD smth) = (As (k))[ii] := by
    have : (As (j))[ii]?.getD smth = (As (j))[ii] := by simp only [getElem?_pos, Option.getD_some,hii]
    rw [this]
    exact Agetsextended4 hii asz
  rw [this]
theorem AsSize_o2e : (As (2*i+1)).length = (As (2*i)).length + 1 := by
  rw [As, KP54]
  simp (config := { zeta := false })
  extract_lets; expose_names
  if h0:(dvt).Dom then simp [h0]; rfl
  else simp [h0]; rfl
theorem AsSize_e2o : (As (2*i+1)).length < (As (2*i+2)).length:= by
  rw (config:={occs:=.pos [2]}) [As]
  unfold KP54
  simp (config := { zeta := false })
  extract_lets; expose_names
  rw [show As (2*i+1) = n2l Aₚ from rfl]
  if h0:(dvt).Dom then simp [h0]
  else simp [h0]
-- theorem asd : i=(i/2)*2 ∨ i=(i/2)*2+1 := by
--   #check Nat.even_or_odd
--   #check Odd
--   omega
  -- grind
theorem AsSize_mono' : (As i).length < (As (i+1)).length := by
  cases Nat.even_or_odd i with
  | inl h =>
    rcases h with ⟨h1,h2⟩
    have := @AsSize_o2e h1
    have a0 : i=2*h1 := by
      rw [h2]
      exact Eq.symm (Nat.two_mul h1)
    rw [a0]
    simp_all only [lt_add_iff_pos_right, zero_lt_one]
  | inr h =>
    rcases h with ⟨h1,h2⟩
    have := @AsSize_e2o h1
    rw [h2]
    simp_all only []
theorem AsSize_mono (hij:i<j) : (As i).length < (As j).length := by
  have a0 := @AsSize_mono' i
  have a1 := (@ABgetsextended3 (i+1) j (hij)).left
  exact Nat.lt_of_lt_of_le a0 (List.IsPrefix.length_le a1)
theorem BsSize_o2e : (Bs (2*i+2)).length = (Bs (2*i+1)).length + 1 := by
  rw [Bs, KP54]
  simp (config := { zeta := false })
  extract_lets; expose_names
  if h0:(dvt).Dom then simp [h0]; rfl
  else simp [h0]; rfl
theorem BsSize_e2o : (Bs (2*i)).length < (Bs (2*i+1)).length:= by
  rw (config:={occs:=.pos [2]}) [Bs]
  unfold KP54
  simp (config := { zeta := false })
  extract_lets; expose_names
  rw [show Bs (2*i) = n2l Bₚ from rfl]
  if h0:(dvt).Dom then simp [h0]
  else simp [h0]
theorem BsSize_o2e': (Bs (2 * (i + 1) - 1)).length < (Bs (2 * (i + 1))).length := by
  have : 2 * (i + 1) - 1 = 2*i+1 := by exact rfl
  rw [this]
  have : 2*(i+1) = 2*i + 2:= by exact rfl
  rw [this]
  have := @BsSize_o2e i
  simp_all only [Nat.add_one_sub_one, lt_add_iff_pos_right, zero_lt_one]
theorem Asexext (hij:i<j): ∃ lM1, (As i)++(n2l (lM1+1))=As j := by
  have a0 := (@ABgetsextended3 i j (Nat.le_of_succ_le hij)).left
  have a1 : (As i).length < (As j).length := by exact AsSize_mono hij
  rcases a0 with ⟨h1,h2⟩
  have a2 : h1.length > 0 := by grind
  have a3 : l2n h1 ≠ 0 := by
    contrapose a2
    simp at a2 ⊢
    apply Encodable.encode_inj.mp a2
  have a4 : (l2n h1)-1+1=l2n h1 := by exact Nat.succ_pred_eq_of_ne_zero a3
  use (l2n h1)-1
  simp [a4]
  exact h2
  
  -- exact?
theorem AsBsSize : i≤(As i).length ∧ i≤(Bs i).length := by
  induction i with
  | zero => exact ⟨Nat.zero_le (As 0).length, Nat.zero_le (Bs 0).length⟩
  | succ i ih =>
    unfold As
    unfold Bs
    unfold KP54
    simp (config := { zeta := false }) [-Nat.rfind_dom]
    lift_lets
    extract_lets
    expose_names
    if h0:(i + 1) % 2 = 0 then
      simp [h0,-Nat.rfind_dom]
      if h1 : (dvt).Dom  then
        simp [h1,-Nat.rfind_dom]
        constructor
        refine Nat.add_le_add ih.left ?_
        exact Nat.le_add_left 1 _
        exact ih.right
      else
        simp [h1,-Nat.rfind_dom]
        exact ih
    else
      simp [h0,-Nat.rfind_dom]
      if h1 : (dvt_1).Dom  then
        simp [h1,-Nat.rfind_dom]
        constructor
        exact ih.left
        refine Nat.add_le_add ih.right ?_
        exact Nat.le_add_left 1 _
      else
        simp [h1,-Nat.rfind_dom]
        exact ih
theorem AsSize : i<(As (i+1)).length := (@AsBsSize (i+1)).left
theorem BsSize : i<(Bs (i+1)).length := (@AsBsSize (i+1)).right
-- private def A := {x | (As (x+1))[x]'AsSize≠0}
private def A := {x | n2b $ (As (x+1))[x]'AsSize}
private def B := {x | n2b $ (Bs (x+1))[x]'BsSize}
-- private def B := {x | (Bs (x+1))[x]'BsSize≠0}
private def Atest := {x | (n2l (KP54 (x)).l)[x]? = some 1}

noncomputable def Bsize (i:ℕ) := (Bs i).length
-- private theorem Rasd (i:ℕ) (h:(eval_string (As (2*(i+1))) i (Bsize i)).Dom): (eval_string (As (2*(i+1))) i (Bsize i)).get h ≠ (χ B) (Bsize i) := by

-- use (n2l ((KP54 (2 * (i + 1) - 1)).r)).length
-- private theorem Rasd (i:ℕ) : ∃ k,(eval_string (As (2*i)) i (k)) ≠ (Bs (2*i))[k]'(by
-- DELETE THE BELOW
private theorem Rasd (i:ℕ) (hi:0<i):
-- let k := (n2l (Bs (2*(i)))).length-1
let k := (n2l (Bs (2*i-1))).length
(eval_string (As (2*(i))) i (k)) ≠ (Bs (2*(i)))[k]'(by
  -- unfold Bsize
  -- rw [show k=(n2l (l2n (Bs (2 * i)))).length-1 from rfl]
  rw [show k=(n2l (l2n (Bs (2 * i - 1)))).length from rfl]
  simp

  sorry
  ) := by
  -- unfold As
  -- unfold B
  -- simp only []
  extract_lets
  expose_names

  unfold Bs
  unfold As
  -- unfold χ
  unfold KP54
  simp (config := { zeta := false }) [-Nat.rfind_dom]
  lift_lets
  extract_lets
  expose_names
  -- have i_1_simp: i_1 = i := by exact Nat.div2_bit0 i
  have i_1_simp: i_1 = i := rfl
  simp (config := { zeta := false }) only [i_1_simp]
  cases i with
  | zero => contradiction
  | succ i =>
  -- sorry
  -- use lb
  simp (config := { zeta := false }) [-Nat.rfind_dom]
  -- have h0:2 * (i + 1) % 2 = 0 := by exact Nat.mul_mod_right 2 (i + 1)
  -- if h0:(Bsize i + 1) % 2 = 0 then
  -- simp (config := { zeta := false }) [h0, -Nat.rfind_dom]
  -- if h1: (rfind Nat.fzero (c_kp54_aux Aₚ (i_1) lb).encodeCode 17).Dom then
  if h1: (rfind Nat.fzero (c_kp54_aux Aₚ (i+1) lb).encodeCode 17).Dom then
  simp (config := { zeta := false }) [h1, -Nat.rfind_dom]
  -- simp (config := { zeta := false })
  lift_lets
  extract_lets
  expose_names
  have : k=lb := by
    rw [show k=(n2l (l2n (Bs (2 * (i+1) - 1)))).length from rfl]
    simp
    rw [show lb=(n2l Bₚ).length from rfl]
    unfold Bs
    rw [show Bₚ=(KP54 (2 * (i + 1) - 1)).r from rfl]
  simp [this]
  have lbrw : lb = (n2l Bₚ).length := rfl

  simp only [lbrw]
  simp
  have aaa : A_result = (eval_string (n2l Aₚ ++ n2l (rf + 1)) (decodeCode i_1) lb).get (c_kp54_aux_2
    (Eq.mpr_prop (Eq.refl (rfind Nat.fzero (c_kp54_aux Aₚ i_1 lb).encodeCode 17).Dom)
      (Eq.mpr_prop
        (congrArg (fun x ↦ (rfind Nat.fzero (c_kp54_aux Aₚ x lb).encodeCode 17).Dom) i_1_simp)
        (of_eq_true (eq_true h1))))) := rfl

  simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at aaa
  have : (n2l Aₚ ++ n2l (rf + 1))=Aₛ:= rfl
  simp only [this] at aaa
  simp (config := { zeta := false }) only [i_1_simp] at aaa
  simp only [←lbrw]
  have Aresrw : eval_string Aₛ (decodeCode (i + 1)) lb = Part.some A_result := by
    rw [aaa]
    simp
  rw [Aresrw]
  cases A_result <;> simp

  else
  simp (config := { zeta := false }) [h1, -Nat.rfind_dom]
  sorry

theorem Rasd2_aux : (n2l (Bs (2*(i+1)-1))).length < (Bs (2*(i+1))).length := by
  simp only [Denumerable.ofNat_encode]
  exact BsSize_o2e'
private theorem Rasd2 (i:ℕ) (h:(eval_string (As (2*(i+1))) i ((n2l (Bs (2*(i+1)-1))).length)).Dom):
-- let k := (n2l (Bs (2*(i)))).length-1
let k := (n2l (Bs (2*(i+1)-1))).length
(eval_string (As (2*(i+1))) i k).get h ≠ b2n (n2b $ (Bs (2*(i+1)))[k]'(Rasd2_aux)) := by
  -- unfolding
  extract_lets
  expose_names
  unfold Bs
  unfold As
  unfold KP54
  simp (config := { zeta := false }) [-Nat.rfind_dom]
  lift_lets
  extract_lets
  expose_names
  have i_1_simp: i_1 = i := Nat.div2_bit1 i
  have keqlb : k=lb := by
    rw [show k=(n2l (l2n (Bs (2 * (i+1) - 1)))).length from rfl]
    simp
    rw [show lb=(n2l Bₚ).length from rfl]
    unfold Bs
    rw [show Bₚ=(KP54 (2 * (i + 1) - 1)).r from rfl]


  if h1: (dvt).Dom then
  simp (config := { zeta := false }) [h1, -Nat.rfind_dom]
  lift_lets
  extract_lets
  expose_names

  simp [keqlb]
  have lbrw : lb = (n2l Bₚ).length := rfl
  simp only [lbrw]
  simp
  have aaa : A_result = (eval_string (n2l Aₚ ++ n2l (rf + 1)) (decodeCode i_1) lb).get (c_kp54_aux_2
    (Eq.mpr_prop (Eq.refl (dvt).Dom)
      (Eq.mpr_prop
        (congrArg (fun x ↦ (dvt).Dom) i_1_simp)
        (of_eq_true (eq_true h1))))) := rfl

  simp [-Denumerable.list_ofNat_succ] at aaa
  have : (n2l Aₚ ++ n2l (rf + 1))=Aₛ:= rfl
  simp only [this] at aaa
  simp (config := { zeta := false }) only [i_1_simp] at aaa
  simp only [←lbrw]
  have Aresrw : eval_string Aₛ (decodeCode (i)) lb = Part.some A_result := by
    rw [aaa]
    simp
  simp [Aresrw]
  cases A_result <;> simp [n2b,b2n]


  
  else
  exfalso
  have keqlb_2 : (n2l (l2n (Bs (2 * (i + 1) - 1)))).length = lb := by exact keqlb
  rw [keqlb_2] at h
  rw [show dvt = eval Nat.fzero (c_kp54_aux Aₚ i_1 lb).dovetail 17 from rfl] at h1
  have := dovetail_ev_1.mp (Part.eq_none_iff'.mpr h1)
  clear h1
  -- simp? [c_kp54_aux_evp] at this
  simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at this

  have Aprw : n2l Aₚ = As (2*i+1) := rfl
  rw [Aprw] at this
  have aux0 : 2*(i+1) = 2*i+2 := rfl
  rw [aux0] at h
  -- have := @Asexext' (2*i+1)
  have := @Asexext (2*i+1) (2*i+2) (Nat.lt_add_one (2 * i + 1))
  rcases this with ⟨h1,h2⟩
  have := this h1
  rw [h2] at this
  rw [show 2 * i + 1 + 1= 2*i+2 from rfl] at this
  rw [i_1_simp] at this
  exact this h


theorem Aextends : eval_string (As (2*i)) i k=Part.some y → evalSet A i k=Part.some y := by
  unfold A

  simp
  unfold χ
  simp
  unfold eval_string
  simp
  intro h
  rcases eval_clamped_prop'' h with ⟨h0,h1⟩
  -- apply Part.eq_some_iff.mp
  have h2 := Part.eq_some_iff.mpr h0
  clear h0
  rw [←h2]
  apply Eq.symm
  apply use_principle_eval
  rotate_left
  exact Part.eq_some_imp_dom h2

  suffices ∀ i_1 < (As (2 * i)).length,
  b2n (n2b ((As (2 * i))[i_1]?.getD 999)) = if n2b ((As (i_1 + 1))[i_1]'AsSize) = true then 1 else 0
    from by
    intro h3 h4
    have h5 := this h3 (Nat.le_trans h4 h1)
    simp only [h5, ite_eq_ite]

  intro ii hii
  have asz := @AsSize ii
  rw [@Agetsextended5 ii (2*i) (ii + 1) 999 hii asz]
  rfl


  -- have := eval_clamped_prop

theorem Aextends''''' :
let k:=(n2l (Bs (2*(i+1)-1))).length
¬(eval_string (As (2*(i+1))) i k).Dom → ¬(evalSet A i k).Dom := by
  extract_lets
  expose_names
  -- intro h
  unfold As
  unfold KP54
  simp (config := { zeta := false })
  lift_lets
  extract_lets
  expose_names
  have i_1_simp: i_1 = i := Nat.div2_bit1 i
  have keqlb : k=lb := by
    rw [show k=(n2l (l2n (Bs (2 * (i+1) - 1)))).length from rfl]
    simp
    rw [show lb=(n2l Bₚ).length from rfl]
    unfold Bs
    rw [show Bₚ=(KP54 (2 * (i + 1) - 1)).r from rfl]
  
  if h0:(dvt).Dom then
  simp (config := { zeta := false }) [h0]
  lift_lets
  extract_lets
  expose_names
  simp
  intro h
  exfalso
  have := c_kp54_aux_2 h0
  simp [-Denumerable.list_ofNat_succ] at this
  rw [i_1_simp] at this
  have a0 : (n2l Aₚ ++ n2l ((eval Nat.fzero (c_kp54_aux Aₚ i lb).dovetail 17).get h0 + 1)) = Aₛ := by exact rfl
  rw [a0] at this
  rw [keqlb] at h
  exact h this



  else
  simp at h0
  simp (config := { zeta := false }) [h0]
  have a0 : eval Nat.fzero (c_kp54_aux Aₚ i_1 lb).dovetail 17 = Part.none := by exact Part.eq_none_iff'.mpr h0
  
  have a1 := dovetail_ev_1.mp a0; clear a0
  simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at a1
  intro h; clear h
  contrapose a1
  simp at a1
  simp [-Denumerable.list_ofNat_succ]
  
  rw [i_1_simp]
  rw [←keqlb]

  -- unfold A at a1
  -- unfold χ at a1
  -- simp at a1
  simp only [eval_string]

  let compl := ((eval (χ A) (decodeCode i) k))
  -- simp [show ((eval (χ A) (decodeCode i) k)) = compl from rfl] at a1
  let usecomp := (use (χ A) (decodeCode i) k)
  have a2 := e2u a1
  have : usecomp.Dom := by exact a2
  let usecn := usecomp.get a2

  have a4 := a2
  unfold A at a4
  unfold χ at a4
  simp at a4
  
  -- use reverse of eval_clamped_prop'' to rephrase the eval_clamped in the goal to just eval.
  -- then, use the extension that will get the oracle string to As (use).
  -- the inequality will be satisfies as the list as size greater than use.
  have := eval_clamped_prop''_rev (a1) (Nat.le_refl ((usecomp).get (e2u a1)))
  have a3 : (eval_clamped (χ A) (usecn) (decodeCode i) k).Dom := by exact Part.eq_some_imp_dom this
  unfold A at this
  unfold χ at this
  simp at this
  have Aprw : n2l Aₚ = As (2*i+1) := rfl
  rw [Aprw]
  if h0:2*i+1≤usecn then
    -- we want to make (As (2 * i + 1) ++ n2l (x + 1)) equal to (As (usecn + 1))
    rcases @Asexext (2*i+1) (usecn+1) (Nat.add_lt_add_right h0 1) with ⟨x,hx⟩
    use x
    rw [hx]
    
    have mainrw : (use (χ A) (decodeCode i) k) = (use (fun e ↦ b2n (n2b ((As (usecn + 1)).getD e 999))) (decodeCode i) k) := by
      refine use_principle_use a1 ?_
      intro i2 hi2
      unfold χ
      unfold A
      simp
      have hi3 : i2 < (As (usecn + 1)).length := calc
        i2 < usecn  := hi2
        usecn <  (As (usecn + 1)).length := AsSize
      have := @Agetsextended5 i2 (usecn+1) (i2 + 1) 999 hi3 (AsSize)
      rw [this]
      simp only [b2n, ite_eq_ite]
    apply eval_clamped_prop''_rev2.mp
    simp only [←mainrw]
    exact Nat.le_of_succ_le (@AsSize usecn)
    simp only [←mainrw]
    exact a2
  else
  simp at h0
  use 0
  
  -- have a7 := (@eval_clamped_prop''_rev2 (χ A) i k a2 usecn).mpr a3
  have a6 : usecn < (As (2 * i + 1)).length := calc
    usecn < 2 * i + 1 := h0
    _     ≤ (As (2 * i + 1)).length := AsSize
  have a5 : usecn ≤ (As (2 * i + 1) ++ n2l (0 + 1)).length := calc
    usecn ≤ 2 * i + 1 := Nat.le_of_succ_le h0
    _     ≤ (As (2 * i + 1)).length := AsSize
    _     ≤ (As (2 * i + 1) ++ n2l (0 + 1)).length := by
      simp only [zero_add, List.length_append, le_add_iff_nonneg_right, zero_le]
    
  have mainrw : (use (χ A) (decodeCode i) k) = (use (fun e ↦ b2n (n2b ((As (2 * i + 1) ++ n2l (0 + 1)).getD e 999))) (decodeCode i) k):= by
    refine use_principle_use a1 ?_
    intro i2
    intro hi2
    have hi3 : i2 < (As (2 * i + 1)).length := by exact Nat.lt_trans hi2 a6
    unfold χ
    unfold A
    simp
    have : (As (2 * i + 1) ++ [0])[i2]? = (As (2 * i + 1))[i2]? := by
      simp [hi3]
      grind
    rw [this]
    have := @Agetsextended5 i2 (2*i+1) (i2 + 1) 999 (hi3) (AsSize)
    rw [this]
    
    -- have : (n2b ((As (2 * i + 1) ++ [0])[i2]?.getD 999)) = n2b ((As (i2 + 1))[i2]'AsSize) := by

    --   sorry
    -- rw [this]
    simp only [b2n, ite_eq_ite]
  apply eval_clamped_prop''_rev2.mp
  simp only [←mainrw]
  exact a5
  simp only [←mainrw]
  exact a2

theorem Aextends' : ¬(eval_string (As (2*i)) i k).Dom → ¬(evalSet A i k).Dom := by
  unfold A

  simp
  unfold χ
  simp
  unfold eval_string
  simp
  intro h
  rcases eval_clamped_prop'' h with ⟨h0,h1⟩
  -- apply Part.eq_some_iff.mp
  have h2 := Part.eq_some_iff.mpr h0
  clear h0
  rw [←h2]
  apply Eq.symm
  apply up_to_use
  rotate_left
  exact Part.eq_some_imp_dom h2

  suffices ∀ i_1 < (As (2 * i)).length,
  b2n (n2b ((As (2 * i))[i_1]?.getD 999)) = if n2b ((As (i_1 + 1))[i_1]'AsSize) = true then 1 else 0
    from by
    intro h3 h4
    have h5 := this h3 (Nat.le_trans h4 h1)
    simp only [h5, ite_eq_ite]

  intro ii hii
  have asz := @AsSize ii
  have : ((As (2 * i))[ii]?.getD 999) = (As (ii + 1))[ii] := by
    have : (As (2 * i))[ii]?.getD 999 = (As (2 * i))[ii] := by simp_all only [getElem?_pos, Option.getD_some]
    rw [this]
    exact Agetsextended4 hii asz
  rw [this]
  rfl
  sorry
-- theorem Aextends'' : (eval_string (KP54 (2*(i+1))).l i) (k)=Part.some y ↔  evalSet A i (k)=Part.some y := by sorry
-- theorem Aextends'''_aux (h:( evalSet A i k).Dom): (eval_string (As (2*(i+1))) i k).Dom := by sorry
-- theorem Aextends''' {i:ℕ} (h:(evalSet A i k).Dom): evalSet A i k=eval_string (As (2*i)) i k:= by sorry
theorem Aextends''' {i:ℕ} (h:(evalSet A i k).Dom): evalSet A i k=eval_string (As (2*(i+1))) i k:= by sorry
-- theorem Aextends'''' {i:ℕ} (h:(evalSet A i k).Dom): evalSet A i k=eval_string (As (2*(i+1))) i k:= by sorry

-- R i is satisfied at stage 2i.
theorem Part.get_eq_some {p:Part ℕ} (h:p.Dom) : p=Part.some (p.get h) := by exact Part.dom_imp_some h
private theorem R (i:ℕ) : evalSet A i ≠ χ B := by
  apply Function.ne_iff.mpr
  have main := Rasd2 i
  extract_lets at main
  expose_names
  use k
  if h0:(evalSet A (decodeCode i) (k)).Dom then
  suffices (evalSet A (decodeCode i) k).get h0 ≠ (χ B) k from by
    simp
    contrapose this
    simp
    simp at this
    exact Part.get_eq_iff_eq_some.mpr this

  have := Aextends''' h0
  simp only [this]
  have main1 := main (this ▸ h0)
  clear main
  have rasd2aux := @Rasd2_aux i

  have : χ B k = b2n (n2b (Bs (2 * (i + 1)))[k]) := by
    unfold B
    unfold χ
    simp
    have := Bgetsextended4 (@BsSize k) (rasd2aux)
    simp [this]
    exact rfl
  exact Ne.symm (ne_of_eq_of_ne this (id (Ne.symm main1)))
  else
  aesop
private theorem S (i:ℕ) : evalSet B i ≠ χ A := by sorry

theorem ex_incomparable_sets : ∃ A B:Set ℕ, A|ᵀB := by
  use A
  use B
  constructor
  · change ¬SetTuringReducible A B
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    have contrad := S c
    exact contrad hc
  · change ¬SetTuringReducible B A
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    have contrad := R c
    exact contrad hc

end KP54

-- i want to write:
/-
ran_to_dom c = code_for
  fun y =>
  rfind_config (evaln c config=y)
-/
-- or for simple:
/-
fun x =>
  rfind_config (evaln c config=y)
-/
-- or for incomparable sets under K via finite extensions:
/-
-/
-- or for low+simple:
/-
fun s =>
  for e=0 to s:
    if <e,s> ∩ A_s = ∅:
      for x in <e,s>:
        if x≥2e ∧ ∀ i≤e, x>use(i,A_s,i,s):
          return x
  return null
-/



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
