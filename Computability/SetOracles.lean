import Computability.Jump
import Computability.Constructions.Eval
import Computability.Constructions.Dovetail
import Computability.Use
import Computability.EvalString
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
noncomputable def eval (O:Set ℕ) : Nat.RecursiveIn.Code → ℕ→.ℕ := Nat.RecursiveIn.Code.eval (χ O)
@[simp] noncomputable def evalSet₁ (O:Set ℕ) : ℕ→.ℕ := eval₁ (χ O)
@[simp] noncomputable def evalnSet₁ (O:Set ℕ) : ℕ→ℕ := evaln₁ (χ O)
theorem prim_evalnSet₁:Nat.PrimrecIn (χ O) (evalnSet₁ O) := by simp only [evalnSet₁]; exact prim_evaln₁
def SetK0 (A:Set ℕ) := {ex:ℕ | (eval A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (eval A x x).Dom}
abbrev SetJump := SetK
def jumpn : ℕ → Set ℕ → Set ℕ
| 0 => id
| i+1 => SetJump ∘ jumpn i

-- from TuringDegree.lean
protected theorem SetTuringReducible.refl (A:Set ℕ) : SetTuringReducible A A := by exact Nat.RecursiveIn.oracle
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
@[reducible,simp] def SetTuringDegreeLE (A B : Set ℕ) : Prop := TuringDegree.PO.le ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeLT (A B : Set ℕ) : Prop := TuringDegree.PO.lt ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeEQ (A B : Set ℕ) : Prop := AntisymmRel TuringDegree.PO.le ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeIN (A B : Set ℕ) : Prop := (¬TuringDegree.PO.le ⟦A⟧ ⟦B⟧)∧(¬TuringDegree.PO.le ⟦B⟧ ⟦A⟧)
@[reducible,simp] scoped[Computability] infix:50 "≤ᵀ" => SetTuringDegreeLE
@[reducible,simp] scoped[Computability] infix:50 "<ᵀ" => SetTuringDegreeLT
@[reducible,simp] scoped[Computability] infix:50 "≡ᵀ" => SetTuringDegreeEQ
@[reducible,simp] scoped[Computability] infix:50 "|ᵀ" => SetTuringDegreeIN

section evalSettheorems
theorem exists_code_for_evalSet (O:Set ℕ) (f:ℕ→.ℕ) : SetRecursiveIn O f ↔ ∃ c:Nat.RecursiveIn.Code, eval O c = f := by exact exists_code
private theorem exists_code_for_evalSet₁ {O:Set ℕ} : ∃ c:Nat.RecursiveIn.Code, eval O c = evalSet₁ O := by apply ((exists_code_for_evalSet O (evalSet₁ O)).mp) rec_eval₁
noncomputable def c_evalSet₁ (O:Set ℕ) := choose (@exists_code_for_evalSet₁ O)
@[simp] theorem c_evalSet₁_ev : eval O (c_evalSet₁ O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁
@[simp] theorem c_evalSet₁_ev2 : eval (χ O) (c_evalSet₁ O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁

private theorem exists_code_for_evalnSet₁ {O:Set ℕ} : ∃ c:Nat.RecursiveIn.Code, eval O c = evalnSet₁ O := by apply ((exists_code_for_evalSet O (evalnSet₁ O)).mp) (Nat.RecursiveIn.of_primrecIn prim_evaln₁)
private theorem exists_prim_code_for_evalnSet₁ : ∃ c, c.code_prim ∧ evalnSet₁ O = eval_prim (χ O) c := by exact code_prim_of_primrecIn prim_evalnSet₁
noncomputable def c_evalnSet₁ (O:Set ℕ) := choose (@exists_prim_code_for_evalnSet₁ O)
@[simp] theorem c_evalnSet₁_evp : eval_prim (χ O) (c_evalnSet₁ O) = evalnSet₁ O := by exact (choose_spec exists_prim_code_for_evalnSet₁).right.symm
@[simp] theorem c_evalnSet₁_ev_pr : code_prim (c_evalnSet₁ O) := by exact (choose_spec exists_prim_code_for_evalnSet₁).left
@[simp] theorem c_evalnSet₁_ev2 : eval (χ O) (c_evalnSet₁ O) = evalnSet₁ O := by rw [←@eval_prim_eq_eval (c_evalnSet₁ O) (χ O) c_evalnSet₁_ev_pr]; simp
@[simp] theorem c_evalnSet₁_ev : eval O (c_evalnSet₁ O) = evalnSet₁ O := by simp [_root_.eval]

private theorem exists_code_for_eval₁ {O:ℕ→ℕ} : ∃ c:Nat.RecursiveIn.Code, eval O c = eval₁ O := by apply (exists_code.mp) rec_eval₁
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
abbrev W (O:Set ℕ) (e : ℕ) := (eval O e).Dom
/-- `WR O e` := range of e^th oracle program -/
abbrev WR (O:Set ℕ) (e : ℕ) := (eval O e).ran

section dom_to_ran



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
    simp [_root_.eval] at h
    rcases h with ⟨y,hy⟩
    simp [WR, _root_.eval]
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
    simp only [Nat.RecursiveIn.Code.eval, Part.coe_some, Part.bind_eq_bind]
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
    simp [WR, _root_.eval]
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
    simp only [Nat.RecursiveIn.Code.eval, Part.coe_some, Part.bind_eq_bind]
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






section ran_to_dom
namespace Nat.RecursiveIn.Code
-- #check evaln₁

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
