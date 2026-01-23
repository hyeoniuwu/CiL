/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Jump
import Computability.Rin
import Computability.Constructions.Eval
import Computability.Constructions.Dovetail
import Computability.Use
import Computability.EvalString
import Mathlib.Order.Basic

/-!
# SetOracles.lean

We setup sets for use as oracles, (e.g. evaluation with sets as oracles, reduction between sets), and many basic definitions in degree theory, along with some basic results.

section basic_definitions:
  With use of the characteristic function operator `χ`, we are able to talk of sets of naturals as oracles.

  We define `TuringDegree` to be the equivalence classes of sets of naturals under Turing equivalence i.e. `SetTuringEquivalent`.

-/

open Nat
open scoped Computability
open Classical
open Computability.Code
namespace Computability

section basic_definitions
/-- χ O is the characteristic function of the set O.  -/
noncomputable def χ (O:Set ℕ) : ℕ→ℕ := λ x ↦ if x ∈ O then 1 else 0
theorem χsimp {O} : χ O = λ x ↦ if x ∈ O then 1 else 0 := by exact rfl
@[simp] abbrev SetRecursiveIn (O:Set ℕ) (f:ℕ→.ℕ) : Prop := RecursiveIn (χ O) f
@[simp] abbrev SetTuringReducible (A O:Set ℕ) : Prop := RecursiveIn (χ O) (χ A)
@[simp] abbrev SetTuringReducibleStrict (A O:Set ℕ) : Prop := RecursiveIn (χ O) (χ A) ∧ ¬ RecursiveIn (χ A) (χ O)
@[simp] abbrev SetTuringEquivalent (O A:Set ℕ) : Prop := AntisymmRel SetTuringReducible O A
noncomputable def evalSet (O:Set ℕ) : Code → ℕ→.ℕ := eval (χ O)
noncomputable def evalnSet (O:Set ℕ) := evaln (χ O)
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
end basic_definitions

-- lemmas
lemma χ_eq_0or1 : (χ O x = 0) ∨ (χ O x = 1) := by by_cases h : x ∈ O <;> simp [h, χsimp]
lemma some_comp_simp (a:Part ℕ) {f:ℕ→ℕ} {h:a.Dom}: (Part.some (f (a.get h)) = a >>= (f:ℕ→.ℕ)) := by
  simp only [bind]
  rw [Part.bind]
  exact Eq.symm (Part.assert_pos h)

namespace Code
section SetJumpTheorems
open Nat
open RecursiveIn
-- namespace Rin = RecursiveIn
alias Rin := RecursiveIn
-- #check Rin.oracle

theorem χ_leq_χSetK0 {O:Set ℕ} : Rin (χ (SetK0 O)) (χ O) := by
  /-
  We wish to show that `χ O` can be constructed with knowledge of
    χ (SetK0 O) = k = λ ⟪e,x⟫ ↦ [e:O](x)↓ then 1 else 0.

  Let [c_g:A](x) = if A(x)=0 then ↑ else 0.

  Then, note that `χ O` = `λ x ↦ k(c_g, x)`.
  -/
  let k : ℕ→ℕ := λ ex ↦ if (eval (χ O) ex.l ex.r).Dom then 1 else 0
  let g := λ x ↦ if (χ O) x = 0 then Part.none else Part.some 0
  have hg : Rin (χ O) g := Rin.ite Rin.oracle Rin.none Rin.zero
  rcases exists_code_nat.mp hg with ⟨cg, hcg⟩
  let f':ℕ→.ℕ := λ x ↦ k ⟪cg, x⟫
  have f_eq_f': (χ O) = f' := by
      funext xs
      simp only [f', k]
      simp only [PFun.coe_val, pair_l, pair_r, Part.coe_some, Part.some_inj]
      rw [hcg]
      simp only [g]
      cases Classical.em (χ O xs = 0) with
      | inl h => simp [h]
      | inr h =>
        simp only [h, ↓reduceIte, Part.some_dom]
        cases χ_eq_0or1 with
        | inl h2 => exact False.elim (h h2)
        | inr h2 => exact h2
  have f'_recIn_k : Rin k f' := by
    exact Rin.someTotal k (λ x ↦ k ⟪cg, x⟫) $ Rin.totalComp' Rin.oracle (Rin.of_primrecIn PrimrecIn.pair_proj)
  rw [f_eq_f']
  exact f'_recIn_k

theorem χSetK0_leq_K0χ {O:Set ℕ} : Rin (K0 (χ O)) (χ (SetK0 O)) := by
  -- We simply note that `χ (SetK0 O) = Nat.sg ∘ K0 (χ O)`.
  let k : ℕ→ℕ := λ ex ↦ if (eval (χ O) ex.l ex.r).Dom then 1 else 0
  have h0 : χ (SetK0 O) = k := by exact rfl
  let f := sg ∘ K0 (χ O)
  have k_eq_f : k = f := by
    funext xs
    simp [f, k]
  have rin_f : Rin (K0 (χ O)) f := by
    exact Rin.totalComp (Rin.of_primrecIn Nat.PrimrecIn.sg) Rin.oracle
  rw [h0]
  rw [k_eq_f]
  exact rin_f

theorem K0χ_leq_χSetK0 {O:Set ℕ} : Rin (χ (SetK0 O)) (K0 (χ O)) := by
  /-
  Let k(e,x) = if [e:O](x)↓ then 1 else 0.
  We wish to that with `k`, we can build `f = K0 (χ O)`, where
    f(e,x) = 0 if [e:O](x)↑ else [e:O](x)+1.

  We do this as follows:
    def f(e,x):
      if k(e,x)=0, return 0
      else return [e:O](x) + 1
  -/
  let k : ℕ→ℕ := λ ex ↦ if (eval (χ O) ex.l ex.r).Dom then 1 else 0
  have h1 (ex:ℕ) : k ex = 0 ↔ ¬(eval (χ O) ex.l ex.r).Dom := by simp [k]
  have h2 (ex:ℕ) : k ex ≠ 0 ↔ (eval (χ O) ex.l ex.r).Dom := by simp [k]

  let f := fun ex => if (k ex = 0) then Part.some 0 else (eval (χ O) ex.l ex.r) >>= (Nat.succ:ℕ→.ℕ)
  have rin_f : Rin k f := by
    exact Rin.ite Rin.oracle Rin.zero $
    Rin.comp Rin.succ (TuringReducible.trans' Rin.eval χ_leq_χSetK0)

  have h3 : (K0 (χ O) : ℕ→.ℕ) = f := by
    funext xs
    cases Classical.em (k xs = 0) with
    | inl h => simp [h, (h1 xs).mp h, f]
    | inr h =>
      simp only [f, PFun.coe_val, K0, (h2 xs).mp h, ↓reduceDIte, h, ↓reduceIte, Part.bind_eq_bind]
      apply some_comp_simp

  rw [h3]
  exact rin_f
theorem K0χ_eq_χSetK0 (O:Set ℕ) : (K0 (χ O)) ≡ᵀᶠ (χ (SetK0 O)) := ⟨K0χ_leq_χSetK0, χSetK0_leq_K0χ⟩
theorem χSetK0_eq_K0χ (O:Set ℕ) : (χ (SetK0 O)) ≡ᵀᶠ (K0 (χ O)) := (K0χ_eq_χSetK0 O).symm
-- the next two theorems are more or less equivalent to some of the above, with minor tweaks.
theorem χ_leq_χSetK (O:Set ℕ) : Rin (χ (SetK O)) (χ O) := by
  let χK : ℕ→ℕ := fun x ↦ if (eval (χ O) x x).Dom then 1 else 0
  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0
  have hg : Rin (χ O) g :=  Rin.ite Rin.oracle Rin.none Rin.zero
  rcases exists_code_nat.mp hg with ⟨cg, hcg⟩
  let f': ℕ→.ℕ := fun x => χK (c_evconst ⟪cg, x⟫)
  have f_eq_f': (χ O) = f' := by
    funext xs
    simp only [f']
    simp [χK, c_evconst_ev]

    rw [hcg]
    simp only [g]

    cases Classical.em (χ O xs = 0) with
    | inl h => simp [h]
    | inr h =>
      simp [h]
      cases χ_eq_0or1 with
      | inl h2 => exact False.elim (h h2)
      | inr h2 => exact h2

  have f'_recIn_χK : Nat.RecursiveIn (χK) f' := by
    simp only [f']
    refine Rin.someTotal (↑χK) (fun x ↦ χK (c_evconst ⟪cg, x⟫)) ?_
    refine Rin.totalComp' Rin.oracle ?_
    · apply exists_code.mpr
      use (c_ev_const.comp₂ (c_const cg) c_id)
      simp [Seq.seq, c_evconst]
      exact rfl

  rw [f_eq_f']
  exact f'_recIn_χK
theorem Kχ_leq_χSetK (O:Set ℕ) : Nat.RecursiveIn (χ (SetK O)) (K (χ O)) := by
  let k : ℕ→ℕ := fun x ↦ if (eval (χ O) (n2c x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = k := by exact rfl
  have h1 (x:ℕ) : k x = 0 ↔ ¬(eval (χ O) (n2c x) x).Dom := by simp [k]
  have h2 (x:ℕ) : k x ≠ 0 ↔ (eval (χ O) (n2c x) x).Dom := by simp [k]

  let f := fun x => if (k x = 0) then 0 else (eval (χ O) x x) >>= (Nat.succ:ℕ→.ℕ)

  have h3 : (K (χ O) : ℕ→.ℕ) = f := by
    funext xs
    cases Classical.em (k xs = 0) with
    | inl h =>
      simp [f, h, (h1 xs).mp h, K]; rfl
    | inr h =>
      simp only [χsimp, PFun.coe_val, K, Part.bind_eq_bind, h, ↓reduceIte, f];
      simp only [(h2 xs), χsimp] at h
      simp only [h]
      apply some_comp_simp

  have rin_f : Rin k f := by
    apply Rin.ite Rin.oracle Rin.zero $ Rin.comp Rin.succ ?_
    apply TuringReducible.trans' Nat.RecursiveIn.eval_K_computable (χ_leq_χSetK O)

  rw [h0]
  rw [h3]
  exact rin_f
theorem χSetK_leq_χSetK0 (O:Set ℕ) : Nat.RecursiveIn (χ (SetK0 O)) (χ (SetK O)) := by
  have main : (χ (SetK O)) = (χ (SetK0 O)) ∘ fun x => Nat.pair x x := by
    funext xs
    simp [χ, SetK, SetK0]
  rw [main]
  exact Rin.totalComp Rin.oracle (Rin.of_primrecIn (PrimrecIn.pair PrimrecIn.id PrimrecIn.id))
theorem χSetK_eq_Kχ (O:Set ℕ) : (χ (SetK O)) ≡ᵀᶠ (K (χ O)) := ⟨trans (χSetK_leq_χSetK0 O) $ trans (χSetK0_leq_K0χ) $ trans (K0_leq_K (χ O)) $ Rin.oracle , Kχ_leq_χSetK O⟩
theorem Kχ_eq_χSetK (O:Set ℕ) : (K (χ O)) ≡ᵀᶠ (χ (SetK O)) := (χSetK_eq_Kχ O).symm
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
theorem Set_lt_SetJump (O:Set ℕ) : O<ᵀO⌜ := ⟨Set_leq_SetK O, SetJump_not_leq_Set O⟩
end SetJumpTheorems

theorem reducible_iff_code {A B : Set ℕ} : A≤ᵀB ↔ ∃ c, eval (χ B) c = χ A := by
  simp [TR_Set_iff_Fn, exists_code]

section computably_enumerable
/-- `W O e` := domain of e^th oracle program -/
abbrev W (O:Set ℕ) (e : Code) := (evalSet O e).Dom
/-- `WR O e` := range of e^th oracle program -/
abbrev WR (O:Set ℕ) (e : Code) := (evalSet O e).ran
/-- `Wn O e s` := domain of e^th oracle program ran for s steps -/
abbrev Wn (O:Set ℕ) (e : Code) (s : ℕ) := { x | (evalnSet O s e x).isSome }
/-- `WRn O e s` := range of e^th oracle program ran for s steps -/
abbrev WRn (O:Set ℕ) (e : Code) (s : ℕ) := { y | ∃ x, y ∈ evalnSet O s e x }

theorem Wn_mono {O} : ∀ {k₁ k₂ c x}, k₁ ≤ k₂ → x ∈ Wn O c k₁ → x ∈ Wn O c k₂ := λ a b ↦ evaln_mono_dom a b
theorem Wn_sound {O} : ∀ {k c x}, x ∈ Wn O c k → x ∈ W O c := by
  simp [evalnSet, evalSet]
  intro _ _ _ h
  rw [evaln_sound' h]
  exact Part.dom_iff_mem.mp trivial
theorem evaln_complete_dom : (eval (χ O) c x).Dom ↔ ∃ k, (evaln (χ O) k c x).isSome := by
  constructor
  · intro h
    rcases Part.dom_iff_mem.mp h with ⟨y,hy⟩
    rcases evaln_complete.mp hy with ⟨k,hk⟩
    exact ⟨k, Option.isSome_of_mem hk⟩
  · rintro ⟨y, hy⟩
    exact en2e hy
theorem Wn_complete {O} {c x} : x ∈ W O c ↔ ∃ k, x ∈ Wn O c k := by
  simp [evalnSet, evalSet]
  exact Iff.trans (Iff.symm Part.dom_iff_mem) (@evaln_complete_dom O c x)
theorem W_le_SetK0 : ∀ c, W O c ≤ᵀ SetK0 O := by
  intro c
  apply reducible_iff_code.mpr
  use oracle.comp $ pair (c_const c) c_id
  funext x
  simp [evalSet, eval, Seq.seq, SetK0, χ]
  exact if_ctx_congr Part.dom_iff_mem (congrFun rfl) (congrFun rfl)

theorem W_le_Jump : ∀ c, W O c ≤ᵀ O⌜ :=
  λ c ↦ LE.le.trans_antisymmRel (@W_le_SetK0 O c) (SetK0_eq_Jump O)

section dom_to_ran
/-
Given a code `e`, we wish to find a code `f(e)` s.t:

dom[e] = ran[f(e)].

That is, [e](x)↓ iff ∃ y, x ∈ [f(e)](y).

we can simply define f(e) to be:
def [f(e)](y):
  run [e](y)
  return y
-/
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

  · intro h
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
    next h => exact Part.dom_iff_mem.mp h
    · simp_all only [Part.notMem_none]
end dom_to_ran

section ran_to_dom
/-
Given a code `e`, we wish to find a code `f(e)` s.t:

ran[e] = dom[f(e)].

That is, [f(e)](x)↓ iff ∃ y, x ∈ [e](y).

we can define f(e) to be:
def [f(e)](x):
  dovetail [e] to see if x is in its range.
  return anything.
-/
noncomputable def ran_to_dom := λ c:Code ↦ dovetail (c_if_eq'.comp₂ left ((c_eval₁).comp₂ (c_const c) right))
theorem ran_to_dom_ev : (eval O (ran_to_dom c) y).Dom ↔ ∃ x, y ∈ eval O c x := by
  constructor
  · intro h
    have := dovetail_ev_0 h
    let dvt := ((eval O (c_if_eq'.comp₂ left ((c_eval₁).comp₂ (c_const c) right)).dovetail y).get h)
    rw [show ((eval O (c_if_eq'.comp₂ left ((c_eval₁).comp₂ (c_const c) right)).dovetail y).get h) = dvt from rfl] at this
    simp at this
    simp [eval] at this
    simp [Seq.seq] at this
    have s1 : ((eval₁ O (Nat.pair c dvt))).Dom := by
      contrapose this
      simp [Part.eq_none_iff'.mpr this]
    simp [Part.Dom.bind s1] at this
    simp [eval₁] at this s1
    use dvt
    exact (@Part.get_eq_iff_mem ℕ (eval O c dvt) y s1).mp this.symm
  · rintro ⟨h1,h2⟩
    apply dovetail_ev_2.mpr
    use h1
    simp [eval, Seq.seq, eval₁, Part.bind_of_mem h2]

theorem ran_to_dom_prop : (WR O e) = (W O (ran_to_dom e)) := by
  ext xs
  constructor
  · intro h
    rcases h with ⟨y,hy⟩
    exact ran_to_dom_ev.mpr (Exists.intro y hy)
  · intro h
    simp at h
    rcases h with ⟨y,hy⟩
    exact ran_to_dom_ev.mp (Part.mem_imp_dom hy)
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
  · rw [← codes_aux_aux_0 hx]; simp
    ac_nf
    simp [even_odd_1]
  · rw [← codes_aux_aux_1 hx]; simp
    ac_nf
    simp [even_odd_2]

end join

theorem empty_le : ∀ A : Set ℕ, ∅ ≤ᵀ A := by
  intro A
  apply reducible_iff_code.mpr
  use zero
  unfold χ; simp [eval]
  rfl

theorem evalnSet_mono_dom : ∀ {k₁ k₂ : ℕ} {c n}, k₁ ≤ k₂ → (evalnSet O k₁ c n).isSome → (evalnSet O k₂ c n).isSome := by
  exact fun {k₁ k₂} {c} {n} a a_1 ↦ evaln_mono_dom a a_1

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
    use ran_to_dom c
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


end computably_enumerable
