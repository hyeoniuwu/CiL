import Computability.Use
open Nat.RecursiveIn.Code

namespace Nat.RecursiveIn.Code

def evaln_clamped (O:ℕ→ℕ) (u:ℕ) : ℕ→Code→ℕ→Option ℕ
| 0, _ => fun _ => Option.none
| k + 1, zero => fun n => do
  guard (n ≤ k)
  return 0
| k + 1, succ => fun n => do
  guard (n ≤ k)
  return (Nat.succ n)
| k + 1, left => fun n => do
  guard (n ≤ k)
  return n.unpair.1
| k + 1, right => fun n => do
  guard (n ≤ k)
  pure n.unpair.2
| k + 1, oracle => fun n => do
  guard (n ≤ k)
  guard (n ≤ u)
  pure (O n)
| k + 1, pair cf cg => fun n => do
  guard (n ≤ k)
  Nat.pair <$> evaln_clamped O u (k + 1) cf n <*> evaln_clamped O u (k + 1) cg n
| k + 1, comp cf cg => fun n => do
  guard (n ≤ k)
  let x ← evaln_clamped O u (k + 1) cg n
  evaln_clamped O u (k + 1) cf x
| k + 1, prec cf cg => fun n => do
  guard (n ≤ k)
  n.unpaired fun a n =>
    n.casesOn (evaln_clamped O u (k + 1) cf a) fun y => do
      let i ← evaln_clamped O u k (prec cf cg) (Nat.pair a y)
      evaln_clamped O u (k + 1) cg (Nat.pair a (Nat.pair y i))
| k + 1, rfind' cf => fun n => do
  guard (n ≤ k)
  n.unpaired fun a m => do
    let x ← evaln_clamped O u (k + 1) cf (Nat.pair a m)
    if x = 0 then
      pure m
    else
      evaln_clamped O u k (rfind' cf) (Nat.pair a (m + 1))

theorem evaln_clamped_sG1 (h:(evaln_clamped O u s c x).isSome) : s=s-1+1 := by
  have : s≠0 := by
    contrapose h
    simp only [ne_eq, Decidable.not_not] at h
    simp [h,evaln_clamped]
  exact Eq.symm (succ_pred_eq_of_ne_zero this)
theorem evaln_clamped_prop_0 (h:(evaln_clamped O u s c x).isSome): evaln_clamped O u s c x = evaln O s c x := by
  have h' := h
  rw [evaln_clamped_sG1 h] at h' ⊢
  induction c generalizing x with
  | zero => simp [evaln_clamped, evaln]
  | succ => simp [evaln_clamped, evaln]
  | left => simp [evaln_clamped, evaln]
  | right => simp [evaln_clamped, evaln]
  | oracle =>
    simp [evaln_clamped, evaln]
    have : x ≤ u := by
      contrapose h'
      simp [evaln_clamped]
      simp_all only [not_le, implies_true]
    simp [this]
  | pair cf cg hcf hcg =>
    rw [←evaln_clamped_sG1 h] at hcf hcg
    rw [evaln_clamped_sG1 h] at hcf hcg
    simp only [evaln,evaln_clamped]
    have d1 : (evaln_clamped O u (s - 1 + 1) cf x).isSome := by
      contrapose h'
      simp [evaln_clamped]
      simp at h'
      simp [h']
      simp [Seq.seq]
    rw [hcf d1]
    sorry
    sorry
  | comp cf cg hcf hcg =>
    simp only [evaln,evaln_clamped]
    sorry
  | prec cf cg hcf hcg =>
    simp only [evaln,evaln_clamped]
    sorry
  | rfind' cf hcf =>
    simp only [evaln,evaln_clamped]
    sorry


theorem evaln_clamped_prop_1_aux (h:(evaln_clamped O u s c x).isSome): (usen O c s x).isSome := by
  sorry
  -- have := eval_clamped_prop_0 h
  -- apply e2u
  -- rw [←this]
  -- exact h
  -- have := e2u (Part.eq_some_imp_dom (eval_clamped_prop' h))
-- theorem eval_clamped_prop''_aux' (h:y∈eval_clamped O u c x): (use O c x).Dom := e2u (Part.mem_imp_dom (eval_clamped_prop' h))
theorem evaln_clamped_prop_1 (h:(evaln_clamped O u s c x).isSome): (usen O c s x).get (evaln_clamped_prop_1_aux h)≤u := by
  have h' := h
  simp (config:={singlePass:=true}) [evaln_clamped_sG1 h] at h' ⊢
  induction c with
  | zero => simp [usen]
  | succ => simp [usen]
  | left => simp [usen]
  | right => simp [usen]
  | oracle =>
    simp [usen]
    simp [evaln_clamped] at h'
    sorry
  | pair cf cg hcf hcg =>
    simp (config:={singlePass:=true}) [evaln_clamped_sG1 h] at hcf hcg
    simp [usen]
    have : (evaln_clamped O u (s-1+1) cf x).isSome := by
      contrapose h'
      simp (config:={singlePass:=true}) [evaln_clamped]
      simp at h'

      simp [h']
      sorry
    have := hcf 
    sorry
    -- have d1 := Part.left_dom_of_sub_dom h
    -- have d2 := Part.right_dom_of_sub_dom h
    -- simp [Seq.seq]
    -- simp [Part.Dom.bind $ eval_clamped_prop''_aux d1]
    -- exact ⟨hcf d1, hcg d2⟩
  | comp cf cg hcf hcg => sorry
  | prec cf cg hcf hcg => sorry
  | rfind' _ _ => sorry






-- eval_clamped section


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


-- theorem eval_clamped_prop': y∈eval_clamped O u c x → y∈eval O c x := by sorry
theorem eval_clamped_prop_0 (h:(eval_clamped O u c x).Dom): eval_clamped O u c x = eval O c x := by
  -- intro h
  induction c generalizing x with
  | zero => simp_all [eval,eval_clamped]
  | succ => simp_all [eval,eval_clamped]
  | left => simp_all [eval,eval_clamped]
  | right => simp_all [eval,eval_clamped]
  | oracle =>
    simp_all [eval,eval_clamped]
    aesop? says
      split at h
      next h_1 => simp_all only [Part.some_dom]
      next h_1 => simp_all only [not_lt, Part.not_none_dom]
  | pair cf cg hcf hcg =>
    simp only [eval,eval_clamped]
    rw [hcf (Part.left_dom_of_sub_dom h)]
    rw [hcg (Part.right_dom_of_sub_dom h)]
  | comp cf cg hcf hcg =>
    simp only [eval,eval_clamped]
    have : (eval_clamped O u cg x).Dom := by exact Part.Dom.of_bind h
    rw [←hcg this]
    simp [Part.Dom.bind this]

    
    have : (eval_clamped O u cf ((eval_clamped O u cg x).get this)).Dom := by exact Part.right_dom_of_div_dom h
    rw [←hcf this]
  | prec cf cg hcf hcg =>
    simp only [eval,eval_clamped]
    simp
    have : (eval_clamped O u cf x.l).Dom := by sorry
    sorry
  | rfind' cf hcf =>
    simp only [eval,eval_clamped]
    simp
    

    sorry
theorem eval_clamped_prop''_aux (h:(eval_clamped O u c x).Dom): (use O c x).Dom := by
  have := eval_clamped_prop_0 h
  apply e2u
  rw [←this]
  exact h
theorem eval_clamped_prop_1 (h:(eval_clamped O u c x).Dom): (use O c x).get (eval_clamped_prop''_aux h)≤u := by
  induction c with
  | zero => simp [use]
  | succ => simp [use]
  | left => simp [use]
  | right => simp [use]
  | oracle =>
    simp [use]
    simp [eval_clamped] at h
    aesop? says
      split at h
      next h_1 =>
        simp_all only [Part.some_dom]
        exact h_1
      next h_1 => simp_all only [not_lt, Part.not_none_dom]
  | pair cf cg hcf hcg =>
    simp [use]
    have d1 := Part.left_dom_of_sub_dom h
    have d2 := Part.right_dom_of_sub_dom h
    simp [Seq.seq]
    simp [Part.Dom.bind $ eval_clamped_prop''_aux d1]
    exact ⟨hcf d1, hcg d2⟩
  | comp cf cg hcf hcg => sorry
  | prec cf cg hcf hcg => sorry
  | rfind' _ _ => sorry
theorem eval_clamped_prop''_rev_aux (h:(eval O c x).Dom) (h0:(use O c x).get (e2u h)≤u): (eval_clamped O u c x).Dom := by
  induction c with
  | zero => exact h
  | succ => exact h
  | left => exact h
  | right => exact h
  | oracle =>
    simp [eval_clamped]
    simp [use] at h0
    have : x < u := by exact h0
    simp [this]
  | pair cf cg hcf hcg =>
    simp [eval_clamped]
    have d1 := Part.left_dom_of_sub_dom h
    have d2 := Part.right_dom_of_sub_dom h
    simp [Seq.seq]
    constructor
    exact hcf d1 (le_of_max_le_left h0)
    exact hcg d2 (le_of_max_le_right h0)
  | comp _ _ _ _ => sorry
  | prec _ _ _ _ => sorry
  | rfind' _ _ => sorry
theorem eval_clamped_prop''_rev (h:(eval O c x).Dom) (h0:(use O c x).get (e2u h)≤u): eval_clamped O u c x=Part.some ((eval O c x).get h) := by
  sorry
open Part
theorem eval_clamped_prop''_rev2: (use O c x).get h≤u ↔ (eval_clamped O u c x).Dom :=
  ⟨
    λ h0 ↦ Part.eq_some_imp_dom $ eval_clamped_prop''_rev (u2e h) h0
    ,
    λ h0 ↦ eval_clamped_prop_1 h0
  ⟩

end Nat.RecursiveIn.Code
