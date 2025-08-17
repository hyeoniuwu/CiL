import Computability.Constructions.CovRec

open Nat.RecursiveIn.Code
namespace Nat.RecursiveIn.Code
/--
we define the use `max(all naturals queried to the oracle)+1`
use=0 when no queries are made.
use=none when the computation diverges.
-/
def use (O:ℕ→ℕ) (c:Code) (x:ℕ) : Part ℕ :=
match c with
| zero        => 0
| succ        => 0
| left        => 0
| right       => 0
| oracle      => x
| pair cf cg  => Nat.max <$> (use O cf x) <*> (use O cg x)
| comp cf cg  => Nat.max <$> (use O cg x) <*> (eval O cg x >>= use O cf)
| prec cf cg  =>
  let (xl, i) := Nat.unpair x
  i.rec (use O cf xl)
  fun iM1 IH => do
    let IH_N ← eval O (prec cf cg) (Nat.pair xl iM1);
    Nat.max <$> IH <*> use O cg (Nat.pair xl (Nat.pair iM1 IH_N))
| Code.rfind' cf =>
  let (xl, xr) := Nat.unpair x
  (Nat.rfind fun n => (fun x => x = 0) <$> eval O cf (Nat.pair xl (n + xr))).map (· + xr)
-- actually, maybe we dont have to define it like the above.


theorem Part.dom_imp_ex_some {x:Part ℕ} (h:x.Dom) : ∃ y, x=Part.some y := by
  have h0 := Part.dom_iff_mem.mp h
  rcases h0 with ⟨y,hy⟩
  use y
  exact Part.eq_some_iff.mpr hy
theorem Part.dom_imp_some {x:Part ℕ} (h:x.Dom) : x=Part.some (x.get h) := by
  exact Part.get_eq_iff_eq_some.mp rfl

theorem eval_pair_dom (h:(eval O (pair cf cg) x).Dom) : (eval O cf x).Dom ∧ (eval O cg x).Dom := by
  contrapose h
  push_neg at h
  simp [eval, Seq.seq]
  by_cases hh:(eval O cf x).Dom
  · exact fun a ↦ h hh
  · simp [Part.eq_none_iff'.mpr hh]
theorem eval_comp_dom_1 (h:(eval O (comp cf cg) x).Dom) : (eval O cg x).Dom := by
  contrapose h
  push_neg at h
  simp [eval]
  intro hdom
  exact fun a ↦ h hdom
theorem eval_comp_dom_2 (h1:(eval O (comp cf cg) x).Dom) (h2:(eval O cg x).Dom) : (eval O cf ((eval O cg x).get h2)).Dom := by
  contrapose h1
  simp [eval]
  intro hdom
  exact h1

theorem eval_pair_dom (h:(eval O (pair cf cg) x).Dom) : (eval O cf x).Dom ∧ (eval O cg x).Dom := by
  contrapose h
  push_neg at h
  simp [eval, Seq.seq]
  by_cases hh:(eval O cf x).Dom
  · exact fun a ↦ h hh
  · simp [Part.eq_none_iff'.mpr hh]
theorem eval_pair_dom (h:(eval O (pair cf cg) x).Dom) : (eval O cf x).Dom ∧ (eval O cg x).Dom := by
  contrapose h
  push_neg at h
  simp [eval, Seq.seq]
  by_cases hh:(eval O cf x).Dom
  · exact fun a ↦ h hh
  · simp [Part.eq_none_iff'.mpr hh]
  
theorem use_pair_dom (h:(use O (pair cf cg) x).Dom) : (use O cf x).Dom ∧ (use O cg x).Dom := by

  contrapose h
  push_neg at h

  simp [use, Seq.seq]
  exact fun a ↦ h a
theorem use_comp_dom (h:(use O (comp cf cg) x).Dom) (hh:(eval O cg x).Dom) : (use O cg x).Dom ∧ (use O cf ((eval O cg x).get hh)).Dom := by

  contrapose h
  push_neg at h

  simp [use, Seq.seq]
  exact fun a x ↦ h a

theorem use_mono_pair (hh:(use O (pair cf cg) x).Dom):
  ((use O cf x).get ((use_pair_dom hh).left) ≤ (use O (pair cf cg) x).get hh)
  ∧
  ((use O cg x).get ((use_pair_dom hh).right) ≤ (use O (pair cf cg) x).get hh)
  := by
    have h1 := Part.dom_imp_some ((use_pair_dom hh).left)
    simp only [use, Seq.seq, Part.bind]
    simp (config := { singlePass := true }) only [h1]
    simp [Part.assert]
theorem use_mono_comp (hh:(use O (comp cf cg) x).Dom):
  ((use O cg x).get ((use_pair_dom hh).right) ≤ (use O (comp cf cg) x).get hh)
  -- ∧
  -- ((use O cf x).get ((use_pair_dom hh).left) ≤ (use O (comp cf cg) x).get hh)
  := by
    have h1 := Part.dom_imp_some ((use_pair_dom hh).left)
    simp only [use, Seq.seq, Part.bind]
    simp (config := { singlePass := true }) only [h1]
    simp [Part.assert]

theorem get_use : (eval O c x).Dom → (use O c x).Dom := by
  intro h

  induction c with
  | zero => exact h
  | succ => exact h
  | left => exact h
  | right => exact h
  | oracle => exact h
  | pair cf cg hcf hcg =>
    simp [use]
    simp [Seq.seq]
    exact ⟨hcf (eval_pair_dom h).left, hcg (eval_pair_dom h).right⟩
  | comp cf cg hcf hcg =>
    simp [use]
    simp [Seq.seq]
    exact ⟨hcf (eval_pair_dom h).left, hcg (eval_pair_dom h).right⟩
  | prec cf cg hcf hcg => sorry
  | rfind' _ _ => sorry

  sorry
  -- · 
  -- sorry

#check Primrec
-- #check Partrec.rfind'_dom
theorem up_to_use (hh:(eval O₁ c x).Dom) (hO: ∀ i≤(use O₁ c x).get (get_use hh), O₁ i = O₂ i) : eval O₁ c x = eval O₂ c x := by
  -- have h:x≤use O₁ c x
  induction c with
  | zero => simp [eval]
  | succ => simp [eval]
  | left => simp [eval]
  | right => simp [eval]
  | oracle =>
    have h1:x≤(use O₁ oracle x).get (get_use hh) := by simp [use]
    simp [eval]
    exact hO x h1
  | pair cf cg hcf hcg =>
    simp only [eval]
    have h1:
    (∀ i ≤ (use O₁ cf x).get (get_use (eval_pair_dom hh).left), O₁ i = O₂ i)
    :=by
      intro xx
      intro hxx
      have hxx2 := le_trans hxx (use_mono_pair (get_use hh)).left
      exact hO xx hxx2
    have h2:
    (∀ i ≤ (use O₁ cg x).get (get_use (eval_pair_dom hh).right), O₁ i = O₂ i)
    :=by
      intro xx
      intro hxx
      have hxx2 := le_trans hxx (use_mono_pair (get_use hh)).right
      exact hO xx hxx2
    rw [hcf (eval_pair_dom hh).left h1]
    rw [hcg (eval_pair_dom hh).right h2]
  | comp cf cg hcf hcg =>
    simp only [eval]
    #check eval_comp_dom_1 hh
    #check eval_comp_dom_2 hh
    #check hcg (eval_comp_dom_1 hh)
    sorry
  | prec _ _ _ _ => sorry
  | rfind' _ _ => sorry

-- def eval_clamped (O:Set ℕ) (u:ℕ) (c:Code) : ℕ→.ℕ :=
def evaln_clamped (O:ℕ→ℕ) (use:ℕ) : ℕ→Code→ℕ→Option ℕ
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
    guard (n ≤ use)
    pure (O n)
  | k + 1, pair cf cg => fun n => do
    guard (n ≤ k)
    Nat.pair <$> evaln O (k + 1) cf n <*> evaln O (k + 1) cg n
  | k + 1, comp cf cg => fun n => do
    guard (n ≤ k)
    let x ← evaln O (k + 1) cg n
    evaln O (k + 1) cf x
  | k + 1, prec cf cg => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln O (k + 1) cf a) fun y => do
        let i ← evaln O k (prec cf cg) (Nat.pair a y)
        evaln O (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evaln O (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln O k (rfind' cf) (Nat.pair a (m + 1))
