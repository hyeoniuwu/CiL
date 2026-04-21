/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Basic
import Computability.Helper.Partial
import Computability.Helper.List
import Computability.Use.Completeness
import Mathlib.Tactic.Linarith

/-!
# Use.lean

In this file we specify the use function. In particular, we implement the *exact* use function,
which returns exactly the greatest natural queried during a computation (using `eval`), wrapped in
an option type. (If no naturals are queried, `Option.none` is returned.)

We first define the `usen` function, which acts like the `use` function for computations with
bounded steps (corresponding to `evaln`). As was done for `evaln` and `eval`, we prove
soundness/completeness/monotonicity of `usen` with respect to `use`, yielding a normal form theorem
analogous to that of `evaln`.

The main result is the use principle, which states that two different oracles that agree up to the
use of a computation, may be interchanged in a computation without changing its result.

For the construction of the use function given here, see Constructions/Use.lean.

## Main declarations

- `usen`: use function for computations with bounded steps.
- `use`: use function.
- `usen_mono`: theorem asserting monotonicity of `usen` w.r.t steps.
- `usen_sound`: theorem asserting soundness of `usen` w.r.t `use`.
- `usen_complete`: theorem asserting completeness of `usen` w.r.t `use`.
- `usen_princple`: the use principle, for computations with bounded steps.
- `use_principle`: the use principle.

## Structure

`usen_none_iff_evaln_none`
`use_dom_iff_eval_dom` : asserts that

## Notation/quirks

 - Where `x`, `y` are naturals, `⟪x, y⟫ = Nat.pair x y`.

## References

-/
set_option linter.style.longFile 0
open List Nat
open Oracle.Single.Code
set_option linter.style.cdot false
namespace Oracle.Single.Code


section use_principle
theorem use_eq_rfindOpt {O} (c n) : use O c n = Nat.rfindOpt fun k => usen O c k n :=
  Part.ext fun x => by
    refine usen_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply usen_mono hl

theorem evaln_pair_dom {O s cf cg x} (h : (evaln O (s + 1) (pair cf cg) x).isSome) : (evaln O (s + 1) cf x).isSome ∧ (evaln O (s + 1) cg x).isSome := by
  have := evaln_xles h
  contrapose h
  push Not at h
  simp [evaln, Seq.seq]
  simp [this]
  aesop? says
    intro a a_1
    simp_all only [Option.isSome_some, ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      forall_const]
theorem evaln_comp_dom_aux {O s cf cg x} (h : (evaln O (s + 1) (comp cf cg) x).isSome) : (evaln O (s + 1) cg x).isSome := by
  have h' :=  h
  simp [evaln] at h'
  simp [evaln_xles h] at h'
  contrapose h'
  simp at h'
  simp [h']
theorem evaln_comp_dom {O s cf cg x}
(h : (evaln O (s + 1) (comp cf cg) x).isSome)
:
(evaln O (s + 1) cg x).isSome
∧
(evaln O (s + 1) cf ((evaln O (s + 1) cg x).get (evaln_comp_dom_aux h))).isSome
:= by
  constructor
  · exact evaln_comp_dom_aux h
  · have h' := h
    simp [evaln] at h'
    contrapose h'
    simp at h'
    simp [evaln_xles h]
    intro h1 h2
    simp_all only [Option.get_some]
theorem evaln_prec_dom_aux {O s cf cg x i}
(h : (evaln O (s + 1) (prec cf cg) ⟪x, i+1⟫).isSome)
:
(evaln O s (prec cf cg) ⟪x, i⟫).isSome
:= by
  have h' := h
  simp [evaln] at h' ⊢
  simp [evaln_xles h] at h'
  contrapose h'
  simp at h'
  simp [h']
theorem evaln_prec_dom' {O s cf cg x}
(h : (evaln O (s + 1) (prec cf cg) ⟪x,0⟫).isSome)
:
(evaln O (s + 1) cf x).isSome
:= by
  have h' :=  h
  simp [evaln] at h'
  simp [evaln_xles h] at h'
  exact h'
theorem evaln_prec_dom {O s cf cg x i}
(h : (evaln O (s + 1) (prec cf cg) ⟪x, i+1⟫).isSome)
:
(evaln O (s-i) cf x).isSome ∧
(
let evaln_prev := (evaln O s (prec cf cg) ⟪x, i⟫).get (evaln_prec_dom_aux h)
(evaln O (s + 1) cg ⟪x, i, evaln_prev⟫).isSome
)
:= by
  induction i generalizing s with
  | zero =>
    have h' := h
    simp [evaln] at h' ⊢
    simp [evaln_xles h] at h'
    have := evaln_prec_dom_aux h
    have sG1 := evaln_sG1 this
    simp (config := {singlePass := true}) [sG1] at h' ⊢
    simp [evaln] at h' ⊢
    simp [evaln_xles' (this)] at h' ⊢
    simp [← sG1] at h' ⊢
    contrapose h'
    simp at h' ⊢
    intro h1 h2
    simp_all [-sG1]
  | succ iM1 ih =>
    have h' := h
    simp [evaln] at h'
    simp [evaln_xles h] at h'
    constructor
    · have aux0 := evaln_prec_dom_aux h
      have sG1 := evaln_sG1 aux0
      have aux1 := evaln_mono_dom (show s ≤ s + 1 from le_add_right s 1) aux0
      have ih1 := @ih (s-1) ?_
      rotate_left
      · rw [← sG1]
        exact aux0
      have : s - (iM1 + 1) = s - 1 - iM1 := by exact Simproc.sub_add_eq_comm s iM1 1
      rw [this]
      exact ih1.left

    · simp
      have aux0 := evaln_prec_dom_aux h
      simp [isSome.bind aux0] at h'
      exact h'
theorem usen_pair_dom {O cf cg s x} (h : (usen O (pair cf cg) (s + 1) x).isSome) : (usen O cf (s + 1) x).isSome ∧ (usen O cg (s + 1) x).isSome := by
  have := usen_xles h
  contrapose h
  push Not at h
  simp [usen]
  simp [this]
  aesop
theorem usen_comp_dom_aux {O cf cg s x} (h : (usen O (comp cf cg) (s + 1) x).isSome) : (evaln O (s + 1) cg x).isSome := by
  have hog := h
  simp [usen] at h
  simp [usen_xles hog] at h

  contrapose h
  simp at h
  simp [h]
theorem usen_comp_dom {O cf cg s x} (h : (usen O (comp cf cg) (s + 1) x).isSome) : (usen O cg (s + 1) x).isSome ∧ (usen O cf (s + 1) ((evaln O (s + 1) cg x).get (usen_comp_dom_aux h))).isSome := by
  have hog := h
  simp [usen] at h
  simp [usen_xles hog] at h

  contrapose h
  simp at h
  simp
  intro a b c d e
  simp_all only [Option.isSome_some, Option.get_some, forall_const, reduceCtorEq, not_false_eq_true]
theorem usen_prec_dom_aux {O cf cg s x i}
(h : (usen O (prec cf cg) (s + 1) ⟪x, i+1⟫).isSome)
:
(evaln O s (prec cf cg) ⟪x, i⟫).isSome
:= by
  simp [usen] at h
  contrapose h
  simp
  aesop? says
    intro a a_1 a_2 a_3 a_4 a_5
    simp_all only [Option.isSome_some, not_true_eq_false]
theorem usen_prec_dom' {O cf cg s x}
(h : (usen O (prec cf cg) (s + 1) ⟪x,0⟫).isSome)
:
(usen O cf (s + 1) x).isSome
:= by
  have h' :=  h
  simp [usen] at h'
  simp [usen_xles h] at h'
  exact h'
theorem usen_prec_dom {O cf cg s x i}
(h : (usen O (prec cf cg) (s + 1) ⟪x, i+1⟫).isSome)
:
(usen O cf (s-i) x).isSome
∧
(
let eval_prev := (evaln O s (prec cf cg) ⟪x, i⟫).get (usen_prec_dom_aux h)
(usen O cg (s + 1) ⟪x, i, eval_prev⟫).isSome)
:= by
  have h' := h
  simp [usen] at h'
  simp [usen_xles h] at h'
  simp [isSome.bind (en2un <| usen_prec_dom_aux h)] at h'
  simp [isSome.bind (usen_prec_dom_aux h)] at h'
  simp []

  induction i generalizing s with
  | zero =>
    have h' := h
    simp [usen] at h' ⊢
    simp [usen_xles h] at h'
    have eprev := usen_prec_dom_aux h
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev
    simp (config := {singlePass := true}) [sG1] at eprev
    have := evaln_prec_dom' eprev
    rw [← sG1] at this eprev

    constructor
    · exact en2un this

    simp [isSome.bind uprev] at h'
    simp [isSome.bind eprev] at h'

    contrapose h'
    simp at h'
    simp [h']

  | succ iM1 ih =>
    have h' := h
    simp [usen] at h'
    simp [usen_xles h] at h'
    have eprev := usen_prec_dom_aux h
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev
    constructor
    ·
      have ih1 := @ih (s-1) ?_ ?_
      rotate_left
      · rwa [← sG1]
      ·
        rw [sG1] at uprev
        let u := uprev
        simp [usen] at uprev
        simp [usen_xles u] at uprev
        have eprev2 := usen_prec_dom_aux u
        have uprev2 := en2un eprev2
        simp [isSome.bind uprev2] at uprev
        simp [isSome.bind eprev2] at uprev
        exact uprev
      have : s - (iM1 + 1) = s - 1 - iM1 := by exact Simproc.sub_add_eq_comm s iM1 1
      rw [this]
      exact ih1.left
    ·
      simp [isSome.bind uprev] at h'
      simp [isSome.bind eprev] at h'
      contrapose h'; simp at h'; simp [h']
theorem usen_rfind'_dom {O cf s x}
(h : (usen O (rfind' cf) (s + 1) x).isSome) :
∀ j ≤ nrfind'_obtain (un2en h),
  (usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).isSome := by
  have aux0 := (nrfind'_obtain_prop (un2en h)).right.left
  exact fun j a ↦ en2un (aux0 j a)
theorem usen_mono_pair {O cf cg s x} (hh : (usen O (pair cf cg) (s + 1) x).isSome):
  ((usen O cf (s + 1) x).get ((usen_pair_dom hh).left) ≤ (usen O (pair cf cg) (s + 1) x).get hh)
  ∧
  ((usen O cg (s + 1) x).get ((usen_pair_dom hh).right) ≤ (usen O (pair cf cg) (s + 1) x).get hh)
 := by
    simp only [usen]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.get_bind, Option.get_some, le_sup_left,
      le_sup_right, and_self]
theorem usen_mono_comp {O cf cg s x} (hh : (usen O (comp cf cg) (s + 1) x).isSome):
  ((usen O cg (s + 1) x).get ((usen_comp_dom hh).left) ≤ (usen O (comp cf cg) (s + 1) x).get hh)
  ∧
  ((usen O cf (s + 1) ((evaln O (s + 1) cg x).get (usen_comp_dom_aux hh))).get ((usen_comp_dom hh).right) ≤ (usen O (comp cf cg) (s + 1) x).get hh)
 := by
    simp [usen]
theorem usen_mono_prec' {O cf cg s x} (hh : (usen O (prec cf cg) (s + 1) ⟪x,0⟫).isSome):
((usen O cf (s + 1) x).get (usen_prec_dom' hh) ≤ (usen O (prec cf cg) (s + 1) ⟪x,0⟫).get hh)
:= by
  simp [usen]
theorem usen_mono_prec_1 {O cf cg s x i} (hh : (usen O (prec cf cg) (s + 1) ⟪x, i+1⟫).isSome):
(usen O (prec cf cg) (s) ⟪x, i⟫).get (en2un <| usen_prec_dom_aux hh) ≤ (usen O (prec cf cg) (s + 1) ⟪x, i+1⟫).get hh
 := by
    simp [usen.eq_9]
-- todo: simplify below proof
theorem usen_mono_prec {O cf cg s x i} (hh : (usen O (prec cf cg) (s + 1) ⟪x, i+1⟫).isSome):
((usen O cf (s-i) x).get ((usen_prec_dom hh).left) ≤ (usen O (prec cf cg) (s + 1) ⟪x, i+1⟫).get hh)
∧
let eval_prev := (evaln O s (prec cf cg) ⟪x, i⟫).get (usen_prec_dom_aux hh)
(
(usen O cg (s + 1) ⟪x, i, eval_prev⟫).get ((usen_prec_dom hh).right) ≤ (usen O (prec cf cg) (s + 1) ⟪x, i+1⟫).get hh
)
 := by
  induction i generalizing s with
  | zero =>
    simp only [usen]
    simp

    have h' := hh
    simp [usen] at h' ⊢
    simp [usen_xles hh] at h'
    have eprev := usen_prec_dom_aux hh
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev

    apply Or.inl
    simp (config := {singlePass := true}) [sG1]
    simp [usen]
  | succ n ih =>
    have h' := hh
    simp [usen] at h' ⊢
    simp [usen_xles hh] at h'
    have eprev := usen_prec_dom_aux hh
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev

    have ih1 := @ih (s-1) ?_
    rotate_left
    ·
      rw [← sG1]
      exact uprev
    simp at ih1
    have : s - (n + 1) = s-1-n := by exact Simproc.sub_add_eq_comm s n 1
    simp [this]
    simp [← sG1] at ih1
    apply Or.inl ih1.left


lemma cm_aux_0 {l'}
{l}
{head :ℕ}
{tail : List ℕ}
(h3t : ∃ l'', l'' ++ l' = l)
(hht : head :: tail = l')
:
∃ l'' : List ℕ, l'' ++ head :: tail = l
:= by
  grind
lemma cm_aux_1 {l'}
{l}
{head :ℕ}
{tail : List ℕ}
(h3t : ∃ l'', l'' ++ l' = l)
(hht : head :: tail = l')
:
∃ l'', l'' ++ tail = l
:= by
  rcases h3t with ⟨h1,h2⟩
  use h1 ++ [head]
  aesop? says
    subst h2 hht
    simp_all only [List.append_assoc, List.cons_append, List.nil_append]
theorem clause_mono_2
{base1 base2 : ℕ}
{l : List ℕ}
{f : (a : ℕ)→(l' : List ℕ)→(∃l'',l''++l'=l)→(a∈l')→ℕ}
(hf : ∀ a head tail (m : a∈tail) (l' : List ℕ) (h3t : ∃l'',l''++l'=l) (hht : head :: tail=l'), (f a (head :: tail) (cm_aux_0 h3t hht) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = f a tail (cm_aux_1 h3t hht) m)
{h : ∀ (l') (base : ℕ) (htt : ∃l'',l''++l'=l),  (forIn' (l') (base) fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l' (htt) h)))).Dom}
{h2 : base1 ≤ base2}
:
((forIn' l base1 fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base1 (⟨[],rfl⟩))
≤
(forIn' l base2 fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base2 (⟨[],rfl⟩)))
∧
(base1 ≤ (forIn' l base2 fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base2 (⟨[],rfl⟩)))
:= by
  induction l generalizing base1 base2 with
  | nil => simpa
  | cons head tail ih =>
    simp
    have httconv {l'} (htt : ∃ l'', l'' ++ l' = tail) : ∃ l'', l'' ++ l' = head :: tail := by
      rcases htt with ⟨h1,h2⟩
      exact ⟨head :: h1,Eq.symm (List.append_cancel_left (congrArg (HAppend.hAppend tail) (congrArg (List.cons head) (_root_.id (Eq.symm h2)))))⟩
    have ihmain :
    ∀ (l' : List ℕ) (base : ℕ) (htt : ∃ l'', l'' ++ l' = tail),
       (forIn' l' base fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l' (httconv htt) h)))).Dom
     := by
      intro l' base h1
      rcases h1 with ⟨l'',hl''⟩
      have : (head :: l'') ++ l' = head :: tail := by simp [hl'']
      exact h l' base  ⟨(head :: l''),this⟩
    let addendum := (f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self))
    have ihmain2 : base1.max addendum ≤ base2.max addendum := by exact sup_le_sup_right h2 addendum
    have ihmain0 : (∀ (a head : ℕ) (tail_1 : List ℕ) (m : a ∈ tail_1) (l' : List ℕ) (h3t : ∃ l'', l'' ++ l' = tail)
    (hht : head :: tail_1 = l'), f a (head :: tail_1) (httconv (cm_aux_0 h3t hht)) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail_1) a m)) = f a tail_1 (httconv (cm_aux_1 h3t hht)) m) := by
      intro a head tail_1 m l' h3t hht
      exact hf a head tail_1 m l' (httconv h3t) hht

    have ih1 := @ih (base1.max addendum) (base2.max addendum) (fun a l' h hl => f a l' (httconv h) hl) ihmain0 ihmain ihmain2

    simp [show f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self) = addendum from rfl]

    have aux (a : ℕ) (m : a∈tail): (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = (f a tail (httconv ⟨[],rfl⟩) m) :=  by
      exact hf a head tail m (head :: tail) ⟨[],rfl⟩ rfl
    have :
    (fun a m (b : ℕ) ↦ Part.some (ForInStep.yield (b.max (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))))))
    =
    fun a m (b : ℕ) ↦ Part.some (ForInStep.yield (b.max (f a tail (httconv ⟨[],rfl⟩) m)))
   := by
      funext a m b
      simp [aux a m]

    simp [this]
    exact ⟨ih1.left, le_of_max_le_left ih1.right⟩
theorem clause_mono_2_opt
{base1 base2 : ℕ}
{l : List ℕ}
{f : (a : ℕ)→(l' : List ℕ)→(∃l'',l''++l'=l)→(a∈l')→ℕ}
(hf : ∀ a head tail (m : a∈tail) (l' : List ℕ) (h3t : ∃l'',l''++l'=l) (hht : head :: tail=l'), (f a (head :: tail) (cm_aux_0 h3t hht) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = f a tail (cm_aux_1 h3t hht) m)
{h : ∀ (l') (base : ℕ) (htt : ∃l'',l''++l'=l),  (forIn' (l') (base) fun a h b ↦ some (ForInStep.yield (b.max (f a l' (htt) h)))).isSome}
{h2 : base1 ≤ base2}
:
((forIn' l base1 fun a h b ↦ some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base1 (⟨[],rfl⟩))
≤
(forIn' l base2 fun a h b ↦ some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base2 (⟨[],rfl⟩)))
∧
(base1 ≤ (forIn' l base2 fun a h b ↦ some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base2 (⟨[],rfl⟩)))
:= by
  induction l generalizing base1 base2 with
  | nil => simpa
  | cons head tail ih =>
    simp
    have httconv {l'} (htt : ∃ l'', l'' ++ l' = tail) : ∃ l'', l'' ++ l' = head :: tail := by
      rcases htt with ⟨h1,h2⟩
      exact ⟨head :: h1,Eq.symm (List.append_cancel_left (congrArg (HAppend.hAppend tail) (congrArg (List.cons head) (_root_.id (Eq.symm h2)))))⟩
    have ihmain :
    ∀ (l' : List ℕ) (base : ℕ) (htt : ∃ l'', l'' ++ l' = tail),
       (forIn' l' base fun a h b ↦ some (ForInStep.yield (b.max (f a l' (httconv htt) h)))).isSome
     := by
      intro l' base h1
      rcases h1 with ⟨l'',hl''⟩
      have : (head :: l'') ++ l' = head :: tail := by simp [hl'']
      exact h l' base  ⟨(head :: l''),this⟩
    let addendum := (f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self))
    have ihmain2 : base1.max addendum ≤ base2.max addendum := by exact sup_le_sup_right h2 addendum
    have ihmain0 : (∀ (a head : ℕ) (tail_1 : List ℕ) (m : a ∈ tail_1) (l' : List ℕ) (h3t : ∃ l'', l'' ++ l' = tail)
    (hht : head :: tail_1 = l'), f a (head :: tail_1) (httconv (cm_aux_0 h3t hht)) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail_1) a m)) = f a tail_1 (httconv (cm_aux_1 h3t hht)) m) := by
      intro a head tail_1 m l' h3t hht
      exact hf a head tail_1 m l' (httconv h3t) hht
    have ih1 := @ih (base1.max addendum) (base2.max addendum) (fun a l' h hl => f a l' (httconv h) hl) ihmain0 ihmain ihmain2

    simp [show f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self) = addendum from rfl]

    have aux (a : ℕ) (m : a∈tail): (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = (f a tail (httconv ⟨[],rfl⟩) m) :=  by
      exact hf a head tail m (head :: tail) ⟨[],rfl⟩ rfl

    have :
    (fun a m (b : ℕ) ↦ some (ForInStep.yield (b.max (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))))))
    =
    fun a m (b : ℕ) ↦ some (ForInStep.yield (b.max (f a tail (httconv ⟨[],rfl⟩) m)))
   := by
      funext a m b
      simp [aux a m]
    simp [this]
    exact ⟨ih1.left,le_of_max_le_left ih1.right⟩


theorem le_of_le_sub {c} {a b :ℕ}(h : a ≤ b-c): a ≤ b := by
  grind


theorem usen_mono_rfind' {O cf s x j} (hh : (usen O (rfind' cf) (s + 1) x).isSome):
  ∀ hj : j ≤ nrfind'_obtain (un2en hh),
  (usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).get (usen_rfind'_dom hh j hj) ≤ (usen O (rfind' cf) (s + 1) x).get hh
 := by

  intro hjro
  have rop := nrfind'_obtain_prop (un2en hh)
  let (eq := hro) ro := nrfind'_obtain (un2en hh)
  simp [← hro] at rop hjro
  have rop1 := rop.left
  have rop2 := rop.right.left
  have rop3 := rop.right.right
  have rop4 := nrfind'_obtain_prop_4 (un2en hh)
  simp [← hro] at rop4

  have aux3 := rop2 0 (Nat.zero_le ro)
  simp only [tsub_zero, zero_add, pair_lr] at aux3

  simp [usen_rfind_prop2']
  simp only [
    show (evaln O (s + 1) (rfind' cf) x).get (un2en hh) - x.r = ro from rfl,
    forIn_eq_forIn'
    ]

  -- we simplify the function within the forIn' by noting the bind is unnecesarry; the
  -- usen term halts.
  have :
      (fun i h r ↦
      (usen O cf (s + 1-i) ⟪x.l, i+x.r⟫).bind fun use_i
      ↦ some (ForInStep.yield (r.max use_i))
     : (i : ℕ) → i ∈ (List.range (ro + 1)).reverse → ℕ → Option (ForInStep ℕ))
    = (fun i h r ↦
        some (ForInStep.yield (r.max
        ((usen O cf (s + 1-i) ⟪x.l, i+x.r⟫).get (en2un <| rop2 i (rr_mem_bound h)))))
     : (i : ℕ) → i ∈ (List.range (ro + 1)).reverse → ℕ → Option (ForInStep ℕ)) := by
        funext i h r
        simp [isSome.bind (en2un <| rop2 i (rr_mem_bound h))]
  simp [this]

  have listrw : (List.range (ro + 1)).reverse = ro :: (List.range ro).reverse := by
    simp only [reverse_eq_cons_iff, reverse_reverse]
    exact List.range_succ
  simp [listrw]

  -- show 3 things.
  -- 1. that basecase ≤ forIn l ~
  -- 2. that use @ j ≤ forin range j ~
  -- 3. that forin range j ~ ≤ forin range full.
  -- simp only [forIn_eq_forIn']
  have : (usen O cf (s + 1) x).isSome := by exact en2un aux3
  have domaux2 : (usen O cf (s + 1-ro) (Nat.pair x.l (ro + x.r))).isSome := en2un <| rop2 ro le_rfl
  have domaux3aux {a' k} (h0 : k ≤ ro) (h : a' ∈ (List.range k).reverse) : a' ∈ (List.range ro).reverse := by
    simp at h ⊢
    exact Nat.lt_of_lt_of_le h h0
    -- exact?
  have domaux3 (a' k m) (h0 : k ≤ ro) := en2un (rop2 a' (rr_mem_bound (List.forIn'_congr._proof_1 listrw a' (List.mem_cons_of_mem ro (domaux3aux h0 m)))))
  have forInDom {k :ℕ} (base : ℕ) (h : k ≤ ro):
  (forIn' (List.range k).reverse (base) fun a' m b ↦
        some (ForInStep.yield (b.max ((usen O cf (s + 1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' k m h))))).isSome := by
    induction k generalizing base with
    | zero => simp
    | succ n ih =>
      simp [rr_indt, -forIn'_eq_forIn]
      have auxdom4 : (usen O cf (s + 1-n) ⟪x.l, n+x.r⟫).isSome := by
        aesop? says
          rename_i hjro_1 this_1
          simp_all [ro]
          apply domaux3
          on_goal 2 => simp_all only [ro]
          on_goal 2 => rfl
          simp_all only [List.mem_reverse, List.mem_range]
          exact h
      have := @ih (base.max ((usen O cf (s + 1-n) ⟪x.l, n+x.r⟫).get auxdom4)) (le_of_succ_le h)
      aesop? says
        simp_all only [implies_true, not_false_eq_true, and_self,List.mem_reverse, List.mem_range, ro]

  have auxdom5 : (usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).isSome :=  by (expose_names; exact usen_rfind'_dom hh j hjro_1)
  have auxdom8 (k : ℕ) : (usen O cf (s + 1-(ro-k)) (Nat.pair x.l (ro - k + x.r))).isSome :=  usen_rfind'_dom hh (ro-k) (sub_le ro k)
  have auxdom9 (k : ℕ) :=  forInDom ((usen O cf (s + 1-(ro-k)) (Nat.pair x.l (ro - k + x.r))).get (auxdom8 k)) (sub_le ro k)
  have auxdom7 :=  forInDom ((usen O cf (s + 1-ro) (Nat.pair x.l (ro + x.r))).get domaux2) le_rfl
  have auxdom10 :=forInDom ((usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).get auxdom5) hjro
  have main2:
    (usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).get auxdom5 ≤ (forIn' (List.range j).reverse ((usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).get (auxdom5)) fun a' m b ↦ some (ForInStep.yield (b.max ((usen O cf (s + 1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' j m hjro))))).get auxdom10 :=  by
      -- wait this should be literally just an application of main1.
      let base := (usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).get auxdom5
      simp [show (usen O cf (s + 1-j) ⟪x.l, j+x.r⟫).get auxdom5 = base from rfl]
      let f (a : ℕ) (l' : List ℕ) (h2 : ∃ l'' : List ℕ, l'' ++ l' = (List.range j).reverse) (h3 : a ∈ l')
           := (usen O cf (s + 1-a) (Nat.pair x.l (a + x.r))).get (
              by
                rcases listrevlem h2 with ⟨h4,h5,h6⟩
                rw [h5] at h3
                exact domaux3 a h4 h3 (Nat.le_trans h6 hjro)
            )
      have bigaux : ∀ (l' : List ℕ) (base : ℕ) (htt : ∃ l'', l'' ++ l' = (List.range j).reverse),
      (forIn' l' base fun a h b ↦ some (ForInStep.yield (b.max (f a l' htt h)))).isSome := by
        intro l' base htt
        unfold f
        rcases listrevlem htt with ⟨h1,h2,h3⟩
        simp [h2]
        have : h1 ≤ ro := by (expose_names; exact Nat.le_trans h3 hjro_1)
        exact forInDom base this
      have := (@clause_mono_2_opt base base (List.range j).reverse f (fun a head tail m l' h3t hht ↦ rfl) bigaux (le_rfl)).right

      apply this
  -- here we are saying, starting calculations from j, we'll get smaller results bc we're not taking into account the values j~ro.

  have main3 :
    ∀k,
    (forIn' (List.range (ro-k)).reverse ((usen O cf (s + 1-(ro-k)) (Nat.pair x.l ((ro-k) + x.r))).get (auxdom8 k)) fun a' m b ↦ some (ForInStep.yield (b.max ((usen O cf (s + 1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' (ro-k) m (sub_le ro k)))))).get (auxdom9 k)
    ≤
    (forIn' (List.range ro).reverse ((usen O cf (s + 1-ro) (Nat.pair x.l (ro + x.r))).get domaux2) fun a' m b ↦ some (ForInStep.yield (b.max ((usen O cf (s + 1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' ro m (le_rfl)))))).get auxdom7
   := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
        -- do cases on if ro-n ≤ 0
        cases Nat.eq_zero_or_pos (ro - n) with
        | inl hh =>
          simp [show ro-(n+1)=ro-n-1 from rfl]
          have : ro-n-1=ro-n := by exact sub_one_eq_self.mpr hh
          simp [this]
          exact ih
        | inr hh =>
          -- we want to say:
          -- ih : has all calculations from 0 to ro-k
          -- want to show: all calculations from 0 to ro-k-1
          -- i need to show that lhs of goal is leq lhs of ih.
          -- for that, i need a theorem saying that in this max forin thing,
          -- if everything is the same but the basecase of L is leq R
          -- then L leq R.
          have ronrw0 : ro-(n+1)=ro-n-1 := rfl
          simp [ronrw0]
          have ronrw : ro-n = ro-n-1+1 := by exact Eq.symm (Nat.sub_add_cancel hh)
          simp (config := { singlePass := true }) [ronrw] at ih
          simp [rr_indt (ro-n-1)] at ih

          have domaux10 : (usen O cf (s + 1-(ro - n - 1 + 1)) (Nat.pair x.l (ro - n - 1 + 1 + x.r))).isSome := by
            rw [← ronrw]
            exact auxdom8 n
          have domaux11 : (usen O cf (s + 1-(ro - n - 1)) (Nat.pair x.l (ro - n - 1 + x.r))).isSome := by
            rw [← ronrw0]
            exact auxdom8 (n + 1)
          let base2 := (((usen O cf (s + 1-(ro - n - 1 + 1)) (Nat.pair x.l (ro - n - 1 + 1 + x.r))).get domaux10).max
          ((usen O cf (s + 1-(ro - n - 1 )) (Nat.pair x.l (ro - n - 1 + x.r))).get domaux11))
          let base1 := (usen O cf (s + 1-(ro - n - 1 )) (Nat.pair x.l (ro - n - 1 + x.r))).get domaux11
          have base1_le_base2 : base1 ≤ base2 := by
            exact Nat.le_max_right ((usen O cf (s + 1-(ro - n - 1 + 1)) (Nat.pair x.l (ro - n - 1 + 1 + x.r))).get domaux10) base1
          let f (a : ℕ) (l' : List ℕ) (h2 : ∃ l'' : List ℕ, l'' ++ l' = (List.range (ro - n - 1)).reverse) (h3 : a ∈ l')
           := (usen O cf (s + 1-a) (Nat.pair x.l (a + x.r))).get (
              by
                exact domaux3 a (ro - (n + 1)) (List.forIn'_congr._proof_1 (congrArg (fun x ↦ (List.range x).reverse) ronrw0) a (by
                  simp; exact listrevlem2 h2 h3
                  )) (sub_le ro (n + 1))
            )

          let aux12 : ∀ (l' : List ℕ) (base : ℕ) (htt : ∃ l'', l'' ++ l' = (List.range (ro - n - 1)).reverse),
        (forIn' l' base fun a h b ↦ some (ForInStep.yield (b.max (f a l' htt h)))).isSome := by
            intro l' base htt
            unfold f
            rcases listrevlem htt with ⟨h1,h2,h3⟩
            simp [h2]
            have : h1 ≤ ro := by exact le_of_le_sub (le_of_le_sub h3)
            exact forInDom base this
          -- let f (a : ℕ) (l : List ℕ) (h : a ∈ l) :ℕ := usen O cf (s + 1-) (Nat.pair x.l (a + x.r))
          have mainclause := @clause_mono_2_opt base1 base2 (List.range (ro - n - 1)).reverse f (fun a head tail m l' h3t hht ↦ rfl) aux12 base1_le_base2
          -- have := Nat.le_trans mainclause.left ih
          have : s-(ro - n - 1 ) =  s + 1-(ro - n - 1 + 1) :=  by grind
          simp (config := {singlePass := true}) [this] at ih
          exact Nat.le_trans mainclause.left ih

  have :=(main3 (ro-j))
  have aux92: ro-(ro-j)=j :=  by (expose_names; exact Nat.sub_sub_self hjro_1)
  simp [aux92] at this
  apply le_trans main2 this

def usen_principle.induction
  {motive : Code → ℕ → ℕ → Prop}
  (hzero : ∀ x s, motive .zero x s)
  (hsucc : ∀ x s, motive .succ x s)
  (hleft : ∀ x s, motive .left x s)
  (hright : ∀ x s, motive .right x s)
  (horacle : ∀ x s, motive .oracle x s)
  (hpair : ∀ cf cg s x,
    (motive cf s x) →
    (motive cg s x) →
    motive (.pair cf cg) s x)
  (hcomp : ∀ cf cg x s,
    (motive cg s x) →
    (∀ x', motive cf s x') →
    motive (.comp cf cg) s x)
  (hprec : ∀ cf cg s,
    (∀ x, motive cf s x) →
    (∀ x, motive cg s x) →
    (∀ x, ( ∀ s' ≤ s, ∀ x' < x, motive (.prec cf cg) s' x') → motive (.prec cf cg) s x))
  (hrfind' : ∀ cf s x,
    (∀ x' s', motive cf s' x') →
    motive (.rfind' cf) s x)
 : ∀ c s x, motive c s x := by
    intro c
    induction c with
    | zero => exact fun x => hzero x
    | succ => exact fun x => hsucc x
    | left => exact fun x => hleft x
    | right => exact fun x => hright x
    | oracle => exact fun x => horacle x
    | pair cf cg ihcf ihcg => exact fun s x ↦ hpair cf cg s x (ihcf s x) (ihcg s x)
    | comp cf cg ihcf ihcg => exact fun s x ↦ hcomp cf cg x s (ihcg s x) (ihcf s)
    | prec cf cg ihcf ihcg  =>
  intro s x
  apply @Nat.strongRecOn (fun x' => ∀ s, motive (.prec cf cg) s x') x
    (fun x' ih_x' =>
      fun s =>
        hprec cf cg s (ihcf s) (ihcg s) x' (fun s' hle x'' hx'' => ih_x' x'' hx'' s'))
    | rfind' cf ihcf => exact fun s x ↦ hrfind' cf s x fun x' s' ↦ ihcf s' x'

/--
At a high level, this is an induction proof; we use the inductive hypothesis on subterms obtained from unfolding evaln and usen
to show that those subterms are equal, and thus, that the original expressions are equivalent.

A lot of the complexity comes from the "mono" and "dom" theorems used, which assert:
  "dom" theorems assert that if e.g. c1.prec c2 halts, then the subexpressions c1 and c2 halt
  "mono" theorems assert that the use of the sub-computations (e.g. use of c1 and c2) are
    less than the use of the main computation (e.g c1.prec c2.)

  These two theorems are required to use the inductive hypotheses.

  The "mono" and "dom" theorems are especially complex for the rfind' case.
-/
theorem usen_principle {O₁ O₂} {s c x}
  (hh : (evaln O₁ s c x).isSome)
  (hO : ∀ i<(usen O₁ c s x).get (en2un hh), O₁ i = O₂ i) :
  evaln O₁ s c x = evaln O₂ s c x ∧ usen O₁ c s x = usen O₂ c s x
:= by
  have sG1 := evaln_sG1 hh
  have xles : x ≤ s-1 := evaln_xles' hh
  rw [sG1] at ⊢ hh
  have hO: ∀ i<(usen O₁ c (s-1+1) x).get (en2un hh), O₁ i = O₂ i := by
    simp [← sG1]
    exact fun i a ↦ hO i a

  expose_names
  clear hO_1 hh_1 sG1 xles

  induction c,s,x using usen_principle.induction with
  | hzero s x => simp [evaln, usen]
  | hsucc s x => simp [evaln, usen]
  | hleft s x => simp [evaln, usen]
  | hright s x => simp [evaln, usen]
  | horacle s x =>
    simp [evaln, usen]
    simp [evaln_xles hh]
    apply hO x ?_
    · simp [usen]
  | hpair cf cg s x hcf hcg =>
    -- start with simple unfolding of terms
    simp only [evaln, usen]

    have ih_cf := hcf ?_ ?_; rotate_left
    · exact (evaln_pair_dom hh).left
    · exact fun x h ↦ hO x (le_trans h (usen_mono_pair (en2un hh)).left)
    have ih_cg := hcg ?_ ?_; rotate_left
    · exact (evaln_pair_dom hh).right
    · exact fun x h ↦ hO x (le_trans h (usen_mono_pair (en2un hh)).right)

    simp [
      ih_cf.left,
      ih_cf.right,
      ih_cg.left,
      ih_cg.right
      ]
  | hcomp cf cg x s hcg hcf =>
    -- start with simple unfolding of terms
    simp only [evaln, usen];

    -- deal with trivial case where functions diverge immediately
    if h : ¬x ≤ s-1 then simp [h,Option.bind]
    else
    simp at h; simp [h]; clear h

    have ih_cg := hcg
      (evaln_comp_dom hh).left
      fun x h ↦ hO x (le_trans h (usen_mono_comp (en2un hh)).left)

    have aux0 : (evaln O₂ (s-1+1) cg x).isSome := by
      have := evaln_comp_dom_aux hh
      rwa [ih_cg.left] at this
    have aux2 : (evaln O₁ (s-1+1) cf ((evaln O₂ (s-1+1) cg x).get aux0)).isSome := by
      have this := (evaln_comp_dom hh).right
      rwa [Option.get_inj.mpr ih_cg.left] at this
    have aux4 : (usen O₁ cf ((s-1+1)) ((evaln O₁ (s-1+1) cg x).get (evaln_comp_dom_aux hh))).get (en2un (evaln_comp_dom hh).right) = (usen O₁ cf ((s-1+1)) ((evaln O₂ (s-1+1) cg x).get aux0)).get (en2un aux2) := by
      simp_all only []

    have ih_cf := hcf ((evaln O₂ (s-1+1) cg x).get aux0) ?_ ?_; rotate_left
    · exact aux2
    · have aux := fun x h ↦ hO x (le_trans h (usen_mono_comp (en2un hh)).right)
      rwa [aux4] at aux

    rw [ih_cg.left]
    rw [ih_cg.right]
    simp [isSome.bind aux0]
    simp [ih_cf]

  | hprec cf cg s hcf hcg x ih =>
    -- start with simple unfolding of terms
    rewrite [evaln];rewrite [evaln]
    rewrite [usen]; rewrite [usen]
    rewrite [show x=Nat.pair x.l x.r from by simp] at hh ⊢ ih
    simp (config := { singlePass := true }) only [show x=Nat.pair x.l x.r from by simp] at hO
    simp? says simp only [pair_lr, unpaired, unpair1_to_l, Option.bind_eq_bind, unpair2_to_r, Option.pure_def]

    -- deal with trivial case where functions diverge immediately
    if h : ¬x ≤ s-1 then simp [h,Option.bind]
    else
    simp at h; simp [h]; clear h

    cases hxr : x.r with
    | zero =>
      simp only [rec_zero]
      rw [hxr] at hh
      simp only [hxr] at hO

      have ih_cf := hcf x.l ?_ ?_; rotate_left
      · exact evaln_prec_dom' hh
      · exact fun x h ↦ hO x (le_trans h (usen_mono_prec' (en2un hh)))

      simp [ih_cf]
    | succ xrM1 =>
      -- rewriting/simplifying
      rw [hxr] at hh ih
      simp only [hxr] at hO;
      simp only []

      -- we want to show that the subexpression involving evaln and usen are equivalent, using the inductive hypothesis.
      have aux00 := evaln_prec_dom_aux hh
      have aux02 := fun x h ↦ hO x (le_trans h (usen_mono_prec_1 (en2un hh)))
      have : s-1-1+1=s-1 := by exact Eq.symm (evaln_sG1 aux00)
      simp (config := {singlePass := true}) [← this] at aux00 aux02

      have ih_c := ih
        (s-1)
        (sub_le s 1)
        ⟪x.l, xrM1⟫
        (pair_lt_pair_right x.l (lt_add_one xrM1))
        aux00
        aux02
      clear ih

      simp [this] at ih_c aux00

      have ih_cg := hcg
        ⟪x.l, xrM1, (evaln O₁ (s-1) (cf.prec cg) ⟪x.l, xrM1⟫).get aux00⟫
        (evaln_prec_dom hh).right
        fun x h ↦ hO x (le_trans h (usen_mono_prec (en2un hh)).right)

      rw [← ih_c.left]
      rw [← ih_c.right]
      simp only [isSome.bind aux00]
      simp only [isSome.bind <| en2un aux00]
      simp [ih_cg]

  | hrfind' cf s x hcf =>
    rcases nrfind'_obtain_prop hh with ⟨nrop1,nrop2,nrop3⟩
    let (eq := hnro) nro := nrfind'_obtain hh
    simp only [← hnro, Option.mem_def] at nrop1 nrop2
    have ihAll : ∀ j ≤ nro,
      evaln O₁ (s-1+1-j) cf  ⟪x.l, j+x.r⟫ = evaln O₂ (s-1+1-j) cf ⟪x.l, j+x.r⟫
      ∧
      usen O₁ cf (s-1+1-j)  ⟪x.l, j+x.r⟫ = usen O₂ cf (s-1+1-j) ⟪x.l, j+x.r⟫
   := by
      intro j hjro
      have sG1j : s-1+1-j-1+1 = s-1+1-j := by exact (evaln_sG1 (nrop2 j hjro)).symm
      rw [← sG1j]

      have aux1 : (evaln O₁ (s-1+1-j-1+1) cf ⟪x.l, j+x.r⟫).isSome := by
        rw [sG1j]
        exact nrop2 j hjro

      apply hcf ⟪x.l, j+x.r⟫ ((s-1+1-j)) aux1 ?_
      simp [sG1j]
      exact fun x h ↦ hO x <| le_trans h (usen_mono_rfind' (en2un hh) (show j ≤ nrfind'_obtain hh from hjro))

    have aux0 : (evaln O₂ (s-1+1) cf.rfind' x).isSome := by
      apply evaln_rfind_as_eval_rfind_reverse
      simp
      use nro
      constructor
      · rw [← (ihAll nro le_rfl).left]
        exact nrop1
      intro j hjro
      have hjro : j ≤ nro := by exact le_of_succ_le hjro
      rw [← (ihAll j hjro).left]
      exact nrop2 j hjro

    have main1 : evaln O₁ (s - 1 + 1) cf.rfind' x = evaln O₂ (s - 1 + 1) cf.rfind' x := by
      suffices (evaln O₁ (s-1+1) cf.rfind' x).get hh ∈ evaln O₂ (s-1+1) cf.rfind' x
      from by
        have h2l := Option.mem_unique this (Option.get_mem aux0)
        rw [Option.eq_some_of_isSome hh]
        rw [Option.eq_some_of_isSome aux0]
        simp only [congrArg some h2l]

      have geqlem := nrfind'_geq_xr hh
      suffices (evaln O₁ (s-1+1) cf.rfind' x).get hh -x.r +x.r ∈ evaln O₂ (s-1+1) cf.rfind' x from by
        have h0 : (evaln O₁ (s-1+1) cf.rfind' x).get hh - x.r + x.r = (evaln O₁ (s-1+1) cf.rfind' x).get hh := by exact Nat.sub_add_cancel geqlem
        rwa [h0] at this

      apply (nrfind'_prop aux0).mpr
      rw [show (evaln O₁ (s-1+1) cf.rfind' x).get hh - x.r = nro from rfl]
      constructor
      · rw [← (ihAll nro le_rfl).left]
        exact nrop1
      constructor
      · intro j hjro
        rw [← (ihAll j hjro).left]
        exact nrop2 j hjro
      · intro j hjro
        rw [← (ihAll j (le_of_succ_le hjro)).left]
        exact nrop3 j hjro

    simp [main1]

    -- we rephrase the proof to be of the for loop form found in use, rather than the inductive form of usen
    suffices
    (do
  guard (x ≤ s-1);
  let guard ← evaln O₁ (s-1+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O₁ cf (s-1+1-i) ⟪x.l, i+x.r⟫)
    max := Nat.max max usen_i
  max :Option ℕ)
  =
  (do
  guard (x ≤ s-1);
  let guard ← evaln O₂ (s-1+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O₂ cf (s-1+1-i) ⟪x.l, i+x.r⟫)
    max := Nat.max max usen_i
  max :Option ℕ)
  from by
      have rw1 := @usen_rfind_prop2'' O₁ (s-1) x cf
      rw [← rw1] at this
      have rw2 := @usen_rfind_prop2'' O₂ (s-1) x cf
      rw [← rw2] at this
      exact this
    simp

    simp [evaln_xles hh]
    rw [← main1]
    simp [isSome.bind hh]

    have a2 := fun j hj ↦ (ihAll j hj).right
    have a0 : (evaln O₁ (s - 1 + 1) cf.rfind' x).get hh - x.r = nro := by exact hnro
    rw [a0]
    clear hnro nrop3 nrop1 aux0 hO a0 main1 hcf ihAll

    have a4 := a2 0 (Nat.zero_le nro)
    simp at a4

    generalize 0=b at ⊢
    revert nrop2
    revert a2
    induction nro generalizing b with
    | zero => simp [← a4]
    | succ nron ih =>
      intro a2 nrop2
      simp (config := {singlePass := true}) [rr_indt]; simp

      have := a2 (nron+1) (le_rfl)
      simp at this; simp [← this]; clear this

      have := en2un <| nrop2 (nron+1) (Nat.le_refl (nron + 1))
      simp at this
      simp [isSome.bind this]
      exact @ih
        ((b.max ((usen O₁ cf (s - 1 - nron) (Nat.pair x.l (nron + 1 + x.r))).get this)))
        (fun j hj ↦ a2 j (le_add_right_of_le hj))
        (fun j hj ↦ nrop2 j (le_add_right_of_le hj))

lemma usen_sing'' {O c s1 x h1 h2} : (usen O c s1 x).get h1 = (use O c x).get h2 := by
  rcases usen_complete.mp (Part.get_mem h2) with ⟨h3,h4⟩
  simp at h4
  have h5 : (usen O c h3 x).isSome := by exact Option.isSome_of_mem h4
  have : (use O c x).get h2 = (usen O c h3 x).get h5 := by exact Eq.symm (Option.get_of_eq_some h5 h4)
  rw [this]
  exact usen_sing'
lemma usen_sound' {O c s x} (h : (usen O c s x).isSome) : use O c x = Part.some ((usen O c s x).get h)
:= by
  have := usen_sound (Option.get_mem h)
  exact Part.eq_some_iff.mpr this

theorem use_principle {O₁ O₂} {c x}
(hh : (eval O₁ c x).Dom)
(hO : ∀ i<(use O₁ c x).get (e2u hh), O₁ i = O₂ i) :
eval O₁ c x = eval O₂ c x
∧
use O₁ c x = use O₂ c x
:= by
  rcases evaln_complete.mp (Part.get_mem hh) with ⟨s,h1⟩
  have h3 := usen_dom_iff_evaln_dom'.mpr (Option.isSome_of_mem h1)
  have userepl : (use O₁ c x).get (e2u hh) = (usen O₁ c s x).get h3 := by exact Eq.symm usen_sing''
  have h2 : (evaln O₁ s c x).isSome := by exact Option.isSome_of_mem h1
  rw [userepl] at hO
  have := @usen_principle O₁ O₂ s c x h2 hO
  have h4 := h2
  rw [this.left] at h4
  rw [evaln_sound' h2]
  rw [evaln_sound' h4]
  rw [usen_sound' (en2un h2)]
  rw [usen_sound' (en2un h4)]
  simp [this]

theorem use_principle_evaln {O₁ O₂ : ℕ → ℕ} {s c x : ℕ}
    (hh : (evaln O₁ s c x).isSome)
    (hO : ∀ i < (usen O₁ c s x).get (en2un hh), O₁ i = O₂ i) :
    evaln O₁ s c x = evaln O₂ s c x :=
  (usen_principle hh hO).left
theorem use_principle_usen {O₁ O₂ : ℕ → ℕ} {s c x : ℕ}
    (hh : (evaln O₁ s c x).isSome)
    (hO : ∀ i < (usen O₁ c s x).get (en2un hh), O₁ i = O₂ i) :
    usen O₁ c s x = usen O₂ c s x :=
  (usen_principle hh hO).right
theorem use_principle_eval {O₁ O₂ : ℕ → ℕ} {c x : ℕ}
    (hh : (eval O₁ c x).Dom)
    (hO : ∀ i < (use O₁ c x).get (e2u hh), O₁ i = O₂ i) :
    eval O₁ c x = eval O₂ c x :=
  (use_principle hh hO).left
theorem use_principle_use {O₁ O₂ : ℕ → ℕ} {c x : ℕ}
    (hh : (eval O₁ c x).Dom)
    (hO : ∀ i < (use O₁ c x).get (e2u hh), O₁ i = O₂ i) :
    use O₁ c x = use O₂ c x :=
  (use_principle hh hO).right


/-
What does rfind' do?
rfind' cf (x,i) = the smallest (i+j) s.t. `[cf](x,i+j)=0`

So to calculate `rfind' cf x`, we will need to calculate
`[cf]` on all inputs from `x` to `(x.l, rfind' cf x)`

-/
end use_principle
end Oracle.Single.Code
