/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Basic
import Computability.Helper.Partial
import Computability.Helper.List
import Computability.Use.Basic
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
set_option linter.style.whitespace false
-- set_option linter.flexible false
open List Nat
open Oracle.Single.Code
set_option linter.style.cdot false
namespace Oracle.Single.Code

section usen_mono
theorem usen_bound {O} : ∀ {k c n x}, x ∈ usen O c k n → n < k
  | 0, c, n, x, h => by simp [usen] at h
  | k + 1, c, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [usen] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le
private lemma guard_imp {k₂ n a} {k : ℕ} (h : k ≤ k₂) :
    guard (n ≤ k) = some a → (guard (n ≤ k₂) : Option Unit) = some a := by
  intro h3
  have : n ≤ k := by
    contrapose h3
    simp only [h3, guard_false, reduceCtorEq, not_false_eq_true]
  have : n ≤ k₂ := Nat.le_trans this h
  simp [this]
-- set_option linter.flexible false in
theorem usen_mono {O} : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ usen O c k₁ n → x ∈ usen O c k₂ n
| 0, k₂, c, n, x, _, h => by simp [usen] at h
| k + 1, k₂ + 1, c, n, x, hl, h => by
  have hl' := Nat.le_of_succ_le_succ hl
  have :
    ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
      k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
        x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
    simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
    exists_and_left, exists_const, and_imp]
    introv h h₁ h₂ h₃
    exact ⟨le_trans h₂ h, h₁ h₃⟩
  simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
  induction c generalizing x n <;> rw [usen] at h ⊢;
  iterate 5 exact this hl' (fun a ↦ a) h
  case pair cf cg hf hg =>
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h ⊢
    refine h.imp fun a => And.imp (guard_imp hl') ?_
    refine Exists.imp fun b => ?_
    rintro ⟨h1,h2,h3,h4⟩
    exact ⟨hf n b h1, h2, hg n h2 h3, h4⟩
  case comp cf cg hf hg =>
    simp only [bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact ⟨h1,guard_imp hl' h2,
    h3,hg n h3 h4,
    h5,evaln_mono hl h6,
    h7,hf h5 h7 h8,
    h9⟩
  case prec cf cg hf hg =>
    revert h
    simp only [bind]
    induction n.unpair.2
    · 
      simpa [Option.bind_eq_some_iff] using fun g h ↦ ⟨Nat.le_trans g hl', hf n.l x h⟩
    · simpa [Option.bind_eq_some_iff] using fun g x1 hx1 x2 hx2 x3 hx3 hmax =>
      ⟨
        Nat.le_trans g hl',
        x1,usen_mono hl' hx1,
        x2,by rw [evaln_mono hl' hx2],
        x3,
        by (expose_names; exact hg (Nat.pair n.l (Nat.pair n_1 x2)) x3 hx3), hmax
      ⟩
  case rfind' cf hf =>
    simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
      simp only [bind, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
    refine
    ⟨
      h1,guard_imp hl' h2,
      h3,hf n h3 h4,
      h5,evaln_mono hl h6,
      ?_
    ⟩
    cases h5 with
    | zero => simpa using h7
    | succ n =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at h7 ⊢
      expose_names
      simp only [Option.bind_eq_some_iff] at h7 ⊢
      rcases h7 with ⟨h8,h9,hs⟩
      exact ⟨h8,usen_mono hl' h9, hs⟩
theorem usen_mono_contra {O} :
    ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → usen O c k₂ n = Option.none → usen O c k₁ n = Option.none := by
  intro k₁ k₂ c n k1k2 opt
  contrapose opt
  have := usen_mono k1k2 (Option.get_mem (Option.isSome_iff_ne_none.mpr opt))
  refine Option.ne_none_iff_exists'.mpr ?_
  exact Exists.intro ((usen O c k₁ n).get (Option.isSome_iff_ne_none.mpr opt)) this
theorem usen_mono_dom {O} :
    ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → (usen O c k₁ n).isSome → (usen O c k₂ n).isSome := by
  intro k1 k2 c n k1k2 h1
  exact Option.isSome_of_mem (usen_mono k1k2 (Option.get_mem h1))
theorem evaln_mono_dom {O} :
    ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → (evaln O k₁ c n).isSome → (evaln O k₂ c n).isSome := by
  intro k1 k2 c n k1k2 h1
  exact Option.isSome_of_mem (evaln_mono k1k2 (Option.get_mem h1))

lemma usen_sing {O c s1 x a s2 b} (h1 : a ∈ (usen O c s1 x)) (h2 : b ∈ (usen O c s2 x)): a=b := by
  cases Classical.em (s1 ≤ s2) with
  | inl h =>
    have := usen_mono h h1
    simp_all only [Option.mem_def, Option.some.injEq]
  | inr h =>
    have := usen_mono (Nat.le_of_not_ge h) h2
    simp_all only [Option.mem_def, Option.some.injEq]
lemma usen_sing' {O c s1 x h1 s2 h2} : (usen O c s1 x).get h1 = (usen O c s2 x).get h2 :=
  usen_sing (Option.get_mem h1) (Option.get_mem h2)

lemma usen_mono' {O c s1 x s2}
    (h1 : (usen O c s1 x).isSome)
    (h2 : s1 ≤ s2) :
    (usen O c s2 x) = (usen O c s1 x) := by
  have := usen_mono h2 (Option.get_mem h1)
  simp_all only [Option.mem_def, Option.some_get]
end usen_mono

section usen_dom_iff_evaln_dom
-- TODO: replace ind with an explicit induction scheme
private def ind : ℕ → Code → ℕ
| 0, _ => 0
| _+1, zero => 0
| _+1, succ => 0
| _+1, left => 0
| _+1, right => 0
| _+1, oracle => 0
| s + 1, pair cf cg => ind (s + 1) cf + ind (s + 1) cg
| s + 1, comp cf cg => ind (s + 1) cf + ind (s + 1) cg
| s + 1, prec cf cg =>
  ind (s + 1) cf
  + ind (s + 1) cg
  + ind s (prec cf cg)
| s + 1, rfind' cf =>
  ind (s + 1) cf
  + ind s (rfind' cf)

theorem usen_none_iff_evaln_none {O c s x} :
    (usen O c s x) = Option.none ↔ (evaln O s c x) = Option.none := by
  -- using evaln.induct doesnt work, the prec inductive hypothesis
  -- w cf.prec cg is s + 1 instead of s for some reason
  induction s,c using ind.induct generalizing x with
  | case1 _ => simp [usen, evaln]
  | case2 s => simp [usen, evaln]
  | case3 s => simp [usen, evaln]
  | case4 s => simp [usen, evaln]
  | case5 s => simp [usen, evaln]
  | case6 s => simp [usen, evaln]
  | case7 s cf cg hcf hcg =>
    simp only [usen, evaln, Seq.seq]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp? [h] says
      simp only [h, guard_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_none_iff, reduceCtorEq, imp_false, Option.map_eq_map, Option.map_eq_some_iff,
        Option.map_eq_none_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro hh a ha
      have := (@hcf x).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
      exact hcg.mp (Option.eq_none_iff_forall_ne_some.mpr (hh a2 ha2))
    · intro hh a ha
      apply Option.eq_none_iff_forall_ne_some.mp
      have := (@hcf x).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mp ⟨a,ha⟩
      exact hcg.mpr (hh a2 ha2)
  | case8 s cf cg hcf hcg =>
    simp only [usen, evaln]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp? [h] says
      simp only [h, guard_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_none_iff, reduceCtorEq, imp_false]
    constructor
    · intro hh a ha
      have := (@hcg x).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
      exact hcf.mp (Option.eq_none_iff_forall_ne_some.mpr (hh a2 ha2 a ha))
    · exact fun hh a ha a3 ha3 ↦ Option.eq_none_iff_forall_ne_some.mp (hcf.mpr (hh a3 ha3))
  | case9 s cf cg hcf hcg ih =>
    simp only [usen, evaln]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp? [h] says
      simp only [h, guard_true, Option.pure_def, unpair1_to_l, Option.bind_eq_bind, unpair2_to_r,
        Option.bind_some, unpaired]
    cases hxr : x.r with
    | zero => simpa using hcf
    | succ xrM1 =>
    simp only [Option.bind_eq_none_iff, reduceCtorEq, imp_false]
    constructor
    ·
      intro hh a ha
      have := (@ih ⟪x.l, xrM1⟫).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
      have := hh a2 ha2 a ha
      exact hcg.mp (Option.eq_none_iff_forall_ne_some.mpr this)
    · exact fun hh a ha a3 ha3 ↦ Option.eq_none_iff_forall_ne_some.mp (hcg.mpr (hh a3 ha3))
  | case10 s cf hcf ih =>
    simp only [usen, evaln]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp? [h] says
      simp only [h, guard_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_none_iff, unpaired, unpair1_to_l, unpair2_to_r, pair_lr]
    constructor
    ·
      intro hh a ha
      have := (@hcf x).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
      have := hh a2 ha2 a ha
      cases a with
      | zero => simp at this
      | succ n =>
      simp?  at this ⊢ says
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Option.bind_eq_none_iff,
          reduceCtorEq, imp_false] at this ⊢
      exact ih.mp (Option.eq_none_iff_forall_ne_some.mpr this)
    · intro hh a ha a3 ha3
      have := hh a3 ha3
      cases a3 with
      | zero => simp at this
      | succ n =>
      simp?  at this ⊢ says
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Option.bind_eq_none_iff,
          reduceCtorEq, imp_false] at this ⊢
      apply Option.eq_none_iff_forall_ne_some.mp
      exact ih.mpr this
theorem usen_dom_iff_evaln_dom {O c s x} : (∃a,a ∈ (usen O c s x)) ↔ (∃b,b ∈ (evaln O s c x)) := by
  have := (@usen_none_iff_evaln_none O c s x).not
  simpa [Option.eq_none_iff_forall_ne_some] using this
theorem usen_dom_iff_evaln_dom' {O c s x} : ((usen O c s x).isSome) ↔ ((evaln O s c x).isSome) := by
  have := (@usen_none_iff_evaln_none O c s x).not
  simp only [Option.ne_none_iff_isSome, Bool.coe_iff_coe] at this
  exact Bool.coe_iff_coe.mpr this
abbrev en2un {O s c x} : (evaln O s c x).isSome → (usen O c s x).isSome :=
  usen_dom_iff_evaln_dom'.mpr
abbrev un2en {O c s x} : (usen O c s x).isSome → (evaln O s c x).isSome :=
  usen_dom_iff_evaln_dom'.mp
end usen_dom_iff_evaln_dom

section usen_sound
-- Custom induction principle used in usen_sound
def CodeNatK.induction
  {motive : ℕ → Code → Prop}
  -- base case: k = 0, c arbitrary
  (h0 : ∀ c, motive 0 c)
  -- step case: k + 1
  (hzero : ∀ k, motive (k + 1) .zero)
  (hsucc : ∀ k, motive (k + 1) .succ)
  (hleft : ∀ k, motive (k + 1) .left)
  (hright : ∀ k, motive (k + 1) .right)
  (horacle : ∀ k, motive (k + 1) .oracle)
  (hpair : ∀ k cf cg,
    motive (k + 1) cf →
    motive (k + 1) cg →
    motive (k + 1) (.pair cf cg))
  (hcomp : ∀ k cf cg,
    motive (k + 1) cf →
    motive (k + 1) cg →
    motive (k + 1) (.comp cf cg))
  (hprec : ∀ k cf cg,
    motive (k + 1) cf →
    motive (k + 1) cg →
    motive k (.prec cf cg) →
    motive (k + 1) (.prec cf cg))
  (hrfind : ∀ k cf,
    (∀ x' ≤ k + 1, motive x' cf) →
    motive (k + 1) (.rfind' cf)) : ∀ k c, motive k c := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro c
    induction c with
    | zero   =>
      cases k with
      | zero   => exact h0 .zero
      | succ k => exact hzero k
    | succ   =>
      cases k with
      | zero   => exact h0 .succ
      | succ k => exact hsucc k
    | left   =>
      cases k with
      | zero   => exact h0 .left
      | succ k => exact hleft k
    | right  =>
      cases k with
      | zero   => exact h0 .right
      | succ k => exact hright k
    | oracle =>
      cases k with
      | zero   => exact h0 .oracle
      | succ k => exact horacle k
    | pair cf cg hcf hcg =>
      cases k with
      | zero   => exact h0 (.pair cf cg)
      | succ k => exact hpair k cf cg hcf hcg
    | comp cf cg hcf hcg =>
      cases k with
      | zero   => exact h0 (.comp cf cg)
      | succ k => exact hcomp k cf cg hcf hcg
    | prec cf cg hcf hcg =>
      cases k with
      | zero   => exact h0 (.prec cf cg)
      | succ k => exact hprec k cf cg hcf hcg (ih k (Nat.lt_succ_self _) (.prec cf cg))
    | rfind' cf hcf =>
      cases k with
      | zero   => exact h0 (.rfind' cf)
      | succ k =>
        apply hrfind k cf
        intro x' hle
        cases Nat.eq_or_lt_of_le hle with
        | inl h => rw [h]; exact hcf
        | inr h => exact ih x' h cf

theorem usen_rfind_prop_aux'' {O k n} {cf : Code} :
    (usen O cf.rfind' (k + 1) n).isSome →
    (evaln O (k + 1) cf.rfind' n).isSome := by
  induction k + 1 generalizing n with
  | zero => simp [usen]
  | succ k ih =>
  intro h
  simp only [usen] at h
  simp only [evaln]
  have nlek : n ≤ k := by contrapose h; simp at h; simp [h]
  simp only [nlek] at h ⊢
  have usen_base_dom : (usen O cf (k + 1) n).isSome := by contrapose h; simp at h; simp [h]
  simp only [guard_true, Option.pure_def, Option.bind_eq_bind, Option.isSome.bind usen_base_dom,
    Option.some_get, Option.bind_some] at h
  have evaln_base_dom : (evaln O (k + 1) cf n).isSome := by contrapose h; simp at h; simp [h]
  simp only [Option.isSome.bind evaln_base_dom, guard_true, Option.pure_def, unpaired, unpair1_to_l,
    unpair2_to_r, pair_lr, Option.bind_eq_bind, Option.bind_some] at h ⊢
  cases hevaln_base : (evaln O (k + 1) cf n).get evaln_base_dom with
  | zero => simp
  | succ _ =>
    simp only [hevaln_base] at h ⊢
    have usen_indt_dom : ((usen O cf.rfind' k (Nat.pair n.l (n.r + 1)))).isSome := by
      contrapose h; simp at h; simp [h]
    exact ih usen_indt_dom
theorem usen_rfind_prop_aux' {O k n} {cf : Code} :
(usen O cf.rfind' (k + 1) n).isSome
→
(eval O cf.rfind' n).Dom
:= fun h ↦en2e (usen_rfind_prop_aux'' h)
theorem usen_rfind_prop_aux {O k n x} {cf : Code} :
    (x ∈ usen O cf.rfind' (k + 1) n) → (eval O cf.rfind' n).Dom := by
  intro h
  have : (usen O cf.rfind' (k + 1) n).isSome := Option.isSome_of_mem h
  exact usen_rfind_prop_aux' this

theorem usen_rfind_prop' {O cf k n} (hu : (usen O (rfind' cf) (k + 1) n).isSome) :
∀ j ≤ rfind'_obtain (usen_rfind_prop_aux' hu),
  (usen O cf (k + 1 - j) (Nat.pair n.l (n.r+j))).isSome
  -- and also the maximum of these is equal to the usen.
:= by
  intro j hjro
  rw (config := {occs := .pos [2]}) [add_comm]
  exact en2un ((nrfind'_obtain_prop' (un2en hu)).right.left j hjro)
theorem usen_rfind_prop {O k n x cf} (h : x ∈ usen O cf.rfind' (k + 1) n) :
  ∀ j ≤ rfind'_obtain (usen_rfind_prop_aux h),
  ∃y, y∈ (usen O cf (k + 1 - j) (Nat.pair n.l (n.r+j))) := by
  -- and also the maximum of these is equal to the usen.
  have := @usen_rfind_prop'
  simp only [Option.isSome_iff_mem, Option.mem_def, forall_exists_index] at this
  exact fun j a ↦ this x h j a
lemma nrf_aux {O cf k x} (h : (usen O (rfind' cf) k x).isSome) : k = k - 1 + 1 := by
  have : k ≠ 0 := by
    contrapose h; simp [h]
    simp [usen]
  exact (succ_pred_eq_of_ne_zero this).symm
lemma nrf {O cf k x} (h : (usen O (rfind' cf) k x).isSome) :
  x ≤ k-1 ∧ (usen O cf k x).isSome ∧ (evaln O (k) cf x).isSome := by
  have keqkM1P1 := nrf_aux h
  simp (config := {singlePass := true}) only [keqkM1P1] at h ⊢
  simp only [usen] at h
  have xlek : x ≤ k-1 := by
    contrapose h;
    simp [h, Option.bind]
  simp? [xlek]  at h ⊢ says
    simp only [xlek, guard_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      add_tsub_cancel_right, true_and] at h ⊢
  have usen_base_dom : (usen O cf (k-1+1) x).isSome := Option.isSome_of_isSome_bind h
  simp [Option.isSome.bind usen_base_dom] at h
  simp [usen_base_dom]
  have evaln_base_dom : (evaln O (k -1+1) cf x).isSome := un2en usen_base_dom
  simp [Option.isSome.bind evaln_base_dom] at h ⊢
  simp [evaln_base_dom]

/--
asserts the precise condition for when the rfind_obtain' value is 0
-/
lemma unrpeq2 {O k cf x evalnbasedom evaln_ver_dom} :
    ((evaln O (k + 1) cf x).get evalnbasedom = 0) ↔
    ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r = 0) := by
  rcases nrfind'_obtain_prop' evaln_ver_dom with ⟨nrop1, _, nrop3, _⟩
  constructor
  -- mp
  · intro h
    have h3 : rfind'_obtain (en2e evaln_ver_dom) = 0 := by
      contrapose nrop3
      simp only [Option.mem_def, not_forall, Decidable.not_not]
      simp only [exists_prop]
      use 0
      constructor
      · exact zero_lt_of_ne_zero nrop3
      rw [show 0=(some 0).get (Option.isSome_some) from rfl] at h
      simpa using Option.get_inj.mp h
    rw [evaln_eq_eval evaln_ver_dom]
    simpa [rfind'_obtain] using h3
  -- mpr
  intro h
  have h3 : rfind'_obtain (en2e evaln_ver_dom) = 0 := by
    rw [evaln_eq_eval evaln_ver_dom] at h
    simpa [rfind'_obtain] using h
  simp only [h3, tsub_zero, zero_add, pair_lr, Option.mem_def] at nrop1
  exact Option.get_of_eq_some evalnbasedom nrop1

/--
helper for usen_rfind_prop2 which simplifies the rfind case of usen.
-/
lemma unrpeq0 {O cf k x y} :
    y ∈ usen O (rfind' cf) (k + 1) x ↔ ∃
      (evalnbasedom : (evaln O (k + 1) cf x).isSome)
      (evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome),
      (if (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r=0 then usen O cf (k + 1) x
      else (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
      some (((usen O cf (k + 1) x).get (en2un evalnbasedom)).max usen_indt)) = some y := by
  constructor
  -- mp
  · intro h
    have evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome := un2en (Option.isSome_of_mem h)
    simp only [usen] at h
    simp only [evaln_xles evaln_ver_dom] at h
    have usen_base_dom : (usen O cf (k + 1) x).isSome := by contrapose h; simp at h; simp [h]
    simp? [isSome.bind usen_base_dom]  at h says
      simp only [guard_true, Option.pure_def, Option.bind_eq_bind, Option.isSome.bind usen_base_dom,
        Option.some_get, Option.bind_some, Option.mem_def] at h
    have evaln_base_dom : (evaln O (k + 1) cf x).isSome := evaln_rfind_base evaln_ver_dom
    simp only [Option.isSome.bind evaln_base_dom] at h ⊢
    simp only [add_tsub_cancel_right, evaln_base_dom, exists_true_left]
    use evaln_ver_dom
    simp_all [@unrpeq2 O k cf x evaln_base_dom evaln_ver_dom]
  -- mpr
  intro h
  rcases h with ⟨h1,h2,h3⟩
  simp at h3
  simp [usen]
  have xlek : x ≤ k := le_of_lt_succ (evaln_bound (Option.get_mem h1))
  simp [xlek]
  simp [Option.isSome.bind (en2un h1)]
  simp [Option.isSome.bind (h1)]
  simp_all [@unrpeq2 O k cf x h1 h2]

/--
helper for usen_rfind_prop2 which simplifies the rfind case of use.
-/
lemma unrpeq1 {x k O cf y} : y ∈ (do
  guard (x ≤ k);
  let guard ← evaln O (k + 1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k + 1-i) ⟪x.l, i+x.r⟫)
    max := Nat.max max usen_i
  max : Option ℕ) ↔ ∃
  (evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome),
  (forIn (List.range ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r + 1)).reverse 0
    fun i r ↦ (usen O cf (k + 1 - i) (⟪x.l, i+x.r⟫)).bind fun usen_i ↦
    some (ForInStep.yield (r.max usen_i))) =
  some y := by
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
    Option.mem_def]
  constructor
  · intro h
    have xlek : x ≤ k := by
      contrapose h;
      simp [h, Option.bind]
    simp only [xlek, guard_true, Option.pure_def, Option.bind_some] at h ⊢
    have evaln_ver_dom : (evaln O (k + 1) (rfind' cf) x).isSome := by
      contrapose h; simp at h; simp [h]
    simp [Option.isSome.bind evaln_ver_dom] at h
    use evaln_ver_dom
  intro h
  rcases h with ⟨h1,h2⟩
  have xlek : x ≤ k := by
    simp only [evaln, unpaired, unpair1_to_l, unpair2_to_r, pair_lr, Option.pure_def,
      Option.bind_eq_bind] at h1
    contrapose h1;
    simp [h1]
  simpa [xlek, Option.isSome.bind h1] using h2
/--
This is a helper lemma for `usen_rfind_prop2`.

Consider the list of numbers:
eval cf for s+1-0      steps on input ⟪x.l, x.r + 0⟫
eval cf for s+1-1      steps on input ⟪x.l, x.r + 1⟫
eval cf for s+1-2      steps on input ⟪x.l, x.r + 2⟫
...
eval cf for s+1-roM1   steps on input ⟪x.l, x.r + roM1⟫
eval cf for s+1-roM1-1 steps on input ⟪x.l, x.r + roM1 + 1⟫

We can find the maximum of all those numbers, in two different ways:
fold Nat.max over all elements of the list but the last, and provide the last in the base case
OR
fold Nat.max over all elements of the list but the first, and provide the first in the base case.

The lemma below shows that these two ways give the same number.
-/
lemma displace_loop_0 {O s cf x roM1 ro_dom}
    (a : ℕ) (h1 : (evaln O (s + 1) cf x).isSome)
    (u0 : (usen O cf (s + 1) x).isSome)
    (u1 : (usen O cf (s + 1) ⟪x.l, x.r+1⟫).isSome)
    (nrop2 : (∀ j ≤ roM1 + 1, (usen O cf (s + 1 - j) ⟪x.l, j+x.r⟫).isSome)) :
    (forIn
      (List.range (roM1 + 1)).reverse
      (a.max ((usen O cf (s + 1) x).get (en2un h1)))
      fun i r ↦
        (usen O cf (s + 1 - i) (Nat.pair x.l (i + (x.r + 1)))).bind
        fun a ↦ some (ForInStep.yield (r.max a))) =
    (forIn
      (List.range (roM1 + 1)).reverse
      (a.max ((usen O cf (s - roM1) ⟪x.l,roM1 + 1 + x.r⟫).get ro_dom))
      fun i r ↦
        (usen O cf (s + 1 - i) ⟪x.l, i+x.r⟫).bind fun usen_i ↦
        some (ForInStep.yield (r.max usen_i))) := by
  induction roM1 generalizing a with
  | zero =>
    simp? [isSome.bind u0] says
      simp only [zero_add, range_one, reverse_cons, reverse_nil, nil_append, forIn_cons, tsub_zero,
        Nat.max_assoc, Option.pure_def, forIn_nil, Option.bind_eq_bind, pair_lr, Option.isSome.bind u0,
        Option.bind_some]
    simp? [isSome.bind u1] says simp only [Option.isSome.bind u1, Option.bind_some, Option.some.injEq]
    ac_nf
    rw (config := {occs := .pos [2]}) [Nat.max_comm]
    apply congrArg
    apply congrFun
    apply congrArg
    apply usen_sing'
  | succ roM2 iihh =>
    simp (config := { singlePass := true }) only [reversed_range_indt, forIn_cons]
    simp only [reduceSubDiff, Nat.max_assoc, Option.pure_def, Option.bind_eq_bind]
    have urom : (usen O cf (s +1 - (roM2+1)) (Nat.pair x.l ((roM2+1) + 1 + x.r))).isSome := by
      have := nrop2 (roM2+1+1) (Nat.le_refl (roM2 + 1 + 1))
      simp only [reduceSubDiff] at this
      apply usen_mono_dom _ this
      exact Nat.sub_le_add_right_sub s (roM2 + 1) 1
    simp only [reduceSubDiff] at urom
    rw [add_assoc] at urom
    rw (config := {occs := .pos [3]}) [add_comm] at urom
    simp only [Option.isSome.bind urom, Option.bind_some]
    have urom2 := nrop2 (roM2+1) (le_add_right (roM2 + 1) 1)
    simp only [reduceSubDiff] at urom2
    simp only [Option.isSome.bind urom2, Option.bind_some]
    replace iihh := @iihh
      urom2
      (a.max ((usen O cf (s - roM2) (Nat.pair x.l (roM2 + 1 + (x.r + 1)))).get urom))
      (fun j hj ↦ (nrop2 j (le_add_right_of_le hj)))
    simp only [Nat.max_assoc] at iihh
    simp only [Nat.max_comm]
    rw [iihh]
    simp only [Nat.max_comm]
    have :
        ((usen O cf (s - roM2) (Nat.pair x.l (roM2 + 1 + (x.r + 1)))).get urom) =
        ((usen O cf (s - (roM2 + 1)) (Nat.pair x.l (roM2 + 1 + 1 + x.r))).get ro_dom) := by
      have : (roM2 + 1 + (x.r + 1)) = (roM2 + 1 + 1 + x.r) :=
        Eq.symm (Nat.add_right_comm (roM2 + 1) 1 x.r)
      simpa [this] using usen_sing'
    rw [this]

lemma usen_rfind_prop2_indt_helper
    (O : ℕ → ℕ) (k : ℕ) (cf : Code) (roM1 x : ℕ) (h2 : (evaln O (k + 1) cf.rfind' x).isSome = true)
    (hro : rfind'_obtain (en2e h2) = roM1 + 1)
    (evalnindtdom : (evaln O k cf.rfind' ⟪x.l,x.r + 1⟫).isSome = true) :
    rfind'_obtain (en2e (Option.isSome_of_mem
      (evaln_mono (Nat.le_add_right k 1) (Option.get_mem evalnindtdom)))) = roM1 := by
  simp only [rfind'_obtain] at hro ⊢
  have := rfind'_obtain_prop_6 (en2e h2)
  simp only [rfind'_obtain] at this
  rw [hro] at this
  replace := this 1 (le_add_left 1 roM1)
  simp only [Nat.add_comm] at this
  rw [← (Part.eq_get_iff_mem (en2e evalnindtdom)).mpr this]
  rw [← add_assoc]
  simp

lemma usen_rfind_prop2_indt_helper2
    (O : ℕ → ℕ)
    (k : ℕ)
    (cf : Code)
    (roM1 x : ℕ)
    (h1 : (evaln O (k + 1) cf x).isSome = true)
    (base : ℕ)
    (usenindtdom : (usen O cf.rfind' k ⟪x.l,x.r + 1⟫).isSome = true)
    (nrop1 : 0 ∈ evaln O (k + 1 - (roM1 + 1)) cf ⟪x.l,roM1 + 1 + x.r⟫)
    (nrop2 : ∀ j ≤ roM1 + 1, (evaln O (k + 1 - j) cf ⟪x.l,j + x.r⟫).isSome = true)
    (nrop3 : ∀ j < roM1 + 1, 0 ∉ evaln O (k + 1 - j) cf ⟪x.l,j + x.r⟫)
    (nrop6 : ∀ j ≤ roM1 + 1, roM1 + 1 + x.r ∈ evaln O (k + 1 - j) cf.rfind' ⟪x.l,j + x.r⟫)
    (aux0 : (evaln O (k + 1) cf ⟪x.l,x.r + 1⟫).isSome = true) :
    (if roM1 = 0 then
        some ((base.max ((usen O cf (k + 1) x).get (en2un h1))).max
        ((usen O cf (k + 1) ⟪x.l,x.r + 1⟫).get (en2un aux0)))
      else
        (usen O cf.rfind' k ⟪⟪x.l,x.r + 1⟫.l,⟪x.l,x.r + 1⟫.r + 1⟫).bind fun a ↦
          some
            ((base.max ((usen O cf (k + 1) x).get (en2un h1))).max
              (((usen O cf (k + 1) ⟪x.l,x.r + 1⟫).get (en2un aux0)).max a))) =
      some (base.max (((usen O cf (k + 1) x).get (en2un h1)).max
      ((usen O cf.rfind' k ⟪x.l,x.r + 1⟫).get usenindtdom))) := by
  if hroM1 : roM1=0 then
  simp? [hroM1]  at ⊢ nrop6 nrop1 says
    simp only [hroM1, zero_add, Option.mem_def, add_tsub_cancel_right,
    ↓reduceIte, Nat.max_assoc, Option.some.injEq] at ⊢ nrop6 nrop1
  have nropleft := nrop1
  rw [add_comm] at nropleft
  have :
      ((usen O cf.rfind' k ⟪x.l, x.r+1⟫).get usenindtdom) =
      ((usen O cf (k + 1) ⟪x.l, x.r+1⟫).get (en2un aux0)) := by
    have := nrop6 1 (le_rfl)
    simp at this
    have : k=k-1+1 := nrf_aux usenindtdom
    simp (config := { singlePass := true }) only [this]
    simp only [usen, pair_l, pair_r, Option.bind_eq_bind, Option.get_bind, Option.some_get]
    simpa [← this, nropleft] using usen_sing'
  rw [this]
else
  simp only [hroM1, ↓reduceIte, pair_l, pair_r, Nat.max_assoc]
  have roM1M1: roM1 = roM1-1+1 := Eq.symm (succ_pred_eq_of_ne_zero hroM1)
  simp (config := { singlePass := true }) only [roM1M1, reduceSubDiff, Option.mem_def,
    Nat.add_eq_zero_iff, not_and, add_tsub_cancel_right] at *
  have : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1 + 1))).isSome := by
    have := nrop6 (1+1) (le_add_left (1 + 1) (roM1 - 1))
    simp only [reduceSubDiff] at this
    have := Option.isSome_of_mem this
    ac_nf at this ⊢
    simp only [reduceAdd] at this ⊢
    exact usen_mono_dom (show k-1 ≤ k from sub_le k 1) (en2un this)
  simp only [Option.isSome.bind this, Option.some.injEq]
  apply congrArg
  apply congrArg
  have kkk : k=k-1+1 :=  nrf_aux usenindtdom
  simp only [congrFun (congrArg (usen O cf.rfind') kkk) ⟪x.l,x.r + 1⟫]
  have hdom : (evaln O k cf ⟪x.l, x.r+1⟫).isSome := by
    have := nrop2 1 (le_add_left 1 (roM1 - 1 + 1))
    simp at this
    rwa [add_comm]
  have r1 : (evaln O k cf ⟪x.l, x.r+1⟫).get hdom ≠ 0 := by
    have := nrop3 1 (one_lt_succ_succ (roM1 - 1))
    simp only [add_tsub_cancel_right] at this
    rw [add_comm] at this
    contrapose this
    rw [← this]
    simp
  simp only at this
  rw [add_comm] at this
  simp only [usen, pair_l, pair_r, Option.bind_eq_bind, Option.get_bind, Option.some_get]
  simpa [← kkk, r1] using congr (congr rfl usen_sing') usen_sing'

/--
rewrites the use of a rfind' in terms of a for loop,
to help relate `usen` to `use`. (as rfind' in `use` is written with a for loop.)

TODO: try to not do two inductions under mp and mpr, just do one induction
-/
theorem usen_rfind_prop2 {O k x y cf} :
  y ∈ usen O cf.rfind' (k + 1) x ↔
  y ∈ (do
    guard (x ≤ k);
    let guard ← evaln O (k + 1) (rfind' cf) x;
    let ro := guard - x.r
    let mut max := 0
    for i in List.reverse (List.range (ro+1)) do
      let usen_i ← (usen O cf (k + 1-i) ⟪x.l, i+x.r⟫)
      max := Nat.max max usen_i
    max : Option ℕ) := by
  rewrite [unrpeq0, unrpeq1]
  constructor
  · intro h
    rcases h with ⟨h1, h2,h3⟩
    have h1 : (evaln O (k + 1) cf x).isSome := (nrf (en2un h2)).right.right
    use h2
    let base' := 0
    rw [show 0=base' from rfl]
    have :
      (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (usen O cf (k + 1) x) else
        (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
          some (((usen O cf (k + 1) x).get (en2un h1)).max usen_indt)) =
      (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (some (base'.max
        ((usen O cf (k + 1) x).get (en2un h1)))) else
        (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
          some (base'.max <| ((usen O cf (k + 1) x).get (en2un h1)).max usen_indt)) := by
      simp [show base' = 0 from rfl]
    rw [this] at h3
    -- we prepare to induct on the rfind'_obtain value.
    clear this
    have rorw : rfind'_obtain (en2e h2) = (evaln O (k + 1) cf.rfind' x).get h2 - x.r := by
      simp [rfind'_obtain, evaln_eq_eval h2]
    revert h3
    revert rorw
    generalize base'=base
    clear base'
    induction (evaln O (k + 1) cf.rfind' x).get h2 - x.r generalizing base h2 x with
    | zero => simp [Option.isSome.bind <| en2un h1]
    | succ roM1 ih =>
      simp? (config := { singlePass := true }) [rr_indt] says
        simp (config := { singlePass := true }) only [Nat.add_eq_zero_iff, add_tsub_cancel_right,
          reversed_range_indt, forIn_cons]
      simp only [one_ne_zero, and_false, ↓reduceIte, reduceSubDiff, Option.pure_def,
        Option.bind_eq_bind]
      intro hro h
      have usenindtdom : (usen O cf.rfind' k ⟪x.l, x.r+1⟫).isSome := by
        contrapose h; simp at h; simp [h]
      simp only [Option.isSome.bind usenindtdom, Option.some.injEq, add_tsub_cancel_right] at h ih
      have evalnindtdom := un2en usenindtdom
      have nrfindt := nrf usenindtdom
      rcases nrfind'_obtain_prop' h2 with ⟨nrop1, nrop2, nrop3, nrop4⟩
      have nrop6 := nrfind'_obtain_prop_6' h2
      rw [hro] at nrop1 nrop2 nrop3 nrop4 nrop6
      have nrop2' : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) ⟪x.l, j+x.r⟫).isSome) :=
        fun j a ↦ en2un (nrop2 j a)
      have ro_dom : (usen O cf (k - roM1) ⟪x.l, roM1 + 1 + x.r⟫).isSome := by
        simpa using nrop2' (roM1+1) (le_rfl)
      simp only [Option.isSome.bind ro_dom, Option.bind_some]
      have aux0 : (evaln O (k + 1) cf ⟪x.l, x.r+1⟫).isSome :=
        Option.isSome_of_mem (evaln_mono (le_add_right k 1) (Option.get_mem nrfindt.right.right))
      replace ih := @ih ⟪x.l, x.r+1⟫ aux0
        (Option.isSome_of_mem (evaln_mono (le_add_right k 1) (Option.get_mem evalnindtdom)))
        aux0 (base.max ((usen O cf (k + 1) x).get (en2un h1)))
        (usen_rfind_prop2_indt_helper O k cf roM1 x h2 hro evalnindtdom)
        (by rw [← h]; exact usen_rfind_prop2_indt_helper2
              O k cf roM1 x h1 base usenindtdom nrop1 nrop2 nrop3 nrop6 aux0)
      have := @displace_loop_0 O k cf x roM1 ro_dom base h1 (en2un h1) (en2un aux0)
        (fun j a ↦ nrop2' j a)
      simp only [pair_l, pair_r] at ih
      rewrite [this] at ih
      rw [ih]
  · -- mpr
    intro h
    rcases h with ⟨h2,h3⟩
    have h1 : (evaln O (k + 1) cf x).isSome := (nrf (en2un h2)).right.right
    use h1; use h2
    let base' := 0
    rw [show 0=base' from rfl] at h3
    have :
        (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0
        then (usen O cf (k + 1) x) else
          (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
            some (((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
          =
        (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0
        then (some (base'.max ((usen O cf (k + 1) x).get (en2un h1)))) else
          (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
            some (base'.max <| ((usen O cf (k + 1) x).get (en2un h1)).max usen_indt)) := by
      simp [show base'=0 from rfl]
    rw [this]
    clear this
    have rwro : rfind'_obtain (en2e h2) = (evaln O (k + 1) cf.rfind' x).get h2 - x.r := by
      simp [rfind'_obtain, evaln_eq_eval h2]
    revert h3
    revert rwro
    generalize base' = base
    clear base'
    induction (evaln O (k + 1) cf.rfind' x).get h2 - x.r generalizing base h2 x with
    | zero => simp [Option.isSome.bind <| en2un h1]
    | succ roM1 ih =>
      intro rwro h
      simp (config := { singlePass := true }) only [reversed_range_indt, forIn_cons] at h
      simp only [reduceSubDiff, Option.pure_def, Option.bind_eq_bind] at h
      rcases nrfind'_obtain_prop' h2 with ⟨nrop1,nrop2,nrop3,nrop4⟩
      have nrop6 := nrfind'_obtain_prop_6' h2
      rw [rwro] at nrop1 nrop2 nrop3 nrop6 nrop4
      have nrop2' : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) ⟪x.l, j+x.r⟫).isSome) :=
        fun j a ↦ en2un (nrop2 j a)
      have ro_dom : (usen O cf (k - roM1) ⟪x.l,roM1 + 1 + x.r⟫).isSome := by
        have := nrop2' (roM1+1) (le_rfl)
        simpa using this
      simp only [Option.isSome.bind ro_dom, Option.bind_some] at h
      have usenindtdom : (usen O cf.rfind' k ⟪x.l, x.r+1⟫).isSome := by
        have := nrop4 1 (le_add_left 1 roM1)
        rw [add_comm]
        simp only [add_tsub_cancel_right] at this
        exact en2un this
      have evalnindtdom := un2en usenindtdom
      have aux0 : (evaln O (k + 1) cf ⟪x.l, x.r+1⟫).isSome := by
        have := nrop2 1 (le_add_left 1 roM1)
        simp only [add_tsub_cancel_right] at this
        rw [add_comm] at this
        exact evaln_mono_dom (le_add_right k 1) this
      replace ih := @ih ⟪x.l, x.r+1⟫
        (Option.isSome_of_mem (evaln_mono (le_add_right k 1) (Option.get_mem evalnindtdom)))
        aux0 (base.max ((usen O cf (k + 1) x).get (en2un h1)))
        (usen_rfind_prop2_indt_helper O k cf roM1 x h2 rwro evalnindtdom) ?_
      rotate_left
      · 
        have := @displace_loop_0 O k cf x roM1 (ro_dom) base h1
          (en2un h1) (en2un aux0) (fun j a ↦ nrop2' j a)
        simpa [this] using h
      simp only [Nat.max_assoc, add_tsub_cancel_right, pair_l, pair_r] at ih
      rw [← ih]
      have := usen_rfind_prop2_indt_helper2
        O k cf roM1 x (evaln_rfind_base h2) base usenindtdom nrop1 nrop2 nrop3 nrop6 aux0
      simp [Option.isSome.bind usenindtdom, ←this]

theorem usen_rfind_prop2' {O cf k x} (h : (usen O (rfind' cf) (k + 1) x).isSome) :
    (usen O cf.rfind' (k + 1) x).get h = (do
    guard (x ≤ k);
    let guard ← evaln O (k + 1) (rfind' cf) x;
    let ro := guard - x.r
    let mut max := 0
    for i in List.reverse (List.range (ro+1)) do
      let usen_i ← (usen O cf (k + 1-i) ⟪x.l, i+x.r⟫)
      max := Nat.max max usen_i
    max : Option ℕ).get
    (Option.isSome_of_mem (usen_rfind_prop2.mp (Option.get_mem h))) := by
  have := usen_rfind_prop2.mp (Option.get_mem h)
  exact (Option.get_of_eq_some (Option.isSome_of_mem this) this).symm
theorem usen_rfind_prop2'' {O k x cf} :
    (usen O cf.rfind' (k + 1) x)=(do
      guard (x ≤ k);
      let guard ← evaln O (k + 1) (rfind' cf) x;
      let ro := guard - x.r
      let mut max := 0
      for i in List.reverse (List.range (ro+1)) do
        let usen_i ← (usen O cf (k + 1-i) ⟪x.l, i+x.r⟫)
        max := Nat.max max usen_i
      max : Option ℕ) :=
  Option.eq_of_eq_some fun _ => usen_rfind_prop2
theorem usen_xles {O c s x} (h : (usen O c (s + 1) x).isSome) : x ≤ s :=
  le_of_lt_succ (usen_bound (Option.get_mem h))
theorem usen_sound {O} : ∀ {c s n x}, x ∈ usen O c s n → x ∈ use O c n := by
  intro c k n x h
  induction k,c using CodeNatK.induction generalizing x n with
  | h0 c => simp [usen] at h
  | hzero k =>
    simp only [usen, Option.pure_def, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', Option.some.injEq, exists_const, use, Part.mem_some_iff] at h ⊢
    exact h.right.symm
  | hsucc k =>
    simp only [usen, Option.pure_def, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', Option.some.injEq, exists_const, use, Part.mem_some_iff] at h ⊢
    exact h.right.symm
  | hleft k =>
    simp only [usen, Option.pure_def, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', Option.some.injEq, exists_const, use, Part.mem_some_iff] at h ⊢
    exact h.right.symm
  | hright k =>
    simp only [usen, Option.pure_def, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', Option.some.injEq, exists_const, use, Part.mem_some_iff] at h ⊢
    exact h.right.symm
  | horacle k =>
    simp only [usen, Option.pure_def, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', Option.some.injEq, exists_const, use, Part.mem_some_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    simp [← h]
  | hpair k cf cg hf hg =>
    simp? [use, usen, Option.bind_eq_some_iff, Seq.seq]  at h ⊢ says
      simp only [usen, Option.pure_def, Option.bind_eq_bind, Option.mem_def,
        Option.bind_eq_some_iff, Option.guard_eq_some', Option.some.injEq, exists_const, use,
        Seq.seq, Part.map_eq_map, Part.bind_map, Part.mem_bind_iff, Part.mem_map_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    rcases h with ⟨y, ef, z, eg, rfl⟩
    aesop? says
      simp_all only [Option.mem_def]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => apply Exists.intro
        on_goal 2 => apply And.intro
        on_goal 3 => {rfl}
        · simp_all only
        · simp_all only
  | hcomp k cf cg hf hg =>
    simp? [use, usen, Option.bind_eq_some_iff, Seq.seq]  at h ⊢ says
      simp only [usen, Option.pure_def, Option.bind_eq_bind, Option.mem_def,
        Option.bind_eq_some_iff, Option.guard_eq_some', Option.some.injEq, exists_const, use,
        Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.map_bind, Part.bind_map,
        Part.mem_bind_iff, Part.mem_map_iff] at h ⊢
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨h2,@hg n h2 h3,
      h4, evaln_sound h5,
      h6, @hf h4 h6 h7, ?_⟩
    subst h8
    exact Nat.max_comm h2 h6
  | hprec k cf cg hf hg ih =>
    simp? [use, usen, Option.bind_eq_some_iff, Seq.seq]  at h ⊢ says
      simp only [usen, unpair1_to_l, Option.pure_def, Option.bind_eq_bind, unpair2_to_r,
        Option.mem_def, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const, use, Seq.seq,
        Part.map_eq_map, Part.bind_map, Part.bind_eq_bind] at h ⊢
    revert h
    induction n.r generalizing x
    case zero =>
      intro h1
      replace h1 := h1.right
      simp only [rec_zero] at h1
      exact hf h1
    case succ m IH =>
      simp only [Part.mem_bind_iff, Part.mem_map_iff, and_imp]
      intro hh1 hh
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hh
      rcases hh with ⟨hh,h3,h4,h5,h7,h8,h9⟩
      use h4
      constructor
      · exact evaln_sound h5
      · use hh
        constructor
        · have main := ih h3
          simpa [use] using main
        · exact ⟨h7, @hg (Nat.pair n.l (Nat.pair m h4)) h7 h8,h9⟩
  | hrfind k cf hfih =>
    have := usen_rfind_prop2.mp h
    have urop1 := usen_rfind_prop h
    rcases urop1 0 (Nat.zero_le (rfind'_obtain (usen_rfind_prop_aux h))) with ⟨h1,h2⟩
    rcases usen_dom_iff_evaln_dom.mp ⟨x,h⟩ with ⟨h7,h8⟩
    have h145: rfind'_obtain (usen_rfind_prop_aux h) = h7 - n.r := by
      simp [rfind'_obtain, Part.eq_some_iff.mpr (evaln_sound h8)]
    simp only [Option.mem_def, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.bind_fun_some, h145, tsub_zero, add_zero, pair_lr] at *
    simp_all only [Option.mem_def, Option.bind_some]
    simp only [usen_xles (Option.isSome_of_mem h)] at this
    simp only [use, Part.pure_eq_some, Part.bind_eq_bind, Part.bind_some, Part.coe_some,
      Part.bind_some_right, Part.mem_bind_iff]
    use h7
    constructor
    · exact evaln_sound h8
    revert this
    revert urop1
    generalize 0 = base
    induction h7 - n.r generalizing base with
    | zero =>
      -- todo: this simp call was from old mathlib
      simp? says simp only [nonpos_iff_eq_zero, forall_eq, tsub_zero, add_zero, pair_lr, zero_add,
        range_one,
        reverse_cons, reverse_nil, nil_append, forIn_cons, Option.pure_def, forIn_nil,
        Option.bind_eq_bind, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_bind_iff,
        Part.mem_some_iff, forall_exists_index]
      intro h3 h4 this
      use (ForInStep.yield (base.max h1))
      constructor
      · exact ⟨h1, @hfih (k + 1) (le_rfl) n h1 h2, rfl⟩
      simp_all
    | succ nn ih =>
      simp (config := { singlePass := true }) only [guard_true, reversed_range_indt, forIn_cons]
      simp only [Option.pure_def, reduceSubDiff, Option.bind_eq_bind, Option.bind_some,
        Part.pure_eq_some, Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff]
      intro urop1
      have aux0 : (∀ j ≤ nn, ∃ y, usen O cf (k + 1 - j) (Nat.pair n.l (n.r + j)) = some y) := by
        intro j jnn
        exact urop1 j (le_add_right_of_le jnn)
      rcases urop1 (nn+1) (Nat.le_refl (nn + 1)) with ⟨h3,h4⟩
      simp only [reduceSubDiff] at h4
      ac_nf at h4 ⊢
      -- todo: this remove -existsAndEq
      simp only [h4, Option.bind_some]
      replace hfih := @hfih (k-nn)
        (le_add_right_of_le (sub_le k nn)) (Nat.pair n.l (nn + (n.r+1))) h3 h4
      intro h5
      use (ForInStep.yield (base.max h3))
      constructor
      · use h3
      exact ih (base.max h3) aux0 h5
end usen_sound

section usen_complete
theorem eval_dom_imp_evaln {O c x} (h : (eval O c x).Dom) : ∃ s, (evaln O s c x).isSome := by
  rcases evaln_complete.mp (Part.get_mem h) with ⟨k, hk⟩
  use k
  exact Option.isSome_of_mem hk

theorem use_dom_iff_eval_dom {O c x} : (use O c x).Dom ↔ (eval O c x).Dom := by
  constructor
  · induction c generalizing x with
    | zero => exact id
    | succ => exact id
    | left => exact id
    | right => exact id
    | oracle => exact id
    | pair cf cg hcf hcg => simp [use,eval,Seq.seq]; simp_all
    | comp cf cg hcf hcg => simp [use,eval,Seq.seq]; simp_all
    | prec cf cg hcf hcg =>
      simp? [use, eval, Seq.seq] says
        simp only [use, unpair1_to_l, eval, unpaired, unpair_pair, Part.bind_eq_bind, Seq.seq,
          Part.map_eq_map, Part.bind_map, unpair2_to_r]
      induction x.r with
      | zero => simp_all
      | succ xrM1 ih =>
      intro a
      simp_all only [Part.bind_dom, Part.map_Dom, exists_prop, exists_and_left, exists_true_left,
        forall_const]
    | rfind' cf hcf => simpa [use] using fun x_1 h => x_1
  intro h
  rcases eval_dom_imp_evaln h with ⟨s, hs⟩
  exact Part.mem_imp_dom <| usen_sound <| Option.get_mem <| en2un hs

abbrev e2u {O c x} : (eval O c x).Dom → (use O c x).Dom := use_dom_iff_eval_dom.mpr
abbrev u2e {O c x} : (use O c x).Dom → (eval O c x).Dom := use_dom_iff_eval_dom.mp
theorem use_rfind_prop {O cf n} (hu : (use O (rfind' cf) n).Dom) :
    ∀ j ≤ rfind'_obtain (u2e hu),
    (use O cf (Nat.pair n.l (n.r+j))).Dom := by
  intro j hjro
  rw [add_comm]
  exact e2u ((rfind'_obtain_prop (u2e hu)).right.left j hjro)

-- similar in concept to displace_loop_0.
lemma displace_loop_1 {O cf ro hi_val lo_val} {base n : ℕ}
    (hhi_val : hi_val ∈ use O cf (Nat.pair n.l (ro + 1 + n.r)))
    (rop3 : ∀ j ≤ ro + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
    (lo_val_dom : (use O cf n).Dom)
    (lo_valdef : lo_val = (use O cf n).get lo_val_dom) :
    (forIn (List.range (ro + 1)).reverse (base.max hi_val) fun i r ↦
    (use O cf (Nat.pair n.l (i + n.r))).bind fun use_i ↦
      Part.some (ForInStep.yield (r.max use_i))) =
    (forIn (List.range (ro + 1)).reverse (base.max (lo_val)) fun i r ↦
    (use O cf (Nat.pair n.l (i + (1 + n.r)))).bind fun use_i ↦
      Part.some (ForInStep.yield (r.max use_i))) := by
  revert hhi_val
  ac_nf
  induction ro generalizing hi_val n base with
  | zero =>
    intro hhi_val
    have := Part.get_eq_iff_eq_some.mp (_root_.id (Eq.symm lo_valdef))
    simp_all? says
      simp_all only [zero_add, Part.get_some, range_one, reverse_cons, reverse_nil, nil_append,
        forIn_cons, pair_lr, Nat.max_assoc, Part.bind_some, Part.pure_eq_some, forIn_nil,
        Part.bind_eq_bind]
    have := rop3 1 (le_rfl)
    simp only [Part.Dom.bind this, Part.bind_some, Part.some_inj]
    simp only [← (Part.eq_get_iff_mem this).mpr hhi_val]
    ac_nf
  | succ nnn ih =>
    intro hhi_val
    simp (config := { singlePass := true }) only [reversed_range_indt, forIn_cons]
    simp only [Nat.max_assoc, Part.pure_eq_some, Part.bind_eq_bind]
    ac_nf
    have dom1 : (use O cf (Nat.pair n.l (nnn + (n.r + 1)))).Dom := by
      have := rop3 (nnn+1) (le_add_right (nnn + 1) 1)
      ac_nf at this
    simp only [Part.Dom.bind dom1, Part.bind_some, reduceAdd]
    have dom2 : (use O cf (Nat.pair n.l (nnn + (n.r + 2)))).Dom := by
      ac_nf at hhi_val
      simp only [reduceAdd] at hhi_val
      exact Part.mem_imp_dom hhi_val
    simp only [Part.Dom.bind dom2, Part.bind_some]
    replace ih := @ih ((use O cf (Nat.pair n.l (nnn + (n.r + 1)))).get dom1) (base.max hi_val)
      (Nat.pair n.l (n.r)) ?_
    rotate_right
    · intro j hj
      have := rop3 j (le_add_right_of_le hj)
      simpa
    simp only [pair_lr] at ih
    ac_nf at ih
    have iihh2 := ih lo_val_dom lo_valdef (Part.get_mem dom1)
    clear ih
    rw [iihh2]
    have : (use O cf (Nat.pair n.l (nnn + (n.r + 2)))).get dom2 = hi_val := by
      simpa [show (nnn + (n.r + 2)) = (nnn + 1 + (n.r + 1)) from by grind]
        using Part.get_eq_of_mem hhi_val _
    rw [this]
    rw (config := {occs := .pos [2]}) [Nat.max_comm]
lemma displace_loop_2 {O cf ro hi_val lo_val s x} {base n use_steps : ℕ}
    (hhi_val : hi_val ∈ use O cf (Nat.pair n.l (ro + 1 + n.r)))
    (rop3 : ∀ j ≤ ro + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
    (lo_val_dom : (use O cf n).Dom)
    (lo_valdef : lo_val=(use O cf n).get lo_val_dom)
    (i2' : usen O cf (use_steps + 1) n = some ((use O cf n).get lo_val_dom))
    (lolineq : s + 1 ≤ use_steps )
    (hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, usen O cf (k + 1) n = some x)
    (hs : (forIn (List.range (ro + 1)).reverse (base.max lo_val) fun i r ↦
        (usen O cf (s + 1 - i) (Nat.pair n.l (i + (1 + n.r)))).bind fun a ↦
        some (ForInStep.yield (r.max a))) =
      some x) :
    (forIn (List.range (ro + 1)).reverse (base.max (lo_val)) fun i r ↦
      (usen O cf (s + 1-i) (Nat.pair n.l (i + (1 + n.r)))).bind fun use_i ↦
      some (ForInStep.yield (r.max use_i))) =
    ((forIn (List.range (ro + 1)).reverse (base.max hi_val) fun i r ↦
      (usen O cf (use_steps + 1 - i) (Nat.pair n.l (i + n.r))).bind fun usen_i ↦
        some (ForInStep.yield (r.max usen_i)))) := by
  revert hhi_val
  induction ro generalizing hi_val n base with
  | zero =>
    intro hhi_val
    simp_all? says
      simp_all only [zero_add, range_one, reverse_cons, reverse_nil, nil_append, forIn_cons,
        tsub_zero, Nat.max_assoc, Option.pure_def, forIn_nil, Option.bind_eq_bind, pair_lr,
        Option.bind_some, Option.some.injEq]
    rcases hf hhi_val with ⟨g3,g4⟩
    have : ∃ z, z ∈ (usen O cf (s + 1) ⟪n.l, 1+n.r⟫) := by
      contrapose hs
      simp only [Option.mem_def, not_exists] at hs
      simp [Option.eq_none_iff_forall_ne_some.mpr hs]
    rcases this with ⟨_, hnext_val⟩
    simp at hnext_val
    simp only [hnext_val] at hs
    simp only [usen_sing hnext_val g4, Option.bind_some, Option.some.injEq] at hs
    subst hs
    ac_nf
  | succ nnn ih =>
    intro hhi_val
    simp (config := { singlePass := true }) only [reversed_range_indt, forIn_cons] at hs ⊢
    simp only [reduceSubDiff, Nat.max_assoc, Option.pure_def, Option.bind_eq_bind] at hs ⊢
    rcases hf hhi_val with ⟨g3,g4⟩
    have : ∃ z, z ∈ (usen O cf (s - nnn) (Nat.pair n.l (nnn + 1 + (1 + n.r)))) := by
      contrapose hs
      simp only [Option.mem_def, not_exists] at hs
      have := Option.eq_none_iff_forall_ne_some.mpr hs
      simp [this]
    rcases this with ⟨_, hnext_val⟩
    simp at hnext_val
    simp only [hnext_val, Option.bind_some] at hs ⊢
    rw [add_assoc] at g4
    simp only [usen_sing hnext_val g4] at *
    have : ∃ z, z ∈ (usen O cf (use_steps - nnn) (Nat.pair n.l (nnn + 1 + n.r))) := by
      contrapose hs
      simp only [Option.mem_def, not_exists] at hs
      have := Option.eq_none_iff_forall_ne_some.mpr hs
      simp (config := {singlePass := true}) [reversed_range_indt]
      have : (usen O cf (s + 1 - nnn) (Nat.pair n.l (nnn + (1 + n.r)))) = Option.none := by
        rw [add_assoc] at this
        have ineq1: s + 1 - nnn ≤ use_steps - nnn := by grind only [cases Or]
        simp [usen_mono_contra ineq1 this]
      simp [this]
    rcases this with ⟨g1, g2⟩
    simp only [Option.mem_def] at g2
    simp only [g2, Option.bind_some]
    have dom1 : (use O cf (Nat.pair n.l (nnn + 1 + n.r))).Dom := by
      have := rop3 (nnn+1) (le_add_right (nnn + 1) 1)
      rw [show n.r + (nnn + 1) = nnn + 1 + n.r from by grind] at this
      exact this
    replace ih := @ih ((use O cf (Nat.pair n.l (nnn + 1 + n.r))).get dom1)
      (base.max hi_val) (Nat.pair n.l (n.r)) ?_
    rotate_right
    · intro j hj
      have := rop3 j (le_add_right_of_le hj)
      simpa
    simp only [pair_lr, Nat.max_assoc] at ih
    replace ih := ih lo_val_dom lo_valdef i2' ?_ ?_
    rotate_left
    · rw (config := {occs := .pos [2]}) [Nat.max_comm]
      exact hs
    · exact Part.get_mem dom1
    · rw (config := {occs := .pos [2]}) [Nat.max_comm]
      have : g1 = ((use O cf (Nat.pair n.l (nnn + 1 + n.r))).get dom1) := by
        exact (Part.eq_get_iff_mem dom1).mpr (usen_sound g2)
      rw [this]
      exact ih
lemma eval_rfind_prop5 {O cf y x} : x ∈ eval O (rfind' cf) y → y.r ≤ x := by
  simp [eval]; grind
/-
the prec case of the theorem `usen_complete`.
-/
theorem usen_complete_prec {O : ℕ → ℕ} {cf cg : Code}
    {hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, x ∈ usen O cf (k + 1) n}
    {hg : ∀ {n x : ℕ}, x ∈ use O cg n → ∃ k, x ∈ usen O cg (k + 1) n}
    {n x : ℕ} {h : x ∈ use O (cf.prec cg) n} :
    ∃ k, x ∈ usen O (cf.prec cg) (k + 1) n := by
  simp? [use, usen, pure, Seq.seq, Option.bind_eq_some_iff]  at h ⊢ says
    simp only [use, unpair1_to_l, Seq.seq, Part.map_eq_map, Part.bind_map, Part.bind_eq_bind,
      unpair2_to_r, usen, pure, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', exists_const] at h ⊢
  revert h
  generalize n.l = n₁; generalize n.r = n₂
  induction n₂ generalizing x n
  · intro h
    rcases hf h with ⟨k, hk⟩
    exact ⟨_, le_max_left _ _, usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
  case succ m IH =>
    intro h
    simp only [Part.mem_bind_iff, Part.mem_map_iff] at h
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
    rcases IH h4 with ⟨k₁, nk₁, hk₁⟩
    rcases hg h6 with ⟨k₂, hk₂⟩
    refine ⟨(max k₁ k₂).succ, Nat.le_succ_of_le <| le_max_of_le_left <|
          le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, ?_⟩
    simp only [succ_eq_add_one]
    subst h7
    simp_all only [Option.mem_def, sup_le_iff]
    rcases nk₁ with ⟨left, right⟩
    have aux1 : h5 ∈ (usen O cg (max k₁ k₂ + 1 + 1) (Nat.pair n₁ (Nat.pair m h1))) := by
      have : k₂+1 ≤ max k₁ k₂ + 1 + 1 :=  by
        apply Nat.add_le_add_iff_right.mpr
        apply le_add_right_of_le
        apply le_sup_right
      exact usen_mono this hk₂
    have aux2 : h3 ∈ (usen O (cf.prec cg) (max k₁ k₂ + 1) (Nat.pair n₁ m)) := by
      have : Nat.rec (usen O cf (k₁ + 1) n₁) (fun n n_ih ↦
          (usen O (cf.prec cg) k₁ ⟪n₁, n⟫).bind fun usen_prev ↦
          (evaln O k₁ (cf.prec cg) ⟪n₁, n⟫).bind fun evaln_prev ↦
          (usen O cg (k₁ + 1) (Nat.pair n₁ (Nat.pair n evaln_prev))).bind fun usen_indt ↦
          some (usen_prev.max usen_indt)) m = (usen O (cf.prec cg) ( k₁ + 1) (Nat.pair n₁ m)) := by
        simp [usen]
        simp [right]
      rw [this] at hk₁
      have : (k₁ + 1) ≤ (max k₁ k₂ + 1) := by
        apply Nat.add_le_add_iff_right.mpr
        apply le_sup_left
      exact usen_mono this hk₁
    have aux0 : h1 ∈ (evaln O (max k₁ k₂ + 1) (cf.prec cg) ⟪n₁, m⟫) := by
      rcases usen_dom_iff_evaln_dom.mp ⟨h3, aux2⟩ with ⟨hh1,hh2⟩
      rcases evaln_complete.mp h2 with ⟨hh3,hh4⟩
      rwa [evaln_sing hh2 hh4] at hh2
    rw [aux2, aux0]
    simp only [Option.bind_some]
    rw [aux1]
    simp
/-
the rfind' case of the theorem `usen_complete`.
-/
theorem usen_complete_rfind'
    {O : ℕ → ℕ}
    {cf : Code}
    {hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, x ∈ usen O cf (k + 1) n}
    {n x : ℕ}
    {h : x ∈ use O cf.rfind' n} :
    ∃ k, x ∈ usen O cf.rfind' (k + 1) n := by
  simp? [use] at h says
    simp only [use, Part.pure_eq_some, Part.bind_eq_bind, Part.bind_some, Part.coe_some,
      Part.bind_some_right, Part.mem_bind_iff] at h
  -- we use `usen_rfind_prop2` to characterise usen rfind' as a for loop, akin to
  -- the rfind definition in `use`.
  suffices ∃ k, x ∈ (do
    guard (n ≤ k);
    let guard ← evaln O (k + 1) (rfind' cf) n;
    let ro := guard - n.r
    let mut max := 0
    for i in List.reverse (List.range (ro+1)) do
      let usen_i ← (usen O cf (k + 1-i) (Nat.pair n.l (i+n.r)))
      max := Nat.max max usen_i
    max : Option ℕ) from by
    rcases this with ⟨k,hk⟩
    use k
    exact usen_rfind_prop2.mpr hk
  /-
  We will use induction on rfind'_obtain (i.e. the number of searches / loop iterations
  required before rfind' finds a 0.)

  Suppose the theorem holds for `ro`. (that if the rfind'_obtain value is `ro`, then
  there exists some number of steps `s`, such that our for loop returns the same result
  as the `use O cf.rfind' n`.)
  
  Now suppose the rfind'_obtain value is `ro+1`.
  i.e. that `eval O cf ⟪n.l, n.r + ro + 1⟫` is 0.

  Then, we can explicitly execute one layer/iteration of the for loop, bringing
  down the iteration counter to `ro+1`.

  However, the for loop state is mutated; though we start with max = 0, max has now been updated
  by `max := Nat.max max usen_i`.

  So, we will generalise the starting "max" value in our induction proof to `base`.
  -/
  generalize 0 = base at h ⊢
  rcases h with ⟨h1,h2,h3⟩
  have rogeq : n.r ≤ h1 := eval_rfind_prop5 h2
  rw [show h1=h1-n.r+n.r from by simp [rogeq]] at h2
  clear rogeq
  have hdom1 := Part.dom_iff_mem.mpr ⟨h1-n.r+n.r,h2⟩
  have hdom  := use_dom_iff_eval_dom.mpr hdom1
  have rop   := rfind'_obtain_prop hdom1
  have rop6  := rfind'_obtain_prop_6 hdom1
  have urop1 := use_rfind_prop hdom
  have hrop : rfind'_obtain (u2e hdom) = h1 - n.r := by
    simp [rfind'_obtain, Part.eq_some_iff.mpr h2]
  simp? [hrop]  at * says
    simp only [Option.mem_def, hrop, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.bind_fun_some] at *
  clear hrop
  revert h3; revert h2; revert urop1; revert rop6; revert rop
  induction h1 - n.r generalizing base n with
  | zero =>
    simp_all only [zero_add, pair_lr, nonpos_iff_eq_zero, forall_eq, not_lt_zero',
      IsEmpty.forall_iff, implies_true, and_true, add_zero, range_one, reverse_cons, reverse_nil,
      nil_append, forIn_cons, Part.pure_eq_some, forIn_nil, Part.bind_eq_bind, Part.mem_bind_iff,
      Part.mem_some_iff, forall_exists_index, and_imp, forall_const]
    intro urop1 rop1 h2 rop6 h4 lo_val hlo_val h7 h8
    rcases evaln_complete.mp h2 with ⟨s, hs⟩
    rcases hf hlo_val with ⟨s_lo, hs_lo⟩
    have nlek : (n ≤ (s - 1).max (s_lo + 1)) := by
      contrapose hs_lo
      simp only [le_sup_iff, not_or, not_le] at hs_lo
      intro h16
      have := Nat.lt_trans (usen_bound h16) hs_lo.right
      simp at this
    use Nat.max (s-1) (s_lo+1)
    simp_all only [Option.mem_def, le_sup_iff, guard_true, Option.pure_def, Option.bind_some]
    have aux2 := evaln_mono (le_add_of_sub_le (Nat.le_max_left (s - 1) (s_lo + 1))) hs
    simp at aux2
    simp [aux2]
    have : (s_lo + 1) ≤ (s - 1).max (s_lo + 1) + 1 := by
      simp only [add_le_add_iff_right, le_sup_iff, le_add_iff_nonneg_right, _root_.zero_le,
        or_true]
    have aux0 := usen_mono this hs_lo
    simp at aux0
    simp [aux0]
  | succ ro ih =>
    simp (config := { singlePass := true }) only [reversed_range_indt, forIn_cons, and_imp]
    simp only [Part.pure_eq_some, Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff,
      Option.pure_def, Option.bind_eq_bind, forall_exists_index, and_imp]
    intro urop1 rop1 rop2 rop4 rop6 rop3 h2 h3 hi_val hhi_val h7 h8
    -- hi_val is the value `max` is updated to after one iteration of the for loop.
    have rop40 := rop4 1 (le_add_left 1 ro)
    have rop41 := e2u rop40
    have lo_val_dom := rop3 0 (le_add_left 0 (ro + 1))
    simp only [add_zero, pair_lr] at lo_val_dom
    let lo_val := (use O cf n).get lo_val_dom
    /-
    in our ih, we start from the highest value but only do
    ro iterations, so
      1. we start from ⟪n.l, 1+n.r⟫
      2. lo_val need to be included in the base value.
    To bridge the ih to our goal, where we instead exclude the hi_val and
    include lo_val, we use the displace_loop* lemmas.
    -/
    replace ih := @ih ⟪n.l, 1+n.r⟫ (base.max lo_val) rop40 rop41 ?_ ?_ ?_ ?_ ?_
    -- discharge the ih conditions
    rotate_left
    · simp only [pair_l, pair_r]
      constructor
      · ac_nf at urop1 ⊢
      constructor
      · intro j hj
        have := rop1 (j+1) (Nat.add_le_add_right hj 1)
        rw [← add_assoc]
        exact rop1 (j+1) (Nat.add_le_add_right hj 1)
      constructor
      · intro j hj
        rw [← add_assoc]
        exact rop2 (j+1) (Nat.add_le_add_right hj 1)
      · intro j hj
        rw [← add_assoc]
        exact rop4 (j+1) (Nat.add_le_add_right hj 1)
    · simp only [pair_l, pair_r]
      intro j hj
      rw [← add_assoc]
      rw [← add_assoc]
      exact rop6 (j+1) (Nat.add_le_add_right hj 1)
    · simp only [pair_l, pair_r]
      intro j hj
      rw [add_comm]
      rw [← add_assoc]
      exact e2u (rop1 (j+1) (Nat.add_le_add_right hj 1))
    · simp only [pair_r]
      rw [← add_assoc]
      exact rop6 (1) (le_add_left 1 ro)
    all_goals
      simp_all only [pair_l, pair_r]
      have displace_loop_1 := @displace_loop_1 O cf ro hi_val lo_val
        base n hhi_val rop3 lo_val_dom rfl
      have := h8
      rewrite [displace_loop_1] at this
    · exact this
    rcases ih with ⟨s, hs⟩
    have a0 := rop3 0 (le_add_left 0 (ro + 1))
    simp only [add_zero, pair_lr] at a0
    replace a0 := Part.get_mem a0
    rcases (hf a0) with ⟨s_lo, hs_lo⟩
    -- the lo calculation halts within s_lo steps.
    replace : ∃z,z∈ (evaln O (s + 1) cf.rfind' ⟪n.l, 1+n.r⟫) := by
      contrapose hs
      simp only [Option.mem_def, not_exists] at hs
      have := Option.eq_none_iff_forall_ne_some.mpr hs
      simp [this]
    rcases this with ⟨_, h22⟩
    simp only [Option.mem_def] at h22
    rw [h22] at hs
    rcases evaln_complete.mp (rop6 1 (le_add_left 1 ro)) with ⟨_, h20⟩
    rw [evaln_sing h22 h20] at hs
    rcases evaln_complete.mp h2 with ⟨s_rf, hs_rf⟩
    -- the entire calculation (of rfind) halts within s_rf steps.
    rcases hf hhi_val with ⟨s_hi, hs_hi⟩
    -- the hi calculation halts within s_lo steps.
    let use_steps := (Nat.max (Nat.max s_rf (s_hi+1) + ro) (Nat.max (s + 1) s_lo)).max n
    use use_steps
    -- we choose steps to be sufficiently large such that all the smaller computations
    -- can be easily shown to converge.
    have nlek : (n ≤ use_steps) := Nat.le_max_right _ _
    have nlek2 : (Nat.pair n.l (1 + n.r) ≤ s) := by
      contrapose hs
      simp [hs]
    simp only [nlek] at ⊢
    simp only [nlek2, guard_true, Option.pure_def, Option.bind_some] at hs
    replace : ro + 1 + n.r - (1 + n.r) + 1 = ro + 1 := by
      rw [add_assoc]
      rw [Nat.add_sub_cancel_right ro (1+n.r)]
    rw [this] at hs
    replace : (evaln O ((use_steps)+1) cf.rfind' n) = some (ro + 1 + n.r) := by
      simp only [Option.mem_def] at hs_rf
      rw [← hs_rf]
      apply evaln_mono' (Option.isSome_of_mem hs_rf) _
      grind
    simp [this]
    have : (usen O cf (use_steps - ro) (Nat.pair n.l (ro + 1 + n.r))) = some hi_val := by
      rw [← hs_hi]
      apply usen_mono' (Option.isSome_of_mem hs_hi) _
      grind
    simp [this]
    have aux1 : usen O cf (use_steps + 1) n = some ((use O cf n).get lo_val_dom) := by
      rw [← hs_lo]
      apply usen_mono' (Option.isSome_of_mem hs_lo) _
      grind
    have lemlem2 := @displace_loop_2 O cf ro hi_val lo_val s x base n use_steps hhi_val
      (fun j a ↦ rop3 j a) lo_val_dom rfl aux1 (by grind) (fun a ↦ hf a) hs
    simp_all only [Option.mem_def]
theorem usen_complete {O} {c n x} : x ∈ use O c n ↔ ∃ s, x ∈ usen O c s n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => usen_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ usen O  c (k + 1) n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
  | pair cf cg hf hg =>
    simp? [use, usen, pure, Seq.seq, Option.bind_eq_some_iff]  at h ⊢ says
      simp only [use, Seq.seq, Part.map_eq_map, Part.bind_map, Part.mem_bind_iff, Part.mem_map_iff,
        usen, pure, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', Option.some.injEq, exists_const] at h ⊢
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    simp? [use, usen, pure, Seq.seq, Option.bind_eq_some_iff]  at h ⊢ says
      simp only [use, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.map_bind, Part.bind_map,
        Part.mem_bind_iff, Part.mem_map_iff, usen, pure, Option.bind_eq_bind, Option.mem_def,
        Option.bind_eq_some_iff, Option.guard_eq_some', Option.some.injEq, exists_const] at h ⊢
    rcases h with ⟨y, hy, hx1, hx2, hx3, hx4, hx5⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx4 with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        ?_⟩
    use hx1
    constructor
    · rcases usen_dom_iff_evaln_dom.mp (Exists.intro y hk₁) with ⟨b,hb⟩
      rcases evaln_complete.mp hx2 with ⟨kk,hs⟩
      rw [evaln_sing hs hb]
      exact evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hb
    · refine ⟨_,usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂,
      (by subst hx5; exact Nat.max_comm hx3 y) ⟩
  | prec cf cg hf hg => exact @usen_complete_prec O cf cg hf hg n x h
  | rfind' cf hf => exact @usen_complete_rfind' O cf hf n x h
  | oracle =>
    simp [use] at h
    use (n+1)
    simpa [usen] using h.symm
  | _ =>
    simp [use] at h
    use (n+1)
    simp only [Option.mem_def]
    simp only [usen, le_add_iff_nonneg_right, _root_.zero_le, guard_true, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
    exact h.symm

end usen_complete
end Oracle.Single.Code
