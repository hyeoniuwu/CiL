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
private lemma guard_imp {k₂ n a} {k : ℕ} (h : k ≤ k₂) : guard (n ≤ k) = some a → (guard (n ≤ k₂) : Option Unit) = some a := by
  intro h3
  have : n ≤ k := by
    contrapose h3
    simp only [h3, guard_false, reduceCtorEq, not_false_eq_true]
  have : n ≤ k₂ := by exact Nat.le_trans this h
  simp [this]
theorem usen_mono {O} : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ usen O c k₁ n → x ∈ usen O c k₂ n
| 0, k₂, c, n, x, _, h => by simp [usen] at h
| k + 1, k₂ + 1, c, n, x, hl, h => by
  have hl' := Nat.le_of_succ_le_succ hl
  have :
    ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
      k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
        x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
    simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_and_left,
      exists_const, and_imp]
    introv h h₁ h₂ h₃
    exact ⟨le_trans h₂ h, h₁ h₃⟩
  simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
  induction' c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n <;>
    rw [usen] at h ⊢;

    -- rw [usen] at h ⊢<;> refine this hl' (fun h => ?_) h
  iterate 5 exact this hl' (fun a ↦ a) h
  · -- pair cf cg
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢

    -- refine h.imp fun a => ?_
    refine h.imp fun a => And.imp (?_) <| ?_
    exact guard_imp hl'

    refine Exists.imp fun b => ?_
    rintro ⟨h1,h2,h3,h4⟩
    exact ⟨hf n b h1, h2, hg n h2 h3, h4⟩


    -- exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
  · -- comp cf cg
    simp only [bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact ⟨h1,guard_imp hl' h2,
    h3,hg n h3 h4,
    h5,evaln_mono hl h6,
    h7,hf h5 h7 h8,
    h9⟩


  · -- prec cf cg
    revert h
    simp only [bind]
    induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
    · exact fun g h ↦ ⟨Nat.le_trans g hl', hf n.l x h⟩
    ·
      exact fun g x1 hx1 x2 hx2 x3 hx3 hmax =>
      ⟨
        Nat.le_trans g hl',
        x1,usen_mono hl' hx1,
        x2,by rw [evaln_mono hl' hx2],
        x3,
        by (expose_names; exact hg (Nat.pair n.l (Nat.pair n_1 x2)) x3 hx3), hmax
      ⟩

  · -- rfind' cf
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
    | zero => simp at h7 ⊢; assumption
    | succ n =>
      simp at h7 ⊢
      expose_names
      simp only [Option.bind_eq_some_iff] at h7 ⊢
      rcases h7 with ⟨h8,h9,h10⟩
      exact ⟨h8,usen_mono hl' h9, h10⟩
theorem usen_mono_contra {O} : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → usen O c k₂ n = Option.none → usen O c k₁ n = Option.none := by
  intro k₁ k₂ c n k1k2 opt
  contrapose opt
  have := usen_mono k1k2 (Option.get_mem (Option.isSome_iff_ne_none.mpr opt))
  refine Option.ne_none_iff_exists'.mpr ?_
  exact Exists.intro ((usen O c k₁ n).get (Option.isSome_iff_ne_none.mpr opt)) this
theorem usen_mono_dom {O} : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → (usen O c k₁ n).isSome → (usen O c k₂ n).isSome := by
  intro k1 k2 c n k1k2 h1
  exact Option.isSome_of_mem (usen_mono k1k2 (Option.get_mem h1))
theorem evaln_mono_dom {O} : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → (evaln O k₁ c n).isSome → (evaln O k₂ c n).isSome := by
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
lemma usen_sing' {O c s1 x h1 s2 h2} : (usen O c s1 x).get h1 = (usen O c s2 x).get h2 := usen_sing (Option.get_mem h1) (Option.get_mem h2)

lemma usen_mono' {O c s1 x s2}
(h1 : (usen O c s1 x).isSome)
(h2 : s1 ≤ s2)
: (usen O c s2 x) = (usen O c s1 x) := by
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

theorem usen_none_iff_evaln_none {O c s x} : (usen O c s x) = Option.none ↔ (evaln O s c x) = Option.none := by
-- using evaln.induct doesnt work, the prec inductive hypothesis w cf.prec cg is s + 1 instead of s for some reason
  induction s,c using ind.induct generalizing x with
  | case1 _ => simp [usen,evaln]
  | case2 s => simp [usen,evaln]
  | case3 s => simp [usen,evaln]
  | case4 s => simp [usen,evaln]
  | case5 s => simp [usen,evaln]
  | case6 s => simp [usen,evaln]
  | case7 s cf cg hcf hcg =>
    simp [usen,evaln]
    simp [Seq.seq]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp [h]
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
    simp [usen,evaln]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp [h]
    constructor
    · intro hh a ha
      have := (@hcg x).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
      exact hcf.mp (Option.eq_none_iff_forall_ne_some.mpr (hh a2 ha2 a ha))
    · exact fun hh a ha a3 ha3 ↦ Option.eq_none_iff_forall_ne_some.mp (hcf.mpr (hh a3 ha3))
  | case9 s cf cg hcf hcg ih =>
    simp [usen,evaln]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp [h]
    cases hxr : x.r with
    | zero => simp; exact hcf
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
    simp [usen,evaln]
    cases Classical.em (x ≤ s) with
    | inr h => simp [h]
    | inl h =>
    simp [h]
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
      simp at this ⊢
      exact ih.mp (Option.eq_none_iff_forall_ne_some.mpr this)

    · intro hh a ha a3 ha3
      have := hh a3 ha3

      cases a3 with
      | zero => simp at this
      | succ n =>
      simp at this ⊢
      apply Option.eq_none_iff_forall_ne_some.mp
      exact ih.mpr this
theorem usen_dom_iff_evaln_dom {O c s x} : (∃a,a ∈ (usen O c s x)) ↔ (∃b,b ∈ (evaln O s c x)) := by
  have := (@usen_none_iff_evaln_none O c s x).not
  simp [Option.eq_none_iff_forall_ne_some] at this
  exact this
theorem usen_dom_iff_evaln_dom' {O c s x} : ((usen O c s x).isSome) ↔ ((evaln O s c x).isSome) := by
  have := (@usen_none_iff_evaln_none O c s x).not
  simp at this
  simp [isSome_iff_not_none] at this
  exact Bool.coe_iff_coe.mpr this
abbrev en2un {O s c x} : (evaln O s c x).isSome → (usen O c s x).isSome := usen_dom_iff_evaln_dom'.mpr
abbrev un2en {O c s x} : (usen O c s x).isSome → (evaln O s c x).isSome := usen_dom_iff_evaln_dom'.mp
end usen_dom_iff_evaln_dom

section usen_sound
-- Custom induction principle used in usen_sound
def CodeNatK.induction
  {motive : ℕ → Code → Prop}
  -- base case: k = 0, c arbitrary
  (h0 : ∀ c, motive 0 c)

  -- step case: k+1
  (hzero  : ∀ k, motive (k+1) .zero)
  (hsucc  : ∀ k, motive (k+1) .succ)
  (hleft  : ∀ k, motive (k+1) .left)
  (hright : ∀ k, motive (k+1) .right)
  (horacle : ∀ k, motive (k+1) .oracle)

  (hpair : ∀ k cf cg,
    motive (k+1) cf →
    motive (k+1) cg →
    motive (k+1) (.pair cf cg))

  (hcomp : ∀ k cf cg,
    motive (k+1) cf →
    motive (k+1) cg →
    motive (k+1) (.comp cf cg))

  (hprec : ∀ k cf cg,
    motive (k+1) cf →
    motive (k+1) cg →
    motive k (.prec cf cg) →
    motive (k+1) (.prec cf cg))

  (hrfind : ∀ k cf,
    (∀ x' ≤ k+1, motive x' cf) →
    motive (k+1) (.rfind' cf))

 : ∀ k c, motive k c := by
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
(usen O cf.rfind' (k + 1) n).isSome
→
(evaln O (k + 1) cf.rfind' n).isSome
:= by
  induction k+1 generalizing n with
  | zero => simp [usen]
  | succ k ih =>

  intro h
  simp [usen] at h
  simp [evaln]
  have nlek : n ≤ k := by contrapose h; simp at h; simp [h]
  simp [nlek] at h ⊢
  have usen_base_dom : (usen O cf (k + 1) n).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind usen_base_dom] at h
  have evaln_base_dom : (evaln O (k + 1) cf n).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind evaln_base_dom] at h ⊢

  cases hevaln_base : (evaln O (k + 1) cf n).get evaln_base_dom with
  | zero => simp
  | succ _ =>
    simp [hevaln_base] at h ⊢
    have usen_indt_dom : ((usen O cf.rfind' k (Nat.pair n.l (n.r + 1)))).isSome := by contrapose h; simp at h; simp [h]
    clear h
    exact ih usen_indt_dom
theorem usen_rfind_prop_aux' {O k n} {cf : Code} :
(usen O cf.rfind' (k + 1) n).isSome
→
(eval O cf.rfind' n).Dom
:= fun h ↦en2e (usen_rfind_prop_aux'' h)
theorem usen_rfind_prop_aux {O k n x} {cf : Code} :
(x ∈ usen O cf.rfind' (k + 1) n)
→
(eval O cf.rfind' n).Dom
:= by
  intro h
  have : (usen O cf.rfind' (k + 1) n).isSome := by exact Option.isSome_of_mem h
  exact usen_rfind_prop_aux' this

theorem usen_rfind_prop' {O cf k n} (hu : (usen O (rfind' cf) (k + 1) n).isSome):
∀j ≤ rfind'_obtain (usen_rfind_prop_aux' hu),
  (usen O cf (k + 1 - j) (Nat.pair n.l (n.r+j))).isSome
  -- and also the maximum of these is equal to the usen.
:= by
  intro j hjro
  rw (config := {occs := .pos [2]}) [add_comm]
  exact en2un ((nrfind'_obtain_prop' (un2en hu)).right.left j hjro)
theorem usen_rfind_prop {O k n x cf} (h : x ∈ usen O cf.rfind' (k + 1) n):
∀j ≤ rfind'_obtain (usen_rfind_prop_aux h),
  ∃y,y∈ (usen O cf (k + 1 - j) (Nat.pair n.l (n.r+j)))
  -- and also the maximum of these is equal to the usen.
:= by
  have := @usen_rfind_prop'
  simp [Option.isSome_iff_mem] at this
  exact fun j a ↦ this x h j a
lemma nrf_aux {O cf k x} (h : (usen O (rfind' cf) k x).isSome) :
 k=k-1+1
:= by
  have : k ≠ 0 := by
    contrapose h; simp [h]
    simp [usen]
  have keqkM1P1 : k=k-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero this)
  exact keqkM1P1
lemma nrf {O cf k x} (h : (usen O (rfind' cf) k x).isSome) :
x ≤ k-1
∧
(usen O cf k x).isSome
∧
(evaln O (k) cf x).isSome
:= by
  have keqkM1P1 := nrf_aux h
  simp (config := {singlePass := true}) [keqkM1P1] at h ⊢

  simp [usen] at h
  have xlek : x ≤ k-1 := by
    contrapose h;
    simp [h, Option.bind]
  simp [xlek] at h ⊢
  have usen_base_dom : (usen O cf (k-1+1) x).isSome := by exact Option.isSome_of_isSome_bind h
  simp [isSome.bind usen_base_dom] at h
  simp [usen_base_dom]
  have evaln_base_dom : (evaln O (k -1+1) cf x).isSome := by exact un2en usen_base_dom
  simp [isSome.bind evaln_base_dom] at h ⊢
  simp [evaln_base_dom]

lemma unrpeq2' {O cf x evalnbasedom evaln_ver_dom} :
((eval O cf x).get evalnbasedom = 0)
↔
((eval O cf.rfind' x).get evaln_ver_dom - x.r=0) := by
  have h1 := rfind'_obtain_prop evaln_ver_dom
  have h2 := h1.left
  have h4 := h1.right.right

  constructor
-- mp
  intro h
  have h3 : rfind'_obtain evaln_ver_dom = 0 := by
    contrapose h4
    simp at h4 ⊢
    use 0
    constructor
    exact zero_lt_of_ne_zero h4
    simp
    exact (Part.get_eq_iff_mem evalnbasedom).mp h
  simp [rfind'_obtain] at h3
  exact h3

-- mpr
  intro h
  have h3 : rfind'_obtain evaln_ver_dom = 0 := by
    simp [rfind'_obtain]
    exact h
  simp [h3] at h2
  exact Eq.symm ((fun {α} {o} {a} h ↦ (Part.eq_get_iff_mem h).mpr) evalnbasedom h2)
lemma unrpeq2 {O k cf x evalnbasedom evaln_ver_dom} :
((evaln O (k + 1) cf x).get evalnbasedom = 0)
↔
((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r=0) := by
  have h1 := nrfind'_obtain_prop' evaln_ver_dom
  have h2 := h1.left
  have h4 := h1.right.right

  constructor
-- mp
  intro h
  have h3 : rfind'_obtain (en2e evaln_ver_dom) = 0 := by
    contrapose h4
    simp at h4 ⊢
    use 0
    constructor
    exact zero_lt_of_ne_zero h4
    simp
    rw [show 0=(some 0).get (Option.isSome_some) from rfl] at h
    exact Option.get_inj.mp h
  simp [rfind'_obtain] at h3
  rw [evaln_eq_eval evaln_ver_dom]
  exact h3

-- mpr
  intro h
  have h3 : rfind'_obtain (en2e evaln_ver_dom) = 0 := by
    rw [evaln_eq_eval evaln_ver_dom] at h
    simp [rfind'_obtain]
    exact h
  simp [h3] at h2
  exact Option.get_of_eq_some evalnbasedom h2
lemma unrpeq0 {O cf k x y} :
(y ∈ usen O (rfind' cf) (k + 1) x)
↔
(
  ∃
  (evalnbasedom : (evaln O (k + 1) cf x).isSome)
  (evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome)
  ,
  -- (if (evaln O (k + 1) cf x).get evalnbasedom = 0 then usen O cf (k + 1) x
  (if (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r=0 then usen O cf (k + 1) x
  else
    (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
      some (((usen O cf (k + 1) x).get (en2un evalnbasedom)).max usen_indt)) = some y) := by
  constructor
-- mp
  intro h
  have evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome := un2en (Option.isSome_of_mem h)
  simp [usen] at h
  have xlek : x ≤ k := evaln_xles evaln_ver_dom
  simp [xlek] at h
  have usen_base_dom : (usen O cf (k+1) x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind usen_base_dom] at h
  have evaln_base_dom : (evaln O (k+1) cf x).isSome := by exact evaln_rfind_base evaln_ver_dom
  simp [isSome.bind evaln_base_dom] at h ⊢
  simp [evaln_base_dom]

  use evaln_ver_dom
  simp_all [@unrpeq2 O k cf x evaln_base_dom evaln_ver_dom]


-- mpr
  intro h
  rcases h with ⟨h1,h2,h3⟩
  simp at h3
  simp [usen]
  have xlek : x ≤ k := le_of_lt_succ (evaln_bound (Option.get_mem h1))
  simp [xlek]
  simp [isSome.bind (en2un h1)]
  simp [isSome.bind (h1)]
  simp_all [@unrpeq2 O k cf x h1 h2]

lemma unrpeq1 {x k O cf y} : (y ∈ (do
  guard (x ≤ k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) ⟪x.l, i+x.r⟫)
    max := Nat.max max usen_i
  max :Option ℕ)) ↔ (
  ∃
  (evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome),
  ((forIn (List.range ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r + 1)).reverse 0 fun i r ↦
    (usen O cf (k + 1 - i) (⟪x.l, i+x.r⟫)).bind fun usen_i ↦ some (ForInStep.yield (r.max usen_i))) =
  some y)
) := by
  simp
  constructor
  intro h
  have xlek : x ≤ k := by
    contrapose h;
    simp [h, Option.bind]
  simp [xlek] at h ⊢
  have evaln_ver_dom : (evaln O (k+1) (rfind' cf) x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind evaln_ver_dom] at h
  use evaln_ver_dom

  intro h
  rcases h with ⟨h1,h2⟩
  have xlek : x ≤ k := by
    simp [evaln] at h1
    contrapose h1;
    simp [h1]
  simp [xlek]
  simp [isSome.bind h1]
  exact h2
lemma lemlemlem2 {O k cf x roM1 asddom}
(a : ℕ)
(h1 : (evaln O (k + 1) cf x).isSome)
(u0 : (usen O cf (k + 1) x).isSome)
(u1 : (usen O cf (k + 1) ⟪x.l, x.r+1⟫).isSome)
(nrop2 : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) ⟪x.l, j+x.r⟫).isSome))
:
(forIn (List.range (roM1 + 1)).reverse (a.max ((usen O cf (k + 1) x).get (en2un h1))) fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + (x.r + 1)))).bind fun a ↦ some (ForInStep.yield (r.max a)))
    =
(forIn (List.range (roM1 + 1)).reverse (a.max ((usen O cf (k - roM1) ⟪x.l,roM1 + 1 + x.r⟫).get asddom))
    fun i r ↦
    (usen O cf (k + 1 - i) (⟪x.l, i+x.r⟫)).bind fun usen_i ↦ some (ForInStep.yield (r.max usen_i)))
 := by

  induction roM1 generalizing a with
  | zero =>
    simp [isSome.bind u0]
    simp [isSome.bind u1]
    ac_nf
    rw (config := {occs := .pos [2]}) [Nat.max_comm]
    apply congrArg
    apply congrFun
    apply congrArg
    apply usen_sing'

  | succ roM2 iihh =>

    simp (config := {singlePass := true}) [rr_indt]
    simp

    have urom : (usen O cf (k +1 - (roM2+1)) (Nat.pair x.l ((roM2+1) + 1 + x.r))).isSome := by
      have := nrop2 (roM2+1+1) (Nat.le_refl (roM2 + 1 + 1))
      simp at this
      apply usen_mono_dom _ this
      exact Nat.sub_le_add_right_sub k (roM2 + 1) 1
    simp at urom
    rw [add_assoc] at urom
    rw (config := {occs := .pos [3]}) [add_comm] at urom
    simp [isSome.bind urom]

    have urom2 : (usen O cf (k +1 - (roM2+1)) (Nat.pair x.l ((roM2+1) + x.r))).isSome := nrop2 (roM2+1) (le_add_right (roM2 + 1) 1)
    simp at urom2
    simp [isSome.bind urom2]

    have iihh1 := @iihh
      urom2
      (a.max ((usen O cf (k - roM2) (Nat.pair x.l (roM2 + 1 + (x.r + 1)))).get urom))
      (fun j hj ↦ (nrop2 j (le_add_right_of_le hj)))
    simp at iihh1
    clear iihh

    simp [Nat.max_comm]
    rw [iihh1]
    simp [Nat.max_comm]
    have : ((usen O cf (k - roM2) (Nat.pair x.l (roM2 + 1 + (x.r + 1)))).get urom) = ((usen O cf (k - (roM2 + 1)) (Nat.pair x.l (roM2 + 1 + 1 + x.r))).get asddom) := by
      have : (roM2 + 1 + (x.r + 1)) = (roM2 + 1 + 1 + x.r) := by exact Eq.symm (Nat.add_right_comm (roM2 + 1) 1 x.r)
      simp [this]
      exact usen_sing'
    rw [this]

theorem usen_rfind_prop2 {O k x y cf} :
(y ∈ usen O cf.rfind' (k + 1) x)
↔
y ∈ (do
  guard (x ≤ k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) ⟪x.l, i+x.r⟫)
    max := Nat.max max usen_i
  max :Option ℕ)
 := by
  rw [unrpeq0]
  rw [unrpeq1]
  constructor
  intro h
  rcases h with ⟨_,h2,h3⟩
  have h1 : (evaln O (k + 1) cf x).isSome := by exact (nrf (en2un h2)).right.right
  use h2


  let base' := 0
  rw [show 0=base' from rfl]
  have :
  (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (usen O cf (k + 1) x) else
    (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
      some (((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
    =
  (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (some (base'.max ((usen O cf (k + 1) x).get (en2un h1)))) else
    (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
      some (base'.max <| ((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
 := by
    simp [show base'=0 from rfl]
  rw [this] at h3
  clear this
  have asd : rfind'_obtain (en2e h2) = (evaln O (k + 1) cf.rfind' x).get h2 - x.r := by
    simp [rfind'_obtain]
    rw [evaln_eq_eval h2]
  revert h3
  revert asd
  generalize base'=base
  clear base'

  induction (evaln O (k + 1) cf.rfind' x).get h2 - x.r generalizing base h2 x with
  | zero =>
    simp
    simp [isSome.bind <| en2un h1]
  | succ roM1 ih =>
    simp
    simp at ih
    simp (config := {singlePass := true}) [rr_indt]
    simp
    intro hro h
    have usenindtdom : (usen O cf.rfind' k ⟪x.l, x.r+1⟫).isSome := by
      contrapose h; simp at h; simp [h]
    simp [isSome.bind usenindtdom] at h ih
    have evalnindtdom := un2en usenindtdom
    have nrfindt := nrf usenindtdom

    have nrop := nrfind'_obtain_prop' h2
    have nrop6 := nrfind'_obtain_prop_6' h2
    rw [hro] at nrop nrop6
    have nrop2 : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) ⟪x.l, j+x.r⟫).isSome) := fun j a ↦ en2un (nrop.right.left j a)
    have asddom : (usen O cf (k - roM1) ⟪x.l,roM1 + 1 + x.r⟫).isSome := by
      have := nrop2 (roM1+1) (le_rfl)
      simp at this
      exact this
    simp [isSome.bind asddom]

    have aux0 : (evaln O (k + 1) cf ⟪x.l, x.r+1⟫).isSome := Option.isSome_of_mem (evaln_mono (le_add_right k 1) (Option.get_mem nrfindt.right.right))
    have ih1 := @ih
      ⟪x.l, x.r+1⟫
      aux0
      (Option.isSome_of_mem (evaln_mono (le_add_right k 1) (Option.get_mem evalnindtdom)))
      aux0
      (base.max ((usen O cf (k+1) x).get (en2un h1)))
      ?_
      ?_
    rotate_left
    · simp [rfind'_obtain] at hro ⊢
      have := rfind'_obtain_prop_6 (en2e h2)
      simp [rfind'_obtain] at this
      rw [hro] at this
      have := this 1 (le_add_left 1 roM1)
      simp [Nat.add_comm] at this
      have := (Part.eq_get_iff_mem (en2e evalnindtdom)).mpr this
      rw [← this]
      rw [← add_assoc]
      simp only [reduceSubDiff, add_tsub_cancel_left]
    · rw [← h]
      if hroM1 : roM1=0 then
        simp [hroM1] at ⊢ nrop6 nrop
        have nropleft := nrop.left
        rw [add_comm] at nropleft
        have : ((usen O cf.rfind' k ⟪x.l, x.r+1⟫).get usenindtdom) = ((usen O cf (k + 1) ⟪x.l, x.r+1⟫).get (en2un aux0)) := by
          have := nrop6 1 (le_rfl)
          simp at this
          have : k=k-1+1 := by exact nrf_aux usenindtdom
          simp (config := {singlePass := true}) [this]
          simp [usen]
          simp [← this]
          simp [nropleft]
          exact usen_sing'
        rw [this]
      else
        clear ih
        simp [hroM1]
        have roM1M1: roM1 = roM1-1+1 := Eq.symm (succ_pred_eq_of_ne_zero hroM1)
        simp (config := {singlePass := true}) [roM1M1] at *
        have : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1 + 1))).isSome := by
          have := nrop6 (1+1) (le_add_left (1 + 1) (roM1 - 1))
          simp only [reduceSubDiff] at this
          have := Option.isSome_of_mem this
          ac_nf at this ⊢
          simp at this ⊢
          exact usen_mono_dom (show k-1 ≤ k from sub_le k 1) (en2un this)
        simp [isSome.bind this]
        apply congrArg
        apply congrArg

        have kkk : k=k-1+1 :=  nrf_aux usenindtdom
        simp [show (usen O cf.rfind' k ⟪x.l, x.r+1⟫) = (usen O cf.rfind' (k-1+1) ⟪x.l, x.r+1⟫) from congrFun
          (congrArg (usen O cf.rfind') kkk) ⟪x.l, x.r+1⟫]

        simp [usen]

        have auxdom1 : (evaln O k cf ⟪x.l, x.r+1⟫).isSome := by
          have := nrop.right.left 1 (le_add_left 1 (roM1 - 1 + 1))
          simp at this
          rwa [add_comm]
        have r1 : (evaln O k cf ⟪x.l, x.r+1⟫).get auxdom1 ≠ 0 := by
          have := nrop.right.right 1 (one_lt_succ_succ (roM1 - 1))
          simp at this
          rw [add_comm] at this
          contrapose this
          rw [← this]
          simp
        simp at this
        rw [add_comm] at this
        simp [← kkk]
        simp [r1]
        apply congr
        apply congr
        exact rfl
        exact usen_sing'
        exact usen_sing'

    simp at ih1
    have := @lemlemlem2 O k cf x roM1 (asddom) base h1 (en2un h1) (en2un aux0) (fun j a ↦ nrop2 j a)
    rw [this] at ih1
    rw [ih1]

-- mpr
  intro h
  rcases h with ⟨h2,h3⟩
  have h1 : (evaln O (k + 1) cf x).isSome := by exact (nrf (en2un h2)).right.right
  use h1
  use h2

  let base' := 0
  rw [show 0=base' from rfl] at h3
  have :
  (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (usen O cf (k + 1) x) else
    (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
      some (((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
    =
  (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (some (base'.max ((usen O cf (k + 1) x).get (en2un h1)))) else
    (usen O cf.rfind' (k + 1 - 1) ⟪x.l, x.r+1⟫).bind fun usen_indt ↦
      some (base'.max <| ((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
 := by
    simp [show base'=0 from rfl]
  rw [this]
  clear this

  have asd : rfind'_obtain (en2e h2) = (evaln O (k + 1) cf.rfind' x).get h2 - x.r := by
    simp [rfind'_obtain]
    rw [evaln_eq_eval h2]


  revert h3
  revert asd
  generalize base'=base
  clear base'

  induction (evaln O (k + 1) cf.rfind' x).get h2 - x.r generalizing base h2 x with
  | zero => simp [isSome.bind <| en2un h1]
  | succ roM1 ih =>
    simp at ih ⊢
    intro asd h
    simp (config := {singlePass := true}) [rr_indt] at h
    simp at h

    have nrop := nrfind'_obtain_prop' h2
    have nrop4 := nrfind'_obtain_prop_4' h2
    have nrop6 := nrfind'_obtain_prop_6' h2
    rw [asd] at nrop nrop6 nrop4
    have nrop2 : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) ⟪x.l, j+x.r⟫).isSome) := fun j a ↦ en2un (nrop.right.left j a)
    have asddom : (usen O cf (k - roM1) ⟪x.l,roM1 + 1 + x.r⟫).isSome := by
      have := nrop2 (roM1+1) (le_rfl)
      simp at this
      exact this
    simp [isSome.bind asddom] at h

    have usenindtdom : (usen O cf.rfind' k ⟪x.l, x.r+1⟫).isSome := by
      have := nrop4 1 (le_add_left 1 roM1)
      simp at this
      rw [add_comm]
      exact en2un this
    have evalnindtdom := un2en usenindtdom
    have nrfindt := nrf usenindtdom

    have aux0 : (evaln O (k + 1) cf ⟪x.l, x.r+1⟫).isSome := by
      have := nrop.right.left 1 (le_add_left 1 roM1)
      simp at this
      rw [add_comm] at this
      exact evaln_mono_dom (show k ≤ k+1 from le_add_right k 1) this

    have ih1 := @ih
      ⟪x.l, x.r+1⟫
      ?_
      ?_
      (base.max ((usen O cf (k+1) x).get (en2un h1)))
      ?_
      ?_
    rotate_left
    · exact Option.isSome_of_mem (evaln_mono (show k ≤ k+1 from le_add_right k 1) (Option.get_mem evalnindtdom))
    ·
      exact aux0
    ·
-- DUPLICATED
      simp [rfind'_obtain] at asd ⊢
      have := rfind'_obtain_prop_6 (en2e h2)
      simp [rfind'_obtain] at this
      rw [asd] at this
      have := this 1 (le_add_left 1 roM1)
      simp [Nat.add_comm] at this
      have := (Part.eq_get_iff_mem (en2e evalnindtdom)).mpr this
      rw [← this]
      rw [← add_assoc]
      simp only [reduceSubDiff, add_tsub_cancel_left]
    ·
      simp
      have := @lemlemlem2 O k cf x roM1 (asddom) base h1 (en2un h1) (en2un aux0) (fun j a ↦ nrop2 j a)
      rw [this]
      exact h

    simp at ih1
    rw [← ih1]

    have usenindtdom : (usen O cf.rfind' k ⟪x.l, x.r+1⟫).isSome := by
      have := nrop4 1 (le_add_left 1 roM1)
      rw [add_comm]
      exact en2un this
    simp [isSome.bind usenindtdom]
-- TODO : DUPLICATED (the below is duplciated from above)
    if hroM1 : roM1=0 then
      simp [hroM1]

      simp [hroM1] at ⊢ nrop6 nrop
      have nropleft := nrop.left
      rw [add_comm] at nropleft
      have : ((usen O cf.rfind' k ⟪x.l, x.r+1⟫).get usenindtdom) = ((usen O cf (k + 1) ⟪x.l, x.r+1⟫).get (en2un aux0)) := by
        have := nrop6 1 (le_rfl)
        simp at this
        have : k=k-1+1 := by exact nrf_aux usenindtdom
        simp (config := {singlePass := true}) [this]
        simp [usen]
        simp [← this]
        simp [nropleft]
        exact usen_sing'
      rw [this]
    else
      clear ih
      simp [hroM1]
      have roM1M1: roM1 = roM1-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero hroM1)
      simp (config := {singlePass := true}) [roM1M1] at *
      have : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1 + 1))).isSome := by
        have := nrop6 (1+1) (le_add_left (1 + 1) (roM1 - 1))
        simp only [reduceSubDiff] at this
        have := Option.isSome_of_mem this
        ac_nf at this ⊢
        simp at this ⊢
        exact usen_mono_dom (show k-1 ≤ k from sub_le k 1) (en2un this)
      simp [isSome.bind this]
      apply congrArg
      apply congrArg

      have kkk : k=k-1+1 := by exact nrf_aux usenindtdom
      simp [show (usen O cf.rfind' k ⟪x.l, x.r+1⟫) = (usen O cf.rfind' (k-1+1) ⟪x.l, x.r+1⟫) from congrFun
        (congrArg (usen O cf.rfind') kkk) ⟪x.l, x.r+1⟫]

      simp [usen]

      have auxdom1 : (evaln O k cf ⟪x.l, x.r+1⟫).isSome := by
        have := nrop.right.left 1 (le_add_left 1 (roM1 - 1 + 1))
        simp at this
        rwa [add_comm]
      have r1 : (evaln O k cf ⟪x.l, x.r+1⟫).get auxdom1 ≠ 0 := by
        have := nrop.right.right 1 (one_lt_succ_succ (roM1 - 1))
        simp at this
        rw [add_comm] at this
        contrapose this
        rw [← this]
        simp
      simp at this
      rw [add_comm] at this
      simp [← kkk]
      simp [r1]
      apply congr
      apply congr
      exact rfl
      exact usen_sing'
      exact usen_sing'
theorem usen_rfind_prop2' {O cf k x}
(h : (usen O (rfind' cf) (k + 1) x).isSome)
:
(usen O cf.rfind' (k + 1) x).get h
=
(do
  guard (x ≤ k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) ⟪x.l, i+x.r⟫)
    max := Nat.max max usen_i
  max :Option ℕ).get (Option.isSome_of_mem (usen_rfind_prop2.mp (Option.get_mem h))) := by
  have := usen_rfind_prop2.mp (Option.get_mem h)
  exact
    Eq.symm
      (Option.get_of_eq_some (Option.isSome_of_mem (usen_rfind_prop2.mp (Option.get_mem h))) this)
theorem usen_rfind_prop2'' {O k x cf} :
(usen O cf.rfind' (k + 1) x)=(do
  guard (x ≤ k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) ⟪x.l, i+x.r⟫)
    max := Nat.max max usen_i
  max :Option ℕ)
 := by
    apply Option.eq_of_eq_some
    intro y
    exact usen_rfind_prop2
theorem usen_xles {O c s x} (h : (usen O c (s + 1) x).isSome) : x ≤ s := le_of_lt_succ (usen_bound (Option.get_mem h))
theorem usen_sound {O} : ∀ {c s n x}, x ∈ usen O c s n → x ∈ use O c n
:= by
  intro c k n x h
  induction k,c using CodeNatK.induction generalizing x n with
  | h0 c => simp [usen] at h
  | hzero k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    exact h.right.symm
  | hsucc k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    exact h.right.symm
  | hleft k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    exact h.right.symm
  | hright k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    exact h.right.symm
  | horacle k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    simp [← h]
  | hpair k cf cg hf hg =>
    simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢
    obtain ⟨_, h⟩ := h
    rcases h with ⟨y, ef, z, eg, rfl⟩
    aesop? says
      simp_all only [Option.mem_def]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => apply Exists.intro
        on_goal 2 => apply And.intro
        on_goal 3 => {rfl
        }
        · simp_all only
        · simp_all only
  | hcomp k cf cg hf hg =>
    simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢
    -- obtain ⟨_, h⟩ := h
    -- rcases h with ⟨y, eg, ef⟩
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    -- #check @hg h2 h3
    refine ⟨h2,@hg n h2 h3,
            h4,evaln_sound h5,
            h6,@hf h4 h6 h7,
            ?_⟩
    subst h8
    exact Nat.max_comm h2 h6
  | hprec k cf cg hf hg ih =>
    simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢
    -- obtain ⟨_, h⟩ := h
    revert h
    induction' n.r with m IH generalizing x
    -- <;> simp [Option.bind_eq_some_iff]
    · intro h1
      replace h1 := h1.right
      simp at h1
      exact hf h1
    · simp
      intro hh1 hh
      simp [Option.bind_eq_some_iff] at hh
      rcases hh with ⟨hh,h3,h4,h5,h7,h8,h9⟩

      use h4
      constructor
      · exact evaln_sound h5
      · use hh
        constructor
        · have main := ih h3
          simp [use] at main
          exact main
        · exact ⟨h7, @hg (Nat.pair n.l (Nat.pair m h4)) h7 h8,h9⟩
  | hrfind k cf hfih =>
    simp [use]
    have := usen_rfind_prop2.mp h
    have urop1 := usen_rfind_prop h
    rcases urop1 0 (Nat.zero_le (rfind'_obtain (usen_rfind_prop_aux h))) with ⟨h1,h2⟩
    simp at h2

    rcases usen_dom_iff_evaln_dom.mp ⟨x,h⟩ with ⟨h7,h8⟩
    have h145: rfind'_obtain (usen_rfind_prop_aux h) = h7 - n.r := by
      simp [rfind'_obtain]
      simp [Part.eq_some_iff.mpr (evaln_sound h8)]
    simp [h145] at *
    simp_all
    have nlek : n ≤ k := usen_xles (Option.isSome_of_mem h)
    simp [nlek] at this

    use h7
    constructor
    exact evaln_sound h8

    revert this
    revert urop1
    generalize 0 = base
    -- revert 0
    induction h7 - n.r generalizing base with
    | zero =>
      -- todo: this simp call was from old mathlib
      simp? says simp only [nonpos_iff_eq_zero, forall_eq, tsub_zero, add_zero, pair_lr, zero_add, range_one,
        reverse_cons, reverse_nil, nil_append, forIn_cons, Option.pure_def, forIn_nil,
        Option.bind_eq_bind, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_bind_iff,
        Part.mem_some_iff, forall_exists_index]
      intro h3 h4 this
      use (ForInStep.yield (base.max h1))
      constructor
      use h1
      constructor
      exact @hfih (k+1) (le_rfl) n h1 h2
      rfl
      simp_all
    | succ nn ih =>
      simp (config := {singlePass := true}) [rr_indt]
      simp [-existsAndEq]
      intro urop1
      have aux0 : (∀ j ≤ nn, ∃ y, usen O cf (k + 1 - j) (Nat.pair n.l (n.r + j)) = some y) := by
        intro j jnn
        exact urop1 j (le_add_right_of_le jnn)

      rcases urop1 (nn+1) (Nat.le_refl (nn + 1)) with ⟨h3,h4⟩
      simp at h4
      ac_nf at h4 ⊢
      -- todo: this remove -existsAndEq
      simp [h4, -existsAndEq]

      have hf2 := @hfih (k-nn) (le_add_right_of_le (sub_le k nn)) (Nat.pair n.l (nn + (n.r+1))) h3 h4

      intro h5
      use (ForInStep.yield (base.max h3))
      constructor
      use h3
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
      simp [use,eval,Seq.seq]
      induction x.r with
      | zero => simp_all
      | succ xrM1 ih =>
      intro a
      simp_all only [Part.bind_dom, Part.map_Dom, exists_prop, exists_and_left, exists_true_left, forall_const]
    | rfind' cf hcf =>
      simp [use]
      intro x_1 h
      exact x_1
  intro h
  rcases eval_dom_imp_evaln h with ⟨s, hs⟩
  exact Part.mem_imp_dom <| usen_sound <| Option.get_mem <| en2un hs


abbrev e2u {O c x} : (eval O c x).Dom → (use O c x).Dom := use_dom_iff_eval_dom.mpr
abbrev u2e {O c x} : (use O c x).Dom → (eval O c x).Dom := use_dom_iff_eval_dom.mp
theorem use_rfind_prop {O cf n} (hu : (use O (rfind' cf) n).Dom):
∀j ≤ rfind'_obtain (u2e hu),
  (use O cf (Nat.pair n.l (n.r+j))).Dom
  -- and also the maximum of these is equal to the usen.
:= by
  intro j hjro
  rw [add_comm]
  exact e2u ((rfind'_obtain_prop (u2e hu)).right.left j hjro)

lemma lemlemlem {O cf nn h5 h57}
{a n : ℕ}
(h6 : h5 ∈ use O cf (Nat.pair n.l (nn + 1 + n.r)))
(rop3 : ∀ j ≤ nn + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
(h57dom : (use O cf n).Dom)
(h57def : h57=(use O cf n).get h57dom)
:
(forIn (List.range (nn + 1)).reverse (a.max h5) fun i r ↦
    (use O cf (Nat.pair n.l (i + n.r))).bind fun use_i ↦ Part.some (ForInStep.yield (r.max use_i)))
    =
(  forIn (List.range (nn + 1)).reverse (a.max (h57)) fun i r ↦
    (use O cf (Nat.pair n.l (i + (1 + n.r)))).bind fun use_i ↦ Part.some (ForInStep.yield (r.max use_i)))
 := by
  revert h6
  ac_nf
  induction nn generalizing h5 n a with
  | zero =>
    simp
    intro h6
    have : use O cf n = Part.some h57 := by
      exact Part.get_eq_iff_eq_some.mp (_root_.id (Eq.symm h57def))
    simp_all
    have := rop3 1 (le_rfl)
    simp [Part.Dom.bind this]
    simp [← (Part.eq_get_iff_mem this).mpr h6]
    ac_nf

  | succ nnn iihh =>
    -- sorry
    intro h6

    simp (config := {singlePass := true}) [rr_indt]
    simp

    ac_nf

    have dom1 : (use O cf (Nat.pair n.l (nnn + (n.r + 1)))).Dom := by
      have := rop3 (nnn+1) (le_add_right (nnn + 1) 1)
      ac_nf at this
      -- ac_nf at this
      -- rw [show n.r + (nnn + 1) = nnn + 1 + n.r from by grind] at this
      -- exact this
    simp [Part.Dom.bind dom1]
    have dom2 : (use O cf (Nat.pair n.l (nnn + (n.r + 2)))).Dom := by
      ac_nf at h6
      simp at h6
      exact Part.mem_imp_dom h6
    simp [Part.Dom.bind dom2]

    -- sorry

    have iihh1 := @iihh ((use O cf (Nat.pair n.l (nnn + (n.r + 1)))).get dom1) (a.max h5) (Nat.pair n.l (n.r)) ?_
    simp at iihh1
    clear iihh
    rotate_right
    ·
      intro j hj
      have := rop3 j (le_add_right_of_le hj)
      simpa
    ac_nf at iihh1
    have iihh2 := iihh1 h57dom h57def (Part.get_mem dom1)
    clear iihh1
    rw [iihh2]

    have : (use O cf (Nat.pair n.l (nnn + (n.r + 2)))).get dom2 = h5 := by
      simp [show (nnn + (n.r + 2)) = (nnn + 1 + (n.r + 1)) from by grind]
      exact Part.get_eq_of_mem h6 _
    rw [this]
    rw (config := {occs := .pos [2]}) [Nat.max_comm]
lemma lemlemlem3 {O cf nn h5 h57 kk x}
{a n use_steps : ℕ}
(h6 : h5 ∈ use O cf (Nat.pair n.l (nn + 1 + n.r)))
(rop3 : ∀ j ≤ nn + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
(h57dom : (use O cf n).Dom)
(h57def : h57=(use O cf n).get h57dom)
(aux123 : (use O cf n).Dom)
-- (i2 : usen O cf (i1 + 1) n = some ((use O cf n).get aux123))
(i2' : usen O cf (use_steps + 1) n = some ((use O cf n).get aux123))
(lolineq : kk + 1 ≤ use_steps )
(hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, usen O cf (k + 1) n = some x)
(hkk : (forIn (List.range (nn + 1)).reverse (a.max h57) fun i r ↦
    (usen O cf (kk + 1 - i) (Nat.pair n.l (i + (1 + n.r)))).bind fun a ↦ some (ForInStep.yield (r.max a))) =
  some x)
:
(  forIn (List.range (nn + 1)).reverse (a.max (h57)) fun i r ↦
    (usen O cf (kk+1-i) (Nat.pair n.l (i + (1 + n.r)))).bind fun use_i ↦ some (ForInStep.yield (r.max use_i)))
    =
((forIn (List.range (nn + 1)).reverse (a.max h5) fun i r ↦
    (usen O cf (use_steps + 1 - i) (Nat.pair n.l (i + n.r))).bind fun usen_i ↦
      some (ForInStep.yield (r.max usen_i))))
 := by
  revert h6
  induction nn generalizing h5 n a with
  | zero =>
    simp
    intro h6
    simp_all

    rcases hf h6 with ⟨g3,g4⟩
    have : ∃z,z ∈ (usen O cf (kk + 1) ⟪n.l, 1+n.r⟫) := by
      contrapose hkk
      simp at hkk
      have := Option.eq_none_iff_forall_ne_some.mpr hkk
      simp [this]
    rcases this with ⟨lmao3,lmao4⟩
    simp at lmao4
    simp [lmao4] at hkk
    simp [usen_sing lmao4 g4] at hkk
    subst hkk
    ac_nf

  | succ nnn iihh =>
    intro h6
    simp (config := {singlePass := true}) [rr_indt] at hkk ⊢
    simp at hkk ⊢

    rcases hf h6 with ⟨g3,g4⟩
    have : ∃z,z ∈ (usen O cf (kk - nnn) (Nat.pair n.l (nnn + 1 + (1 + n.r)))) := by
      contrapose hkk
      simp at hkk
      have := Option.eq_none_iff_forall_ne_some.mpr hkk
      simp [this]
    rcases this with ⟨lmao3,lmao4⟩
    simp at lmao4
    simp [lmao4] at hkk ⊢
    rw [add_assoc] at g4
    simp [usen_sing lmao4 g4] at *

    have : ∃z,z ∈ (usen O cf (use_steps - nnn) (Nat.pair n.l (nnn + 1 + n.r))) := by
      contrapose hkk
      simp at hkk
      have := Option.eq_none_iff_forall_ne_some.mpr hkk
      simp (config := {singlePass := true}) [rr_indt]
      have : (usen O cf (kk + 1 - nnn) (Nat.pair n.l (nnn + (1 + n.r)))) = Option.none := by
        rw [add_assoc] at this

        have ineq1: kk + 1 - nnn ≤ use_steps - nnn := by grind only [cases Or]
        simp [usen_mono_contra ineq1 this]
      simp [this]

    rcases this with ⟨g1,g2⟩
    simp at g2
    simp [g2]

    have dom1 : (use O cf (Nat.pair n.l (nnn + 1 + n.r))).Dom := by
      have := rop3 (nnn+1) (le_add_right (nnn + 1) 1)
      rw [show n.r + (nnn + 1) = nnn + 1 + n.r from by grind] at this
      exact this

    have iihh1 := @iihh ((use O cf (Nat.pair n.l (nnn + 1 + n.r))).get dom1) (a.max h5) (Nat.pair n.l (n.r)) ?_
    simp at iihh1
    clear iihh
    rotate_right
    ·
      intro j hj
      have := rop3 j (le_add_right_of_le hj)
      simpa

    have iihh2 := iihh1 h57dom h57def h57dom i2' ?_ ?_
    clear iihh1
    rotate_left
    ·
      rw (config := {occs := .pos [2]}) [Nat.max_comm]
      exact hkk
    · exact Part.get_mem dom1
    ·
      rw (config := {occs := .pos [2]}) [Nat.max_comm]
      have : g1 = ((use O cf (Nat.pair n.l (nnn + 1 + n.r))).get dom1) := by
        exact (Part.eq_get_iff_mem dom1).mpr (usen_sound g2)
      rw [this]
      exact iihh2
lemma eval_rfind_prop5 {O cf y x} :
x∈eval O (rfind' cf) y→y.r ≤ x := by
  simp [eval]
  grind

theorem usen_complete_prec
{O : ℕ → ℕ}
{cf cg : Code}
{hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, x ∈ usen O cf (k + 1) n}
{hg : ∀ {n x : ℕ}, x ∈ use O cg n → ∃ k, x ∈ usen O cg (k + 1) n}
{n x : ℕ}
{h : x ∈ use O (cf.prec cg) n} :
∃ k, x ∈ usen O (cf.prec cg) (k + 1) n := by
    simp [use, usen, pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    revert h
    generalize n.l = n₁; generalize n.r = n₂
    -- induction' n₂ with m IH generalizing x n <;> simp [Option.bind_eq_some_iff]
    induction' n₂ with m IH generalizing x n
    · intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    · -- intro y hy hx
      intro h
      simp at h
      rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
      rcases IH h4 with ⟨k₁, nk₁, hk₁⟩
      rcases hg h6 with ⟨k₂, hk₂⟩

      refine ⟨(max k₁ k₂).succ,Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁,
            ?_
            ⟩

      simp only [succ_eq_add_one]
      subst h7
      simp_all only [Option.mem_def, sup_le_iff]
      obtain ⟨left, right⟩ := nk₁

      have aux1 : h5 ∈ (usen O cg (max k₁ k₂ + 1 + 1) (Nat.pair n₁ (Nat.pair m h1))) := by
        simp
        have : k₂+1 ≤ max k₁ k₂ + 1 + 1 :=  by
          apply Nat.add_le_add_iff_right.mpr
          apply le_add_right_of_le
          apply le_sup_right
        exact usen_mono this hk₂
      have aux2 : h3 ∈ (usen O (cf.prec cg) (max k₁ k₂ + 1) (Nat.pair n₁ m)) := by
        -- have aux_aux : Nat.pair n₁ m ≤ k₁ := by exact right
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
theorem usen_complete_rfind'
(O : ℕ → ℕ)
(cf : Code)
(hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, x ∈ usen O cf (k + 1) n)
(n x : ℕ)
(h : x ∈ use O cf.rfind' n) :
∃ k, x ∈ usen O cf.rfind' (k + 1) n := by
  sorry
-- set_option maxHeartbeats 1000000 in
theorem usen_complete {O} {c n x} : x ∈ use O c n ↔ ∃ s, x ∈ usen O c s n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => usen_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ usen O  c (k + 1) n
  · exact ⟨k + 1, h⟩

  induction c generalizing n x with
  | pair cf cg hf hg =>
    simp [use, usen, pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    simp [use, usen, pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
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
      rcases evaln_complete.mp hx2 with ⟨kk,hkk⟩
      rw [evaln_sing hkk hb]
      exact evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hb
    · refine ⟨_,usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂,
      (by subst hx5; exact Nat.max_comm hx3 y) ⟩
  | prec cf cg hf hg => exact usen_complete_prec O cf cg hf hg n x h
  | rfind' cf hf =>
    simp [use] at h
    suffices ∃k,x ∈ (do
  guard (n ≤ k);
  let guard ← evaln O (k+1) (rfind' cf) n;
  let ro := guard - n.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) (Nat.pair n.l (i+n.r)))
    max := Nat.max max usen_i
  max :Option ℕ) from by
      rcases this with ⟨k,hk⟩
      use k
      exact usen_rfind_prop2.mpr hk
    simp

    generalize 0=a at h ⊢
    rcases h with ⟨h1,h2,h3⟩

    have rogeq : n.r ≤ h1 := eval_rfind_prop5 h2
    rw [show h1=h1-n.r+n.r from by simp [rogeq]] at h2
    clear rogeq

    have hdom1 := Part.dom_iff_mem.mpr ⟨h1-n.r+n.r,h2⟩
    have hdom : (use O cf.rfind' n).Dom := use_dom_iff_eval_dom.mpr hdom1
    have rop := rfind'_obtain_prop hdom1
    have rop4 := rfind'_obtain_prop_4 hdom1
    have rop6 := rfind'_obtain_prop_6 hdom1
    have urop1 := use_rfind_prop hdom
    have hrop: rfind'_obtain (u2e hdom) = h1 - n.r := by
      simp [rfind'_obtain]
      simp [Part.eq_some_iff.mpr h2]
    simp [hrop] at *
    clear hrop

    revert h3
    revert h2
    revert urop1
    revert rop6
    revert rop4
    revert rop

    induction h1-n.r generalizing a n with
    | zero =>
      simp_all only [zero_add, pair_lr, nonpos_iff_eq_zero, forall_eq, not_lt_zero',
        IsEmpty.forall_iff, implies_true, and_true, add_zero, range_one, reverse_cons, reverse_nil,
        nil_append, forIn_cons, Part.pure_eq_some, forIn_nil, Part.bind_eq_bind, Part.mem_bind_iff,
        Part.mem_some_iff, forall_exists_index, and_imp, forall_const]
      intro urop1 rop1 h2 rop6 h4 h5 h6 h7 h8

      rcases evaln_complete.mp h2 with ⟨h9,h10⟩
      rcases hf h6 with ⟨h14,h15⟩
      rcases usen_dom_iff_evaln_dom.mp ⟨h5,h15⟩ with ⟨h16,h17⟩

      have nlek : (n ≤ (h9 - 1).max (h14 + 1)) := by
        contrapose h15
        simp at h15
        intro h16
        have contra := usen_bound h16
        have h15 := h15.right
        have : n<n := by
          exact Nat.lt_trans contra h15
        simp at this

      use Nat.max (h9-1) (h14+1)
      -- simp [nlek]
      simp_all
      rcases usen_dom_iff_evaln_dom.mpr ⟨n.r,h10⟩ with ⟨h12,h13⟩
      have : (h9) ≤ (h9 - 1).max (h14 + 1) + 1 := le_add_of_sub_le (Nat.le_max_left (h9 - 1) (h14 + 1))
      have aux2 := evaln_mono this h10
      clear this
      simp at aux2
      simp [aux2]
      have : (h14 + 1) ≤ (h9 - 1).max (h14 + 1) + 1 := by
        simp only [add_le_add_iff_right, le_sup_iff, le_add_iff_nonneg_right, _root_.zero_le,
          or_true]

      have aux0 := usen_mono this h15
      simp at aux0
      simp [aux0]

    | succ nn ih =>
      simp (config := {singlePass := true}) [rr_indt]
      simp only [Part.pure_eq_some, Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff,
        Option.pure_def, Option.bind_eq_bind, forall_exists_index, and_imp]
      intro urop1 rop1 rop2 rop4 rop6 rop3 h2 h3 h5 h6 h7 h8

      have rop10 := rop1 1 (le_add_left 1 nn)
      have rop11 := e2u rop10
      have rop40 := rop4 1 (le_add_left 1 nn)
      have rop41 := e2u rop40

      have h57dom := rop3 0 (le_add_left 0 (nn + 1))
      simp at h57dom
      let h57 := (use O cf n).get h57dom

      have ih1 := @ih ⟪n.l, 1+n.r⟫ (a.max h57) (rop40) rop41 ?_ ?_ ?_ ?_ ?_
      clear ih
      rotate_right 5
      · simp
        constructor
        -- rw [← add_assoc]
        ac_nf at urop1 ⊢
        -- exact urop1
        constructor
        intro j hj
        have := rop1 (j+1) (Nat.add_le_add_right hj 1)
        rw [← add_assoc]
        exact rop1 (j+1) (Nat.add_le_add_right hj 1)
        intro j hj
        rw [← add_assoc]
        exact rop2 (j+1) (Nat.add_le_add_right hj 1)
      · simp
        intro j hj
        -- ac_nf
        rw [← add_assoc]
        exact rop4 (j+1) (Nat.add_le_add_right hj 1)
      ·
        simp
        intro j hj
        rw [← add_assoc]
        rw [← add_assoc]
        exact rop6 (j+1) (Nat.add_le_add_right hj 1)
      ·
        simp
        intro j hj
        rw [add_comm]
        rw [← add_assoc]
        exact e2u (rop1 (j+1) (Nat.add_le_add_right hj 1))
      ·
        simp
        rw [← add_assoc]
        exact rop6 (1) (le_add_left 1 nn)

      simp_all
      have lemlem := @lemlemlem O cf nn h5 h57 a n h6 rop3 (h57dom) (rfl)

      have : (x ∈
    forIn (List.range (nn + 1)).reverse (a.max h57) fun i r ↦
      (use O cf (Nat.pair n.l (i + (1 + n.r)))).bind fun use_i ↦ Part.some (ForInStep.yield (r.max use_i))) := by
          rw [lemlem] at h8
          exact h8

      simp [this] at ih1
      rcases ih1 with ⟨kk,hkk⟩

      have aux123 := rop3 0 (le_add_left 0 (nn + 1))
      simp at aux123
      have aux124 : (use O cf n).get aux123 ∈ use O cf n := by exact Part.get_mem aux123
      rcases (hf aux124) with ⟨i1,i2⟩

      -- simp
      have : ∃z,z∈ (evaln O (kk + 1) cf.rfind' ⟪n.l, 1+n.r⟫) := by
        contrapose hkk
        simp at hkk
        have := Option.eq_none_iff_forall_ne_some.mpr hkk
        simp [this]
      -- simp?
      rcases this with ⟨h21,h22⟩
      clear this

      rcases evaln_complete.mp (rop6 1 (le_add_left 1 nn)) with ⟨h19,h20⟩
      have hh22 := evaln_sing h22 h20
      simp at h22
      rw [h22] at hkk
      rw [hh22] at hkk

      rcases evaln_complete.mp h2 with ⟨h9,h10⟩
      rcases hf h6 with ⟨h14,h15⟩
      rcases usen_dom_iff_evaln_dom.mp ⟨h5,h15⟩ with ⟨h16,h17⟩

      let use_steps := (Nat.max (Nat.max (h9) (h14+1) + nn) (Nat.max (kk+1) (i1))).max n
      use use_steps

      have nlek : (n ≤ use_steps) := by exact Nat.le_max_right _ _

      have nlek2 : (Nat.pair n.l (1 + n.r) ≤ kk) := by
        contrapose hkk
        simp [hkk,Option.bind]

      simp [nlek] at ⊢
      simp [nlek2] at hkk

      have : nn + 1 + n.r - (1 + n.r) + 1 = nn + 1 := by
        rw [add_assoc]
        rw [Nat.add_sub_cancel_right nn (1+n.r)]
      rw [this] at hkk
      clear this

      have : (evaln O ((use_steps)+1) cf.rfind' n) = some (nn + 1 + n.r) := by
        simp at h10
        rw [← h10]
        apply evaln_mono' (Option.isSome_of_mem h10) _
        grind
      simp [this]

      have : (usen O cf (use_steps - nn) (Nat.pair n.l (nn + 1 + n.r))) = some h5 := by
        rw [← h15]
        apply usen_mono' (Option.isSome_of_mem h15) _
        grind
      simp [this]

      have aux1 : usen O cf (use_steps + 1) n = some ((use O cf n).get h57dom) := by
        rw [← i2]
        apply usen_mono' (Option.isSome_of_mem i2) _
        grind
      have aux2 :  kk + 1 ≤ use_steps := by
        grind
      have lemlem2 := @lemlemlem3 O cf nn h5 h57 kk x a n use_steps (h6) (fun j a ↦ rop3 j a) (h57dom) rfl h57dom aux1 aux2 (fun a ↦ hf a) (hkk)
      simp_all only [Option.mem_def]
  | oracle =>
    simp [use] at h
    use (n+1)
    simp [usen]
    exact h.symm
  | _ =>
    simp [use] at h
    use (n+1)
    simp [usen]
    exact h.symm

end usen_complete
