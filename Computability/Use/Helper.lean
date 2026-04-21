/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Basic
import Computability.Helper.Partial
import Computability.Helper.List
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

section evaln_lemmas
-- general lemmas for evaln
lemma evaln_sing {O s1 c x a s2 b}
    (h1 : a ∈ (evaln O s1 c x)) (h2 : b ∈ (evaln O s2 c x)) : a=b := by
  cases Classical.em (s1 ≤ s2) with
  | inl h =>
    have := evaln_mono h h1
    simp_all only [Option.mem_def, Option.some.injEq]
  | inr h =>
    have := evaln_mono (Nat.le_of_not_ge h) h2
    simp_all only [Option.mem_def, Option.some.injEq]
lemma evaln_sing' {O s1 c x h1 s2 h2} :
    (evaln O s1 c x).get h1 = (evaln O s2 c x).get h2 :=
  evaln_sing (Option.get_mem h1) (Option.get_mem h2)
lemma evaln_sing'' {O s1 c x s2}
    (h1 : (evaln O s1 c x).isSome)
    (h2 : (evaln O s2 c x).isSome) :
    (evaln O s1 c x) = (evaln O s2 c x) :=
  Option.get_inj.mp (@evaln_sing' O s1 c x h1 s2 h2)
lemma evaln_mono' {O s1 c x s2}
    (h1 : (evaln O s1 c x).isSome)
    (h2 : s1 ≤ s2) :
    (evaln O s2 c x) = (evaln O s1 c x) := by
  have := evaln_mono h2 (Option.get_mem h1)
  simp_all only [Option.mem_def, Option.some_get]
lemma evaln_sG1 {O s c x} (h : (evaln O s c x).isSome) : s=s-1+1 := by
  have : s ≠ 0 := by
    contrapose h
    simp [h,evaln]
  exact Eq.symm (succ_pred_eq_of_ne_zero this)
lemma evaln_xles {O s c x} (h : (evaln O (s + 1) c x).isSome) : x ≤ s :=
  le_of_lt_succ (evaln_bound (Option.get_mem h))
lemma evaln_xles' {O s c x} (h : (evaln O s c x).isSome) : x ≤ s-1 := by
  rw [evaln_sG1 h] at h
  exact evaln_xles h
abbrev en2e {O s c x} : (evaln O s c x).isSome → (eval O c x).Dom := by
  intro h
  have : (evaln O s c x).get h ∈ evaln O s c x := by exact Option.get_mem h
  have := evaln_sound (Option.get_mem h)
  exact Part.dom_iff_mem.mpr (⟨(evaln O s c x).get h,this⟩)

lemma rfind'_geq_xr {O cf x} (h : (eval O (rfind' cf) x).Dom) : (eval O cf.rfind' x).get h ≥ x.r :=
  by simp [eval]

theorem evaln_eq_eval {O s c x} (h : (evaln O s c x).isSome) :
    (evaln O s c x).get h = (eval O c x).get (en2e h) :=
  Eq.symm (Part.get_eq_of_mem (evaln_sound (Option.get_mem h)) (en2e h))
lemma nrfind'_geq_xr {O s cf x} (h : (evaln O (s) (rfind' cf) x).isSome) :
    (evaln O (s) (rfind' cf) x).get h ≥ x.r := by
  rw [evaln_eq_eval]
  exact rfind'_geq_xr (en2e h)
end evaln_lemmas

section rfind_obtain
def rfind'_obtain {O cf x} (h : (eval O (rfind' cf) x).Dom) : ℕ :=
  ((eval O (rfind' cf) x).get h) - x.r
def nrfind'_obtain {O s cf x} (h : (evaln O s (rfind' cf) x).isSome) : ℕ :=
  ((evaln O s (rfind' cf) x).get h)-x.r
theorem nrop_eq_rop {O s cf x} (h : (evaln O s (rfind' cf) x).isSome) :
    nrfind'_obtain h = rfind'_obtain (en2e h) := by
  unfold nrfind'_obtain
  unfold rfind'_obtain
  rw [evaln_eq_eval h]

theorem evaln_rfind_as_eval_rfind' {O s c x}
    (h : (evaln O s (rfind' c) x).isSome) :
    ((evaln O s (rfind' c) x).get h) ∈
    ((Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun x => x = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) x) := by
  have := evaln_sound (Option.get_mem h)
  simpa only [eval] using this
theorem evaln_rfind_base {O s cf x} (h : (evaln O (s + 1) (rfind' cf) x).isSome) :
    (evaln O (s + 1) (cf) x).isSome := by
  contrapose h
  simp? [evaln] says
    simp only [evaln, unpaired, unpair1_to_l, unpair2_to_r, pair_lr, Option.pure_def,
      Option.bind_eq_bind, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      Option.bind_eq_none_iff, Option.guard_eq_some', forall_const]
  intro h1 h2 h3
  simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  rw [h] at h3
  contradiction
theorem evaln_rfind_indt {O s cf x}
    (h1 : (evaln O (s + 1) (rfind' cf) x).isSome)
    (h2 : (evaln O (s + 1) (cf) x).isSome)
    (h3 : (evaln O (s + 1) (cf) x).get h2 ≠ 0) :
    (evaln O s cf.rfind' ⟪x.l, x.r+1⟫).isSome := by
  contrapose h1
  simp at h1
  simp? [evaln] says
    simp only [evaln, unpaired, unpair1_to_l, unpair2_to_r, pair_lr, Option.pure_def,
      Option.bind_eq_bind, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      Option.bind_eq_none_iff, Option.guard_eq_some', forall_const]
  intro h4 h5 h6
  simp_all only [Option.get_some, ne_eq, ↓reduceIte]
theorem evaln_rfind_as_eval_rfind {O s c x}
    (h : (evaln O (s + 1) (rfind' c) x).isSome) :
    ((evaln O (s + 1) (rfind' c) x).get h) ∈
    ((Nat.unpaired fun a m =>
    (Nat.rfind fun n => (fun x => x = 0) <$> evaln O ((s + 1)-n) c
      (Nat.pair a (n + m))).map (· + m)) x) := by
  have := evaln_rfind_as_eval_rfind' h
  simp_all only [unpaired, unpair2_to_r, unpair1_to_l, Part.map_eq_map, Part.mem_map_iff, mem_rfind,
    decide_eq_true_eq, exists_eq_right, decide_eq_false_iff_not, Part.mem_ofOption, Option.mem_def]
  -- rcases this with ⟨h1, ⟨h2,h3⟩, h4⟩
  rcases this with ⟨h1, ⟨_c0, h3⟩, h4⟩
  clear _c0
  -- rcases this with ⟨h1, _c0, h4⟩
  use h1
  constructor
  constructor
  · have := evaln_sound (Option.get_mem h)
    have : evaln O (s + 1 - h1) c (Nat.pair x.l (h1 + x.r)) = some 0 := by
      clear h3
      clear this
      induction h1 generalizing x s with
      | zero =>
        simp only [zero_add, tsub_zero, pair_lr] at ⊢ h4
        simp? [evaln]  at h4 says
          simp only [evaln, unpaired, unpair1_to_l, unpair2_to_r, pair_lr, Option.pure_def,
            Option.bind_eq_bind, Option.get_bind] at h4
        contrapose h4
        have hh := evaln_rfind_base h
        let (eq:=rwbase) base := (evaln O (s + 1) c x).get hh
        simp only [← rwbase, ne_eq]
        have : base ≠ 0 := by
          contrapose h4;
          rw [h4] at rwbase
          rw [show 0=(Option.some 0).get (Option.isSome_some) from rfl] at rwbase
          exact Option.get_inj.mp rwbase.symm
        simp only [this, ↓reduceIte, ne_eq]
        have halt2 := evaln_rfind_indt h hh this
        have := nrfind'_geq_xr halt2
        simp only [pair_r, ge_iff_le] at this
        exact Nat.ne_of_lt this
      | succ roM1 ih =>
        have := @ih (s-1) ⟪x.l, x.r+1⟫ ?_ ?_
        all_goals
          have hh := evaln_rfind_base h
          let base := (evaln O (s + 1) c x).get hh
          have rwbase : (evaln O (s + 1) c x).get hh =base := rfl
        · 
          simp only [pair_l, pair_r, reduceSubDiff] at this ⊢
          cases s with
          | zero => simp_all [evaln]
          | succ n =>
            simp only [add_tsub_cancel_right] at this
            ac_nf at this ⊢
        · contrapose h4
          simp at h4
          simp [evaln]
          simp [rwbase]

          if h3 : base=0 then simp [h3] else
          simp [h3]
          have halt2 := evaln_rfind_indt h hh h3
          cases s with
          | zero => simp [evaln] at halt2
          | succ sM1 => simp_all
        ·
          simp only [pair_r]
          cases s with
          | zero => simp [evaln] at h4 ⊢
          | succ sM1 =>
            simp
            simp [evaln] at h4
            simp [rwbase] at h4
            cases hbase : base with
            | zero  => simp [hbase] at h4
            | succ n =>
              simp [hbase] at h4
              simp [evaln]
              ac_nf at h4 ⊢
    exact this
  all_goals
    have halt_base := evaln_rfind_base h
    -- let (eq:=hbase_val) base_val := (evaln O (s + 1) c x).get halt_base
    let base_val := (evaln O (s + 1) c x).get halt_base
    have rwasd : (evaln O (s + 1) c x).get halt_base = base_val := rfl
  ·
    intro j hj

    -- clear h2
    -- clear h4
    induction j generalizing x s h1 with
    | zero =>
      simp only [tsub_zero, zero_add, pair_lr]
      use base_val
      constructor
      · exact Option.eq_some_of_isSome halt_base
      have := h3 hj
      simp at this
      -- simp_all only [ne_eq, base_val]
      rcases this with ⟨g1,g2,g3⟩
      have eqe := evaln_eq_eval halt_base
      have : eval O c x = Part.some g1 := by exact Part.eq_some_iff.mpr g2
      simp [this] at eqe
      simp [eqe] at rwasd
      rw [rwasd] at g3
      exact g3
    | succ jM1 ih =>
      -- have ih1 := @ih (s-1) (Nat.pair x.l (1+x.r)) ?_ ?_ ?_ ?_ ?_
      have ih_aux_0 : (evaln O (s - 1 + 1) c.rfind' (Nat.pair x.l (1 + x.r))).isSome = true := by
        -- why is this true?
        -- because h1 (=ro) is >1 so the next step must be defined
        -- so h1 is at least 2
        simp [evaln] at h4
        simp [rwasd] at h4
        cases hb : base_val with
        | zero =>
          simp [hb] at h4
          simp_all only [not_lt_zero', not_isEmpty_of_nonempty, IsEmpty.exists_iff, implies_true]
        | succ base_valM1 =>
          simp [hb] at h4
          have halt2 := evaln_rfind_indt h halt_base (by simp_all)
          cases s with
          | zero => simp [evaln] at halt2
          | succ sM1 =>
            simp_all
            rw (config := {occs := .pos [2]}) [add_comm]

            have : evaln O (sM1 + 1) c.rfind' ⟪x.l, x.r+1⟫ = some (h1+x.r) := by
              simp_all
            exact Option.isSome_of_mem this
      have ih_aux_1 :
          h1 + x.r = (evaln O (s - 1 + 1) c.rfind' (Nat.pair x.l (1 + x.r))).get ih_aux_0 := by
        simp [evaln] at h4
        simp [rwasd] at h4
        if hb : base_val=0 then
          simp [hb] at h4
          rw [h4] at hj
          contradiction
        else
          simp [hb] at h4
          have halt2 := evaln_rfind_indt h halt_base (by simp_all)
          cases s with
          | zero => simp [evaln] at halt2
          | succ sM1 => simpa [add_comm]
      replace ih := @ih (s-1) (Nat.pair x.l (1+x.r))
        ih_aux_0 (h1-1) ?_ ?_
        (evaln_rfind_base ih_aux_0)
        rfl
        (lt_sub_of_add_lt hj)
      rotate_left
      · simp only [pair_r]
        rw [show h1 - 1 + (1 + x.r) = h1+x.r from by grind]
        exact ih_aux_1
      ·
        intro j hjro
        simp only [pair_l, pair_r]
        rw [← add_assoc]
        exact @h3 (j+1) (add_lt_of_lt_sub hjro)
      simp only [pair_l, pair_r, reduceSubDiff] at ih ⊢
      rcases ih with ⟨g1,g2,g3⟩
      cases s with
      | zero => simp_all [evaln]
      | succ sM1 =>
        simp at g2
        rw [add_assoc]
        aesop? says simp_all only [Option.some.injEq, exists_eq_left', not_false_eq_true]
  simp_all only
-- #exit
theorem evaln_rfind_as_eval_rfind_reverse {O s c x}
    (h : ((Nat.unpaired fun a m =>
    (Nat.rfind fun n => (fun x => x = 0) <$> evaln O ((s + 1) - n) c (Nat.pair a (n + m))).map
    (· + m)) x).Dom) :
    ((evaln O (s + 1) (rfind' c) x)).isSome := by
  simp at h
  rcases h with ⟨h1,h2,h3⟩
  induction h1 generalizing s x with
  | zero =>
    simp [evaln]
    have xles : x ≤ s := by
      simp at h2
      contrapose h2
      simp at h2
      have contra : s + 1 ≤ x := h2
      intro he
      have := evaln_bound he
      replace : x<x := Nat.lt_of_lt_of_le this h2
      simp at this
    simp [xles]
    simp_all
  | succ n ih =>
    have h30 := @h3 0 (zero_lt_succ n)
    simp at h30
    simp at h2
    have : s ≠ 0 := by
      contrapose h2
      simp [h2,evaln]
    have sss : s=s-1+1 := by
      exact Eq.symm (succ_pred_eq_of_ne_zero this)
    have ih1 := @ih (s-1) ⟪x.l, x.r+1⟫ ?_ ?_
    simp [evaln]
    -- have := @ih (x) ?_ ?_
    rotate_left
    · simp
      rw [← sss]
      ac_nf at h2 ⊢
    · simp
      intro j hj
      have := @h3 (j+1) (Nat.add_lt_add_right hj 1)
      simp at this
      rw [← sss]
      ac_nf at this ⊢
    have xles : x ≤ s := evaln_xles h30
    simp [xles]

    have := @h3 0 (zero_lt_succ n)
    simp at this
    simp [isSome.bind this]
    if h4 : (evaln O (s + 1) c x).get this = 0 then
      simp [h4]
    else
      simp [h4]
      rw [sss]
      exact ih1
theorem evaln_rfind_as_eval_rfind_reverse' {O s c x}
    (h : ((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> evaln O (s - n) c
    (Nat.pair a (n + m))).map (· + m)) x).Dom) :
    ((evaln O s (rfind' c) x)).isSome := by
  have : s ≠ 0 := by
    contrapose h
    rw [h]
    simp [evaln]
  have : s=s-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero this)

  rw [this] at h ⊢
  exact evaln_rfind_as_eval_rfind_reverse h
theorem nrfind'_obtain_prop {O s cf x}
    (h : (evaln O (s + 1) (rfind' cf) x).isSome) :
    0 ∈ (evaln O (s + 1-(nrfind'_obtain h)) cf (Nat.pair x.l (nrfind'_obtain h+x.r)))
    ∧ (∀ j ≤ nrfind'_obtain h, (evaln O (s + 1-j) cf  ⟪x.l, j+x.r⟫).isSome)
    ∧ (∀ j < nrfind'_obtain h, ¬0 ∈ (evaln O (s + 1-j) cf ⟪x.l, j+x.r⟫)) := by
  let (eq := hrf) rf := (evaln O (s + 1) cf.rfind' x).get h
  have aux0 : rf ∈ evaln O (s + 1) cf.rfind' x := Option.get_mem h
  have := evaln_rfind_as_eval_rfind h
  rw [← hrf] at this; clear hrf
  replace := this
  simp at this

  rcases this with ⟨ro,⟨lll,rrr⟩,ha⟩
  have aux4: nrfind'_obtain h = ro := Eq.symm (Nat.eq_sub_of_add_eq ha)

  constructor
  ·
    rw [aux4]
    exact lll
  rw [aux4]
  constructor
  ·
    intro j hja
    cases lt_or_eq_of_le hja with
    | inl hja =>
      rcases rrr hja with ⟨witness,hwitness,_⟩
      exact Option.isSome_of_mem hwitness
    | inr hja =>
      rw [hja]
      exact Option.isSome_of_mem lll
  · 
    intro j hja
    rcases rrr hja with ⟨witness,⟨hwitness_1,hwitness_2⟩⟩
    exact opt_ne_of_mem_imp_not_mem hwitness_1 hwitness_2
theorem nrfind'_obtain_prop' {O s cf x} (h : (evaln O (s + 1) (rfind' cf) x).isSome) :
    0 ∈ (evaln O (s + 1-(rfind'_obtain (en2e h))) cf (Nat.pair x.l (rfind'_obtain (en2e h)+x.r))) ∧
    (∀ j ≤ rfind'_obtain (en2e h), (evaln O (s + 1-j) cf  ⟪x.l, j+x.r⟫).isSome) ∧
    (∀ j < rfind'_obtain (en2e h), ¬0 ∈ (evaln O (s + 1-j) cf ⟪x.l, j+x.r⟫)) := by
  rw [← nrop_eq_rop h]
  exact nrfind'_obtain_prop h
private lemma mpp_leq {j ro} {x : ℕ} (hjro : j ≤ ro) : (ro - j + (j + x)) = ro + x := by
  simp only [hjro, ← add_assoc,Nat.sub_add_cancel]
theorem nrfind'_obtain_prop_4 {O s cf x} (h : (evaln O (s + 1) (rfind' cf) x).isSome) :
∀ j ≤ nrfind'_obtain h, (evaln O (s + 1-j) (rfind' cf) ⟪x.l, j+x.r⟫).isSome := by
  have rop := nrfind'_obtain_prop h
  let (eq := hro) ro := nrfind'_obtain h
  simp [← hro] at rop ⊢
  rcases rop with ⟨rop1,rop2,_⟩

  intro j hjro
  apply evaln_rfind_as_eval_rfind_reverse' ?_
  simp
  use ro-j
  constructor
  · rw [mpp_leq hjro]
    rw [Nat.sub_sub_sub_cancel_right hjro]
    exact rop1
  intro m hm
  rw [← (Nat.add_assoc m j x.r)]
  have := rop2 (m+j) (le_of_succ_le (add_lt_of_lt_sub hm))
  rwa [Eq.symm (Simproc.sub_add_eq_comm (s + 1) m j)]
private lemma mem_shambles {x} {o : Option ℕ} {p : Part ℕ} (h0 : x∉o) (h1 : o.isSome) (h2 : o.get h1∈p) : (x∉p) := by
  contrapose h2
  rw [Part.eq_some_iff.mpr h2] -- `p` => `Part.some x`
  simp
  have : o ≠ some x := h0
  contrapose this
  rw [← this]
  exact Option.eq_some_of_isSome h1
theorem nrfind'_prop {O s cf x y} (h : (evaln O s (rfind' cf) x).isSome) :
    y+x.r ∈ (evaln O s (rfind' cf) x) ↔
    0 ∈ (evaln O (s-y) cf ⟪x.l, y+x.r⟫) ∧
    (∀ j ≤ y, (evaln O (s-j) cf ⟪x.l, j+x.r⟫).isSome) ∧
    (∀ j < y, ¬0 ∈ (evaln O (s-j) cf ⟪x.l, j+x.r⟫))
    := by
  simp (config := { singlePass := true }) only [evaln_sG1 h, Option.mem_def] at h ⊢
  constructor
  · intro h1
    have : y=nrfind'_obtain h := by
      unfold nrfind'_obtain
      simp_all
    rw [this]
    exact nrfind'_obtain_prop h
  contrapose
  intro h1
  push Not
  intro h2 h3
  replace h1 := mem_shambles h1 h (evaln_rfind_as_eval_rfind h)
  simp at h1
  rcases h1 h2 with ⟨h4,h5,h6⟩
  use h4
  refine ⟨h5,forall_mem_option (h3 h4 (le_of_succ_le h5)) h6⟩
theorem nrfind'_obtain_prop_6 {O s cf x} (h : (evaln O (s + 1) (rfind' cf) x).isSome) :
    ∀ j ≤ nrfind'_obtain h,
    (nrfind'_obtain h)+x.r ∈ (evaln O (s + 1-j) (rfind' cf) ⟪x.l, j+x.r⟫) := by
  have rop := nrfind'_obtain_prop h
  let (eq := hro) ro := nrfind'_obtain h
  simp [← hro] at rop ⊢
  rcases rop with ⟨rop1,rop2,rop3⟩
  have rop4 := nrfind'_obtain_prop_4 h
  intro j hjro
  have := @nrfind'_prop O (s + 1-j) cf ⟪x.l, j+x.r⟫ (ro-j) (rop4 j hjro)
  simp [mpp_leq hjro] at this
  apply (this).mpr ?_
  constructor
  · rw [Nat.sub_sub_sub_cancel_right hjro]
    exact rop1
  constructor
  · intro j2 hj2
    rw [← add_assoc]
    have rop2' := rop2 (j2+j) (add_le_of_le_sub hjro hj2)
    rwa [Eq.symm (Simproc.sub_add_eq_comm (s + 1) j2 j)]
  · intro j2 hj2
    rw [← add_assoc]
    have rop3' := rop3 (j2+j) (add_lt_of_lt_sub hj2)
    rwa [Eq.symm (Simproc.sub_add_eq_comm (s + 1) j2 j)]
theorem nrfind'_obtain_prop_4' {O s cf x} (h : (evaln O (s + 1) (rfind' cf) x).isSome) :
    ∀ j ≤ rfind'_obtain (en2e h), (evaln O (s + 1-j) (rfind' cf) ⟪x.l, j+x.r⟫).isSome := by
  rw [← nrop_eq_rop h]
  exact fun j a ↦ nrfind'_obtain_prop_4 h j a
theorem nrfind'_obtain_prop_6' {O s cf x} (h : (evaln O (s + 1) (rfind' cf) x).isSome) :
    ∀ j ≤ rfind'_obtain (en2e h),
    (rfind'_obtain (en2e h))+x.r ∈ (evaln O (s + 1-j) (rfind' cf) ⟪x.l, j+x.r⟫) := by
  rw [← nrop_eq_rop h]
  exact fun j a ↦ nrfind'_obtain_prop_6 h j a

theorem evaln_complete' {O s c x y} (h : (evaln O s c x).isSome) :
    (y∈eval O c x) → (y∈evaln O s c x) := by
  intro hh
  rcases evaln_complete.mp hh with ⟨h1,h2⟩
  simp only [Option.mem_def] at ⊢ h2
  rw [← h2]
  exact evaln_sing'' h  (Option.isSome_of_eq_some h2)
theorem evaln_complete'' {O} {c n x} : x ∈ eval O c n ↔ ∃ k, x ∈ evaln O (k+1) c n := by
  constructor
  rotate_left
  intro h1
  rcases h1 with ⟨h2,h3⟩
  exact evaln_sound h3
  intro h1
  rcases evaln_complete.mp h1 with ⟨h2,h3⟩
  have := Option.isSome_of_eq_some h3
  simp (config := {singlePass := true}) [evaln_sG1 this] at this
  use h2-1
  exact evaln_complete' this h1
lemma evaln_sound' {O s c x} (h : (evaln O s c x).isSome) : eval O c x = Part.some ((evaln O s c x).get h)
:= by
  have := evaln_sound (Option.get_mem h)
  exact Part.eq_some_iff.mpr this
theorem evaln_sound''' {O s c x y} (h : (evaln O s c x).isSome) :
    (y ∉ evaln O s c x) → (y ∉ eval O c x) := by
  contrapose
  simpa using fun h2 => evaln_complete' h h2

theorem rfind'_obtain_prop {O cf x} (h : (eval O (rfind' cf) x).Dom) :
    0 ∈ (eval O cf (Nat.pair x.l (rfind'_obtain h+x.r))) ∧
    (∀ j ≤ rfind'_obtain h, (eval O cf ⟪x.l, j+x.r⟫).Dom) ∧
    (∀ j < rfind'_obtain h, ¬0 ∈ (eval O cf ⟪x.l, j+x.r⟫)) := by
  rcases evaln_complete''.mp (Part.get_mem h) with ⟨h1,h2⟩
  rcases (nrfind'_obtain_prop' (Option.isSome_of_eq_some h2)) with ⟨nrop1,nrop2,nrop3⟩
  exact
  ⟨
    evaln_sound nrop1,
    fun j a ↦ en2e (nrop2 j a),
    fun j jj => evaln_sound''' (nrop2 j (le_of_succ_le jj)) (nrop3 j jj)
  ⟩
theorem rfind'_obtain_prop_4 {O cf x} (h : (eval O (rfind' cf) x).Dom) :
    ∀ j ≤ rfind'_obtain h, (eval O (rfind' cf) ⟪x.l, j+x.r⟫).Dom :=
  fun j jj => en2e <| nrfind'_obtain_prop_4'
    (Option.isSome_of_eq_some (evaln_complete''.mp (Part.get_mem h)).choose_spec) j jj

theorem rfind'_prop {O cf x y} (h : (eval O (rfind' cf) x).Dom) :
    y+x.r∈eval O (rfind' cf) x ↔
    0 ∈ (eval O cf ⟪x.l, y+x.r⟫) ∧
    (∀ j ≤ y, (eval O cf ⟪x.l, j+x.r⟫).Dom) ∧
    (∀ j < y, ¬0 ∈ (eval O cf ⟪x.l, j+x.r⟫)) := by
  constructor
  · intro h1
    have : y=rfind'_obtain h := by
      unfold rfind'_obtain
      have aux0 : (eval O cf.rfind' x).get h = y+x.r := by exact Part.get_eq_of_mem h1 h
      simp_all only [add_tsub_cancel_right]
    rw [this]
    exact rfind'_obtain_prop h
  contrapose
  intro h1
  push Not
  intro h2 h3
  simp [eval] at h1
  rcases h1 h2 with ⟨h4,h5,h6⟩
  use h4
  refine ⟨h5,forall_mem_part (h3 h4 (le_of_succ_le h5)) h6⟩
theorem rfind'_obtain_prop_6 {O cf x} (h : (eval O (rfind' cf) x).Dom) :
∀ j ≤ rfind'_obtain h, (rfind'_obtain h)+x.r ∈ (eval O (rfind' cf) ⟪x.l, j+x.r⟫) := by
  rcases evaln_complete''.mp (Part.get_mem h) with ⟨h1,h2⟩
  exact fun j jj =>
    evaln_sound ((nrfind'_obtain_prop_6' (Option.isSome_of_eq_some h2)) j jj)
end rfind_obtain
