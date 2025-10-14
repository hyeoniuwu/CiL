import Computability.Basic
import Mathlib.Tactic.Linarith

open List Nat
open Computability.Code

namespace Computability.Code

-- general lemmas for evaln
lemma evaln_sing (h1:a∈(evaln O s1 c x)) (h2:b∈(evaln O s2 c x)): a=b := by
  cases Classical.em (s1≤s2) with
  | inl h =>
    have := evaln_mono h h1
    simp_all only [Option.mem_def, Option.some.injEq]
  | inr h =>
    have := evaln_mono (Nat.le_of_not_ge h) h2
    simp_all only [Option.mem_def, Option.some.injEq]
lemma evaln_sing' : (evaln O s1 c x).get h1 = (evaln O s2 c x).get h2 := evaln_sing (Option.get_mem h1) (Option.get_mem h2)
lemma evaln_sing''
(h1:(evaln O s1 c x).isSome)
(h2:(evaln O s2 c x).isSome)
: (evaln O s1 c x) = (evaln O s2 c x) := Option.get_inj.mp (@evaln_sing' O s1 c x h1 s2 h2)
lemma evaln_mono'
(h1:(evaln O s1 c x).isSome)
(h2:s1≤s2)
: (evaln O s2 c x) = (evaln O s1 c x) := by
  have := evaln_mono h2 (Option.get_mem h1)
  simp_all only [Option.mem_def, Option.some_get]

theorem evaln_sG1 (h:(evaln O s c x).isSome) : s=s-1+1 := by
  have : s≠0 := by
    contrapose h
    simp only [ne_eq, Decidable.not_not] at h
    simp [h,evaln]
  exact Eq.symm (succ_pred_eq_of_ne_zero this)
theorem evaln_xles (h:(evaln O (s+1) c x).isSome) : x≤s :=le_of_lt_succ (evaln_bound (Option.get_mem h))
theorem evaln_xles' (h:(evaln O s c x).isSome) : x≤s-1 := by
  rw [evaln_sG1 h] at h
  exact evaln_xles h
abbrev en2e : (evaln O s c x).isSome → (eval O c x).Dom := by
  intro h
  have : (evaln O s c x).get (h) ∈ evaln O s c x := by exact Option.get_mem h
  have := evaln_sound (Option.get_mem h)
  exact Part.dom_iff_mem.mpr (⟨(evaln O s c x).get (h),this⟩)

lemma rfind'_geq_xr (h:(eval O (rfind' cf) x).Dom) : (eval O cf.rfind' x).get h ≥ x.r := by simp [eval]

theorem evaln_eq_eval (h:(evaln O s c x).isSome) : (evaln O s c x).get h = (eval O c x).get (en2e h) :=
  Eq.symm (Part.get_eq_of_mem (evaln_sound (Option.get_mem h)) (en2e h))
lemma nrfind'_geq_xr (h:(evaln O (s) (rfind' cf) x).isSome) : (evaln O (s) (rfind' cf) x).get h ≥ x.r := by
  rw [evaln_eq_eval]
  exact rfind'_geq_xr (en2e h)
def rfind'_obtain (h:(eval O (rfind' cf) x).Dom) : ℕ := ((eval O (rfind' cf) x).get h)-x.r
def nrfind'_obtain (h:(evaln O s (rfind' cf) x).isSome) : ℕ := ((evaln O s (rfind' cf) x).get h)-x.r
theorem nrop_eq_rop (h:(evaln O s (rfind' cf) x).isSome) : nrfind'_obtain h = rfind'_obtain (en2e h) := by
  unfold nrfind'_obtain
  unfold rfind'_obtain
  rw [evaln_eq_eval h]

theorem evaln_rfind_as_eval_rfind'
(h:(evaln O s (rfind' c) x).isSome)
:
((evaln O s (rfind' c) x).get h)
∈
((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) x)
:= by
  have := evaln_sound (Option.get_mem h)
  simp only [eval] at this
  exact this
theorem evaln_rfind_base (h:(evaln O (s+1) (rfind' cf) x).isSome) : (evaln O (s+1) (cf) x).isSome := by
  contrapose h
  simp at h
  simp [evaln]
  intro h1 h2 h3
  rw [h] at h3
  contradiction
theorem evaln_rfind_indt
(h:(evaln O (s+1) (rfind' cf) x).isSome)
(h2:(evaln O (s+1) (cf) x).isSome)
(h3: (evaln O (s+1) (cf) x).get h2 ≠ 0)
: (evaln O s cf.rfind' (Nat.pair x.l (x.r + 1))).isSome := by
  contrapose h
  simp at h
  simp [evaln]
  intro h4 h5 h6
  simp_all only [Option.get_some, ne_eq, ↓reduceIte]
theorem evaln_rfind_as_eval_rfind
(h:(evaln O (s+1) (rfind' c) x).isSome)
:
((evaln O (s+1) (rfind' c) x).get h)
∈
((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> evaln O ((s+1)-n) c (Nat.pair a (n + m))).map (· + m)) x)
:= by
  have := evaln_rfind_as_eval_rfind' h
  simp_all only [unpaired, unpair2_to_r, unpair1_to_l, Part.map_eq_map, Part.mem_map_iff, mem_rfind,
    decide_eq_true_eq, exists_eq_right, decide_eq_false_iff_not, Part.mem_ofOption, Option.mem_def]
  rcases this with ⟨h1,⟨h2,h3⟩,h4⟩
  use h1
  constructor
  constructor
  have := evaln_sound (Option.get_mem h)

  have : evaln O (s + 1 - h1) c (Nat.pair x.l (h1 + x.r)) = some 0 := by
    clear h3
    clear h2
    clear this
    induction h1 generalizing x s with
    | zero =>
      simp at ⊢ h4
      simp [evaln] at h4

      have hh := evaln_rfind_base h
      let asd := (evaln O (s + 1) c x).get hh
      have rwasd : (evaln O (s + 1) c x).get hh =asd := rfl

      contrapose h4
      simp [rwasd]
      have : asd≠0 := by
        contrapose h4; simp only [ne_eq, Decidable.not_not] at h4 ⊢
        rw [h4] at rwasd
        rw [show 0=(Option.some 0).get (Option.isSome_some) from rfl] at rwasd
        exact Option.get_inj.mp rwasd
      simp [this]
      have halt2 := evaln_rfind_indt h hh this
      have := nrfind'_geq_xr halt2
      simp at this
      exact Nat.ne_of_lt this
    | succ roM1 ih =>
      have := @ih (s-1) (Nat.pair x.l (x.r+1)) ?_ ?_
      -- simp_all
      simp at this ⊢
      all_goals
        have hh := evaln_rfind_base h
        let asd := (evaln O (s + 1) c x).get hh
        have rwasd : (evaln O (s + 1) c x).get hh =asd := rfl
      rotate_left
      ·
        contrapose h4
        simp at h4
        simp [evaln]
        simp [rwasd]

        if hhh:asd=0 then simp [hhh] else
        simp [hhh]
        have halt2 := evaln_rfind_indt h hh hhh
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
          simp [rwasd] at h4
          cases hasd:asd with
          | zero  => simp [hasd] at h4
          | succ n =>
            simp [hasd] at h4
            simp [evaln]
            ac_nf at h4 ⊢
      · cases s with
      | zero => simp_all [evaln]
      | succ n =>
        simp at this
        ac_nf at this ⊢
  exact this
  all_goals
    have halt_base := evaln_rfind_base h
    let base_val := (evaln O (s + 1) c x).get halt_base
    have rwasd : (evaln O (s + 1) c x).get halt_base =base_val := rfl
  ·
    intro j hj

    clear h2
    -- clear h4
    induction j generalizing x s h1 with
    | zero =>
      simp
      use base_val
      constructor
      exact Option.eq_some_of_isSome halt_base
      have := h3 hj
      simp at this
      -- simp_all only [ne_eq, base_val]
      obtain ⟨g1,g2,g3⟩ := this
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
        cases hb:base_val with
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
            rw (config:={occs:=.pos [2]}) [add_comm]

            have : evaln O (sM1 + 1) c.rfind' (Nat.pair x.l (x.r+1)) = some (h1+x.r) := by
              simp_all
            exact Option.isSome_of_mem this
      have ih_aux_1 : h1 + x.r = (evaln O (s - 1 + 1) c.rfind' (Nat.pair x.l (1 + x.r))).get ih_aux_0 := by

        -- rw [h4]
        simp [evaln] at h4
        simp [rwasd] at h4
        -- simp [rwasd]
        if hb:base_val=0 then
          simp [hb] at h4
          rw [h4] at hj
          contradiction
        else
          simp [hb] at h4
          have halt2 := evaln_rfind_indt h halt_base (by simp_all)
          cases s with
          | zero => simp [evaln] at halt2
          | succ sM1 => simpa [add_comm]
      have ih1 := @ih (s-1) (Nat.pair x.l (1+x.r)) ?_ (h1-1) ?_ ?_ ?_ ?_ ?_

      clear ih
      -- clear ih

      rotate_left
      · exact ih_aux_0
      · simp only [pair_r]
        rw [show h1 - 1 + (1 + x.r) = h1+x.r from by grind]
        exact ih_aux_1
      ·
        intro j hjro
        simp only [pair_l, pair_r]
        rw [←add_assoc]
        exact @h3 (j+1) (add_lt_of_lt_sub hjro)
      · exact evaln_rfind_base ih_aux_0
      · exact rfl
      · exact lt_sub_of_add_lt hj
      simp at ih1
      simp

      rcases ih1 with ⟨g1,g2,g3⟩
      cases s with
      | zero => simp_all [evaln]
      | succ sM1 =>
        simp at g2
        rw [add_assoc]
        aesop? says simp_all only [Option.some.injEq, exists_eq_left', not_false_eq_true]
  simp_all only

theorem evaln_rfind_as_eval_rfind_reverse
(h:((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> evaln O ((s+1)-n) c (Nat.pair a (n + m))).map (· + m)) x).Dom)
:
((evaln O (s+1) (rfind' c) x)).isSome
:= by
  simp at h
  rcases h with ⟨h1,h2,h3⟩



  induction h1 generalizing s x with
  | zero =>
    simp [evaln]
    have xles : x≤s := by

      simp at h2
      contrapose h2
      simp at h2
      -- have : s < (Nat.pair x.l (1 + x.r)) := by exact?
      have contra : s+1 ≤ x := by exact h2
      intro he
      have := evaln_bound he
      have : x<x := by exact Nat.lt_of_lt_of_le this h2
      simp at this
    simp [xles]
    simp_all
  | succ n ih =>
    have h30 := @h3 0 (zero_lt_succ n)
    simp at h30
    simp at h2
    have : s≠0 := by
      contrapose h2
      simp at h2
      simp [h2,evaln]
    have sss : s=s-1+1 := by
      exact Eq.symm (succ_pred_eq_of_ne_zero this)
    have ih1 := @ih (s-1) (Nat.pair x.l (x.r+1)) ?_ ?_
    simp [evaln]
    -- have := @ih (x) ?_ ?_

    rotate_left
    · simp
      rw [←sss]
      ac_nf at h2 ⊢
    · simp
      intro j hj
      have := @h3 (j+1) (Nat.add_lt_add_right hj 1)
      simp at this
      rw [←sss]
      ac_nf at this ⊢
    have xles : x≤s := evaln_xles h30
    simp [xles]

    have := @h3 0 (zero_lt_succ n)
    simp at this
    simp [isSome.bind this]
    if hhhh:(evaln O (s + 1) c x).get this = 0 then
      simp [hhhh]
    else
      simp [hhhh]
      rw [sss]
      exact ih1
theorem evaln_rfind_as_eval_rfind_reverse'
(h:((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> evaln O (s-n) c (Nat.pair a (n + m))).map (· + m)) x).Dom)
:
((evaln O s (rfind' c) x)).isSome
:= by
  have : s≠0 := by
    contrapose h
    simp at h
    rw [h]
    simp [evaln]
  have : s=s-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero this)

  rw [this] at h ⊢
  exact evaln_rfind_as_eval_rfind_reverse h
theorem nrfind'_obtain_prop
(h:(evaln O (s+1) (rfind' cf) x).isSome) :
0∈(evaln O (s+1-(nrfind'_obtain (h))) cf (Nat.pair x.l (nrfind'_obtain (h)+x.r)))
∧ (∀ j ≤ nrfind'_obtain (h), (evaln O (s+1-j) cf  (Nat.pair x.l (j+x.r))).isSome)
∧ (∀ j < nrfind'_obtain (h), ¬0∈(evaln O (s+1-j) cf (Nat.pair x.l (j+x.r)))) := by

  let rf := (evaln O (s+1) cf.rfind' x).get h
  have aux0 : rf ∈ evaln O (s+1) cf.rfind' x := Option.get_mem h
  have aux3 : rf = (evaln O (s+1) cf.rfind' x).get h := rfl

  have := evaln_rfind_as_eval_rfind h
  rw [←aux3] at this; clear aux3
  have aux3 := this; clear this
  simp at aux3

  rcases aux3 with ⟨ro,⟨lll,rrr⟩,ha⟩
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
theorem nrfind'_obtain_prop'
(h:(evaln O (s+1) (rfind' cf) x).isSome) :
0∈(evaln O (s+1-(rfind'_obtain (en2e h))) cf (Nat.pair x.l (rfind'_obtain (en2e h)+x.r)))
∧ (∀ j ≤ rfind'_obtain (en2e h), (evaln O (s+1-j) cf  (Nat.pair x.l (j+x.r))).isSome)
∧ (∀ j < rfind'_obtain (en2e h), ¬0∈(evaln O (s+1-j) cf (Nat.pair x.l (j+x.r))))
:= by
  rw [←nrop_eq_rop h]
  exact nrfind'_obtain_prop h
lemma mpp_leq {x:ℕ} (hjro:j ≤ ro): (ro - j + (j + x)) = ro + x := by simp only [hjro, ←add_assoc,Nat.sub_add_cancel]
theorem nrfind'_obtain_prop_4 (h:(evaln O (s+1) (rfind' cf) x).isSome) :
∀ j ≤ nrfind'_obtain h, (evaln O (s+1-j) (rfind' cf) (Nat.pair x.l (j+x.r))).isSome := by
  have rop := nrfind'_obtain_prop h
  let ro := nrfind'_obtain h; have rwro : nrfind'_obtain h = ro := rfl
  simp [rwro] at rop ⊢
  rcases rop with ⟨rop1,rop2,_⟩

  intro j hjro
  apply evaln_rfind_as_eval_rfind_reverse' ?_
  simp
  use ro-j
  constructor
  ·
    rw [mpp_leq hjro]
    rw [Nat.sub_sub_sub_cancel_right hjro]
    exact rop1
  intro m hm
  rw [← (Nat.add_assoc m j x.r)]
  have := rop2 (m+j) (le_of_succ_le (add_lt_of_lt_sub hm))
  rwa [Eq.symm (Simproc.sub_add_eq_comm (s + 1) m j)]
private lemma mem_shambles
{o:Option ℕ}
{p:Part ℕ}
(h0:x∉o)
(h1:o.isSome)
(h2:o.get h1∈p)
:
(x∉p) := by
  contrapose h2
  simp at h2
  have : p=Part.some x := by exact Part.eq_some_iff.mpr h2
  rw [this]
  simp
  have : o ≠ some x := by exact h0
  contrapose this
  simp only [ne_eq, Decidable.not_not] at this ⊢
  rw [←this]
  exact Option.eq_some_of_isSome h1
theorem nrfind'_prop
(h:(evaln O s (rfind' cf) x).isSome)
:
(y+x.r∈(evaln O s (rfind' cf) x))
↔
(
0∈(evaln O (s-y) cf (Nat.pair x.l (y+x.r)))
∧ (∀ j ≤ y, (evaln O (s-j) cf (Nat.pair x.l (j+x.r))).isSome)
∧ (∀ j < y, ¬0∈(evaln O (s-j) cf (Nat.pair x.l (j+x.r))))
)
:= by
  simp (config:={singlePass:=true}) [evaln_sG1 h] at h ⊢
  constructor
  · intro h1
    have : y=nrfind'_obtain (h) := by
      unfold nrfind'_obtain
      simp_all
    rw [this]
    exact nrfind'_obtain_prop h
  have := evaln_rfind_as_eval_rfind h
  contrapose
  intro h1
  push_neg
  intro h2
  intro h3
  have h1 := mem_shambles h1 h this
  simp at h1
  rcases h1 h2 with ⟨h4,h5,h6⟩
  use h4
  refine ⟨h5,forall_mem_option (h3 h4 (le_of_succ_le h5)) h6⟩
theorem nrfind'_obtain_prop_6 (h:(evaln O (s+1) (rfind' cf) x).isSome) :
∀ j ≤ nrfind'_obtain h,
(nrfind'_obtain h)+x.r ∈ (evaln O (s+1-j) (rfind' cf) (Nat.pair x.l (j+x.r)))  := by
  have rop := nrfind'_obtain_prop h
  let ro := nrfind'_obtain h
  have rwro : nrfind'_obtain h = ro := rfl
  simp [rwro] at rop ⊢
  rcases rop with ⟨rop1,rop2,rop3⟩
  have rop4 := nrfind'_obtain_prop_4 h

  intro j hjro

  have := @nrfind'_prop O (s+1-j) cf (Nat.pair x.l (j + x.r)) (ro-j) (rop4 j hjro)
  simp [mpp_leq hjro] at this
  apply (this).mpr ?_
  constructor
  · rw [Nat.sub_sub_sub_cancel_right hjro]
    exact rop1
  constructor
  · intro j2 hj2
    rw [←add_assoc]
    have rop2':=rop2 (j2+j) (add_le_of_le_sub hjro hj2)
    rwa [Eq.symm (Simproc.sub_add_eq_comm (s + 1) j2 j)]

  · intro j2 hj2
    rw [←add_assoc]
    have rop3' := rop3 (j2+j) (add_lt_of_lt_sub hj2)
    rwa [Eq.symm (Simproc.sub_add_eq_comm (s + 1) j2 j)]
theorem nrfind'_obtain_prop_4' (h:(evaln O (s+1) (rfind' cf) x).isSome) :
∀ j ≤ rfind'_obtain (en2e h), (evaln O (s+1-j) (rfind' cf) (Nat.pair x.l (j+x.r))).isSome := by
  rw [←nrop_eq_rop h]
  exact fun j a ↦ nrfind'_obtain_prop_4 h j a
theorem nrfind'_obtain_prop_6' (h:(evaln O (s+1) (rfind' cf) x).isSome) :
∀ j ≤ rfind'_obtain (en2e h),
(rfind'_obtain (en2e h))+x.r ∈ (evaln O (s+1-j) (rfind' cf) (Nat.pair x.l (j+x.r)))  := by
  rw [←nrop_eq_rop h]
  exact fun j a ↦ nrfind'_obtain_prop_6 h j a

theorem evaln_complete' (h:(evaln O s c x).isSome) : (y∈eval O c x)→(y∈evaln O s c x) := by
  intro hh
  rcases evaln_complete.mp hh with ⟨h1,h2⟩
  simp only [Option.mem_def] at ⊢ h2
  rw [←h2]
  exact evaln_sing'' h  (Option.isSome_of_eq_some h2)
theorem evaln_complete'' {c n x} : x ∈ eval O c n ↔ ∃ k, x ∈ evaln O (k+1) c n := by
  constructor
  rotate_left
  intro h1
  rcases h1 with ⟨h2,h3⟩
  exact evaln_sound h3
  intro h1
  rcases evaln_complete.mp h1 with ⟨h2,h3⟩
  have := Option.isSome_of_eq_some h3
  simp (config:={singlePass:=true}) [evaln_sG1 this] at this
  use h2-1
  exact evaln_complete' this h1
theorem evaln_sound''' (h:(evaln O s c x).isSome) : (y∉evaln O s c x)→(y∉eval O c x) := by
  contrapose
  simp
  exact fun h2 => evaln_complete' h h2

theorem rfind'_obtain_prop
(h:(eval O (rfind' cf) x).Dom) :
0∈(eval O cf (Nat.pair x.l (rfind'_obtain h+x.r)))
∧ (∀ j ≤ rfind'_obtain h, (eval O cf (Nat.pair x.l (j+x.r))).Dom)
∧ (∀ j < rfind'_obtain h, ¬0∈(eval O cf (Nat.pair x.l (j+x.r))))
:= by
  rcases evaln_complete''.mp (Part.get_mem h) with ⟨h1,h2⟩
  rcases (nrfind'_obtain_prop' (Option.isSome_of_eq_some h2)) with ⟨nrop1,nrop2,nrop3⟩
  exact
  ⟨
    evaln_sound nrop1,
    fun j a ↦ en2e (nrop2 j a),
    fun j jj => evaln_sound''' (nrop2 j (le_of_succ_le jj)) (nrop3 j jj)
  ⟩
theorem rfind'_obtain_prop_4 (h:(eval O (rfind' cf) x).Dom) : ∀ j ≤ rfind'_obtain h, (eval O (rfind' cf) (Nat.pair x.l (j+x.r))).Dom :=
  fun j jj => en2e $ nrfind'_obtain_prop_4' (Option.isSome_of_eq_some (evaln_complete''.mp (Part.get_mem h)).choose_spec) j jj

theorem rfind'_prop
(h:(eval O (rfind' cf) x).Dom)
:
(y+x.r∈eval O (rfind' cf) x)
↔
(
0∈(eval O cf (Nat.pair x.l (y+x.r)))
∧ (∀ j ≤ y, (eval O cf (Nat.pair x.l (j+x.r))).Dom)
∧ (∀ j < y, ¬0∈(eval O cf (Nat.pair x.l (j+x.r))))
)
:= by
  constructor
  intro h1
  have : y=rfind'_obtain h := by
    unfold rfind'_obtain
    have aux0 : (eval O cf.rfind' x).get h = y+x.r := by exact Part.get_eq_of_mem h1 h
    simp_all only [add_tsub_cancel_right]
  rw [this]
  exact rfind'_obtain_prop h

  contrapose
  intro h1
  push_neg
  intro h2
  intro h3

  simp [eval] at h1
  rcases h1 h2 with ⟨h4,h5,h6⟩
  use h4
  refine ⟨h5,forall_mem_part (h3 h4 (le_of_succ_le h5)) h6⟩
theorem rfind'_obtain_prop_6 (h:(eval O (rfind' cf) x).Dom) :
∀ j ≤ rfind'_obtain h, (rfind'_obtain h)+x.r ∈ (eval O (rfind' cf) (Nat.pair x.l (j+x.r)))  := by
  rcases evaln_complete''.mp (Part.get_mem h) with ⟨h1,h2⟩
  exact fun j jj =>
    evaln_sound ((nrfind'_obtain_prop_6' (Option.isSome_of_eq_some h2)) j jj)


-- /--
-- we define the use `max(all naturals queried to the oracle)+1`
-- use=0 when no queries are made.
-- use=none when the computation diverges.
-- -/
open Classical in
noncomputable def use (O:ℕ→ℕ) (c:Code) (x:ℕ) : Part ℕ :=
match c with
| zero        => Part.some (0)
| succ        => Part.some (0)
| left        => Part.some (0)
| right       => Part.some (0)
| oracle      => Part.some (x+1)
| pair cf cg  => Nat.max <$> (use O cf x) <*> (use O cg x)
| comp cf cg  => Nat.max <$> (use O cg x) <*> (eval O cg x >>= use O cf)
| prec cf cg  =>
  let (xl, i) := Nat.unpair x
  i.rec (use O cf xl)
  fun iM1 IH => do
    let IH_N ← eval O (prec cf cg) (Nat.pair xl iM1);
    Nat.max <$> IH <*> use O cg (Nat.pair xl (Nat.pair iM1 IH_N))
| Code.rfind' cf =>
  do
    let guard ← eval O (rfind' cf) x;
    let ro := guard - x.r
    let mut max := 0
    for i in List.reverse (List.range (ro+1)) do
      let use_i ← (use O cf (Nat.pair x.l (i+x.r)))
      max := Nat.max max use_i
    max
/-- `usen; the use of [c:O]ₛ(x)` -/
def usen (O:ℕ→ℕ) (c:Code) (s:ℕ) : ℕ→ Option ℕ :=
match c,s with
| _, 0            => λ _ ↦ Option.none
| zero      , s+1 => λ x ↦ do guard (x≤s); return 0
| succ      , s+1 => λ x ↦ do guard (x≤s); return 0
| left      , s+1 => λ x ↦ do guard (x≤s); return 0
| right     , s+1 => λ x ↦ do guard (x≤s); return 0
| oracle    , s+1 => λ x ↦ do guard (x≤s); return x+1
| pair cf cg, s+1 => λ x ↦
  do
    guard (x≤s);
    let usen_cf ← usen O cf (s+1) x
    let usen_cg ← usen O cg (s+1) x
    return Nat.max usen_cf usen_cg
| comp cf cg, s+1  => λ x ↦
  do
    guard (x≤s);
    let usen_cg  ← usen O cg (s+1) x
    let evaln_cg ← evaln O (s+1) cg x
    let usen_cf  ← usen O cf (s+1) evaln_cg
    return Nat.max usen_cf usen_cg
| prec cf cg, s+1 => λ x ↦ do
  guard (x≤s);
  let (xl, i) := Nat.unpair x
  (i.casesOn
  (usen O cf (s+1) xl)
  fun iM1 =>
  do
    let usen_prev  ← usen  O (prec cf cg) s (Nat.pair xl iM1)
    let evaln_prev ← evaln O s (prec cf cg) (Nat.pair xl iM1)
    let usen_indt  ← usen  O cg (s+1) (Nat.pair xl (Nat.pair iM1 evaln_prev))
    return Nat.max usen_prev usen_indt)
| rfind' cf, s+1 => λ x ↦
  do
    guard (x≤s);
    let usen_base  ← usen O cf (s+1) x
    let evaln_base ← evaln O (s+1) cf x
    if evaln_base=0 then usen_base else
    let usen_indt  ← usen O (rfind' cf) s (Nat.pair x.l (x.r+1))
    Nat.max usen_base usen_indt

-- Custom induction principle used in usen_sound
def CodeNatK.induction
  {motive : ℕ → Code → Prop}
  -- base case: k = 0, c arbitrary
  (h0 : ∀ c, motive 0 c)

  -- step case: k+1
  (hzero   : ∀ k, motive (k+1) .zero)
  (hsucc   : ∀ k, motive (k+1) .succ)
  (hleft   : ∀ k, motive (k+1) .left)
  (hright  : ∀ k, motive (k+1) .right)
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

-- TODO: replace ind with an explicit induction scheme
private def ind : ℕ → Code → ℕ
| 0, _ => 0
| _+1, zero => 0
| _+1, succ => 0
| _+1, left => 0
| _+1, right => 0
| _+1, oracle => 0
| s+1, pair cf cg => ind (s+1) cf + ind (s+1) cg
| s+1, comp cf cg => ind (s+1) cf + ind (s+1) cg
| s+1, prec cf cg =>
  ind (s+1) cf
  + ind (s+1) cg
  + ind s (prec cf cg)
| s+1, rfind' cf =>
  ind (s+1) cf
  + ind s (rfind' cf)


theorem usen_none_iff_evaln_none : (usen O c s x) = Option.none ↔ (evaln O s c x) = Option.none := by
-- using evaln.induct doesnt work, the prec inductive hypothesis w cf.prec cg is s+1 instead of s for some reason
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
    cases Classical.em (x≤s) with
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
    cases Classical.em (x≤s) with
    | inr h => simp [h]
    | inl h =>
    simp [h]
    constructor
    · intro hh a ha
      have := (@hcg x).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
      exact hcf.mp (Option.eq_none_iff_forall_ne_some.mpr (hh a2 ha2 a ha))
    · exact λ hh a ha a3 ha3 ↦ Option.eq_none_iff_forall_ne_some.mp (hcf.mpr (hh a3 ha3))
  | case9 s cf cg hcf hcg ih =>
    simp [usen,evaln]
    cases Classical.em (x≤s) with
    | inr h => simp [h]
    | inl h =>
    simp [h]
    cases hxr:x.r with
    | zero => simp; exact hcf
    | succ xrM1 =>
    simp only [Option.bind_eq_none_iff, reduceCtorEq, imp_false]

    constructor
    ·
      intro hh a ha
      have := (@ih (Nat.pair x.l xrM1)).not
      simp only [Option.ne_none_iff_exists'] at this
      obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
      have := hh a2 ha2 a ha
      exact hcg.mp (Option.eq_none_iff_forall_ne_some.mpr this)
    · exact λ hh a ha a3 ha3 ↦ Option.eq_none_iff_forall_ne_some.mp (hcg.mpr (hh a3 ha3))
  | case10 s cf hcf ih =>
    simp [usen,evaln]
    cases Classical.em (x≤s) with
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

theorem usen_dom_iff_evaln_dom : (∃a,a∈(usen O c s x)) ↔ (∃b,b∈(evaln O s c x)) := by
  have := (@usen_none_iff_evaln_none O c s x).not
  simp [Option.eq_none_iff_forall_ne_some] at this
  exact this
theorem usen_dom_iff_evaln_dom' : ((usen O c s x).isSome) ↔ ((evaln O s c x).isSome) := by
  have := (@usen_none_iff_evaln_none O c s x).not
  simp at this
  simp [isSome_iff_not_none] at this
  exact Bool.coe_iff_coe.mpr this
theorem usen_bound : ∀ {k c n x}, x ∈ usen O c k n → n < k
  | 0, c, n, x, h => by simp [usen] at h
  | k + 1, c, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [usen] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le
private lemma guard_imp {k:ℕ} (h:k≤k₂) : guard (n ≤ k) = some a → (guard (n ≤ k₂):Option Unit) = some a := by
  intro hhh
  have : n≤k := by
    contrapose hhh
    simp only [hhh, guard_false, reduceCtorEq, not_false_eq_true]
  have : n≤k₂ := by exact Nat.le_trans this h
  simp [this]
theorem usen_mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ usen O c k₁ n → x ∈ usen O c k₂ n
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
    · exact λ g h ↦ ⟨Nat.le_trans g hl', hf n.l x h⟩
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
theorem usen_mono_contra : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → usen O c k₂ n = Option.none → usen O c k₁ n = Option.none := by
  intro k₁ k₂ c n k1k2 opt
  contrapose opt
  have := usen_mono k1k2 (Option.get_mem (Option.isSome_iff_ne_none.mpr opt))
  refine Option.ne_none_iff_exists'.mpr ?_
  exact Exists.intro ((usen O c k₁ n).get (Option.isSome_iff_ne_none.mpr opt)) this
theorem usen_mono_dom : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → (usen O c k₁ n).isSome → (usen O c k₂ n).isSome := by
  intro k1 k2 c n k1k2 h1
  exact Option.isSome_of_mem (usen_mono k1k2 (Option.get_mem h1))
theorem evaln_mono_dom : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → (evaln O k₁ c n).isSome → (evaln O k₂ c n).isSome := by
  intro k1 k2 c n k1k2 h1
  exact Option.isSome_of_mem (evaln_mono k1k2 (Option.get_mem h1))


lemma part_add {x y : ℕ}: Part.some x + Part.some y = Part.some (x+y) := by
  exact Part.some_add_some x y
theorem use_dom_iff_eval_dom : (use O c x).Dom ↔ (eval O c x).Dom := by
  induction c generalizing x with
  | zero => exact Eq.to_iff rfl
  | succ => exact Eq.to_iff rfl
  | left => exact Eq.to_iff rfl
  | right => exact Eq.to_iff rfl
  | oracle => simp [use,eval]
  | pair cf cg hcf hcg => simp [use,eval,Seq.seq]; simp_all only []
  | comp cf cg hcf hcg => simp [use,eval,Seq.seq]; simp_all only [and_exists_self]
  | prec cf cg hcf hcg =>
    simp [use,eval,Seq.seq]
    induction x.r with
    | zero => simp_all
    | succ xrM1 ih => simp_all
  | rfind' cf hcf =>
    constructor
    · simp [use]
      intro x_1 h
      exact x_1

    intro h
    have rop := rfind'_obtain_prop h
    let ro := rfind'_obtain h
    have rwro : rfind'_obtain h = ro := rfl
    simp [rwro] at rop ⊢
    rcases rop with ⟨rop1,rop2,rop3⟩
    have rop4 := rfind'_obtain_prop_4 h
    simp [rwro] at rop4
    simp [use]
    use h
    have rwro2 : (eval O (rfind' cf) x).get h - x.r = ro := rfl
    simp [rwro2]

    generalize 0=a at h ⊢
    revert rop2
    induction ro generalizing a with
    | zero =>
      simp_all
      intro rop2
      -- have := rop2 0 (zero_le ro)
      have := rop2
      aesop? says
        simp_all only [ro]
        split
        next x_1 b heq => simp_all only [Part.some_dom]
        next x_1 b heq => simp_all only [Part.some_dom]
    | succ n ih =>
      simp (config:={singlePass:=true}) [listrwgen]; simp
      intro rop2
      have := hcf.mpr (rop2 (n+1) (le_rfl))
      simp [Part.Dom.bind this]
      use this
      exact ih
        (a.max ((use O cf (Nat.pair x.l (n + 1 + x.r))).get this))
        (λ j hj ↦ rop2 (j) (le_add_right_of_le hj))

abbrev e2u : (eval O c x).Dom → (use O c x).Dom := use_dom_iff_eval_dom.mpr
abbrev u2e : (use O c x).Dom → (eval O c x).Dom := use_dom_iff_eval_dom.mp
abbrev en2un : (evaln O s c x).isSome → (usen O c s x).isSome := usen_dom_iff_evaln_dom'.mpr
abbrev un2en : (usen O c s x).isSome → (evaln O s c x).isSome := usen_dom_iff_evaln_dom'.mp

lemma eval_rfind_prop5 :
x∈eval O (rfind' cf) y→y.r≤x := by
  simp [eval]
  grind
lemma evaln_rfind_prop5 :
x∈evaln O s (rfind' cf) y→y.r≤x := by
  intro h
  exact eval_rfind_prop5 (evaln_sound h)

lemma usen_sing (h1:a∈(usen O c s1 x)) (h2:b∈(usen O c s2 x)): a=b := by
  cases Classical.em (s1≤s2) with
  | inl h =>
    have := usen_mono h h1
    simp_all only [Option.mem_def, Option.some.injEq]
  | inr h =>
    have := usen_mono (Nat.le_of_not_ge h) h2
    simp_all only [Option.mem_def, Option.some.injEq]
lemma usen_sing' : (usen O c s1 x).get h1 = (usen O c s2 x).get h2 := usen_sing (Option.get_mem h1) (Option.get_mem h2)

lemma usen_mono'
(h1:(usen O c s1 x).isSome)
(h2:s1≤s2)
: (usen O c s2 x) = (usen O c s1 x) := by
  have := usen_mono h2 (Option.get_mem h1)
  simp_all only [Option.mem_def, Option.some_get]

lemma evaln_rfind_prop_aux :
(∃y,y+x.r∈evaln O (k+1) (rfind' cf) x)
↔  ¬ (evaln O (k+1) (rfind' cf) x=Option.none) := by
  constructor
  intro h
  grind
  intro h
  rcases Option.ne_none_iff_exists'.mp h with ⟨h1,h2⟩
  have := evaln_rfind_prop5 h2
  use h1-x.r
  simp [this]
  exact h2

theorem evaln_rfind_prop_not' :
¬ y + x.r ∈ evaln O (k + 1) cf.rfind' x ↔
  (¬0 ∈ evaln O (k + 1 - y) cf (Nat.pair x.l (y + x.r))) ∨
    ((∃ j ≤ y, evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r))=Option.none) ) ∨
    (¬ ∀ j < y, 0 ∉ evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r)))
:= by

  induction y generalizing x k with
  | zero =>
    simp_all
    constructor
    intro h
    contrapose h
    simp_all
    simp [evaln]
    cases em (x≤k) with
    | inl hh =>  simp [hh,h]
    | inr hh =>
      simp [hh, Option.bind]
      contrapose hh
      simp
      exact le_of_lt_succ (evaln_bound h.left)


    intro h
    simp [evaln]
    cases em (x≤k) with
    | inr hh => simp [hh, Option.bind]
    | inl hh =>
    cases h with
    | inr h => simp [h]
    | inl h =>
    simp [hh]
    cases em (evaln O (k + 1) cf x=Option.none) with
    | inl hhh => simp [hhh]
    | inr hhh =>
    rcases Option.ne_none_iff_exists'.mp hhh with ⟨h13,h14⟩
    simp_all
    intro cont
    have := evaln_rfind_prop5 cont
    simp at this

  | succ yM1 ih =>
  have rwadd : yM1 + 1 + x.r = yM1 + (x.r + 1) := by ac_nf

  constructor

  intro this
  simp [evaln] at this
  cases em (x≤k) with
  | inl h =>
    simp [h] at this
    cases k with
    | zero => simp_all [evaln]
    | succ kM1 =>

    have ih1 := (@ih (kM1) (Nat.pair x.l (x.r + 1))).mp
    clear ih
    simp at ih1

    cases em ((evaln O (kM1+1+1) cf x)=Option.none) with
    | inl hh =>
      simp_all
      apply Or.inr; apply Or.inl
      use 0
      simpa
    | inr hh =>
    rcases Option.ne_none_iff_exists'.mp hh with ⟨h13,h14⟩
    simp_all
    cases em (h13=0) with
    | inl hhh =>
      simp [hhh] at this
      simp_all
      apply Or.inr
      apply Or.inr
      use 0
      simpa
    | inr hhh =>
    simp [hhh] at this
    have ih2 := ih1 this
    clear ih1

    cases ih2 with
    | inl h => apply Or.inl; assumption
    | inr h =>
    cases h with
    | inl h =>
      apply Or.inr
      apply Or.inl
      rcases h with ⟨h1,h2,h3⟩
      cases h1 with
      | zero =>
        simp_all
        use 1
        constructor
        · exact le_add_left 1 yM1
        simp
        rw (config:={occs:=.pos [2]}) [add_comm]
        assumption
      | succ h1M1 =>
        simp at h3
        use h1M1+1+1
        constructor
        · simp only [add_le_add_iff_right]
          exact h2
        simp only [reduceSubDiff]
        rwa [Nat.add_right_comm (h1M1 + 1) 1 x.r]
    | inr h =>
      apply Or.inr
      apply Or.inr
      rcases h with ⟨h1,h2,h3⟩
      cases h1 with
      | zero =>
        simp_all
        use 1
        constructor
        · exact Nat.lt_add_of_pos_left h2
        simp
        rw (config:={occs:=.pos [2]}) [add_comm]
        assumption
      | succ h1M1 =>
        simp at h3
        use h1M1+1+1
        constructor
        · simp only [add_lt_add_iff_right]
          exact h2
        simp only [reduceSubDiff]
        rwa [Nat.add_right_comm (h1M1 + 1) 1 x.r]

  | inr h =>
    apply Or.inl
    simp at h
    have : x < (Nat.pair x.l (yM1 + 1 + x.r)) := by
      rw (config:={occs:=.pos [1]})  [show x=Nat.pair x.l x.r from by simp]
      apply pair_lt_pair_right
      grind only
    -- have : k

    simp
    have : (k - yM1) < (Nat.pair x.l (yM1 + 1 + x.r)) := by
      grind
    contrapose this
    simp at this
    have := evaln_bound this
    exact Nat.not_lt_of_gt this





  intro this
  simp [evaln]
  cases em (x≤k) with
  | inr hh => simp [hh, Option.bind]
  | inl xlek =>
  simp [xlek]
  cases em ((evaln O (k + 1) cf x)=Option.none) with
  | inl hh => simp [hh]
  | inr hh =>



  have : ∃z,z∈ evaln O (k + 1) cf x := by exact Option.ne_none_iff_exists'.mp hh
  rcases this with ⟨h13,h14⟩
  simp_all
  cases em (h13=0) with
  | inl hhh =>
    simp [hhh]
    grind
  | inr hhh =>
  simp [hhh]



  have ih1 := @ih (k-1) (Nat.pair x.l (x.r+1))
  clear ih
  simp at ih1
  cases k with
  | zero => simp [evaln]
  | succ kM1 =>
  simp at *



  cases this with
  | inl h => exact ih1.mpr (Or.inl h)
  | inr h =>
  cases h with
  | inl h =>
    rcases h with ⟨h1,h2,h3⟩
    cases h1 with
    | zero => simp_all
    | succ h1M1 =>
    have : (∃ j ≤ yM1, evaln O (kM1 + 1 - j) cf (Nat.pair x.l (j + (x.r + 1))) = Option.none) := by
      use h1M1
      constructor
      exact le_of_lt_succ h2
      simp at h3
      ac_nf at h3 ⊢
    exact ih1.mpr (Or.inr (Or.inl this))
  | inr h =>
    rcases h with ⟨h1,h2,h3⟩
    cases h1 with
    | zero => simp_all
    | succ h1M1 =>
    have : ∃ x_1 < yM1, evaln O (kM1 + 1 - x_1) cf (Nat.pair x.l (x_1 + (x.r + 1))) = some 0 := by
      use h1M1
      constructor
      exact succ_lt_succ_iff.mp h2
      simp at h3
      ac_nf at h3 ⊢
    exact ih1.mpr (Or.inr (Or.inr this))
theorem evaln_rfind_prop :
y+x.r∈evaln O (k+1) cf.rfind' x
↔
0∈(evaln O (k+1-y) cf (Nat.pair x.l (y+x.r)))
∧ (∀ j ≤ y, ∃z,z∈(evaln O (k+1-j) cf (Nat.pair x.l (j+x.r))))
∧ (∀ j < y, ¬0∈(evaln O (k+1-j) cf (Nat.pair x.l (j+x.r)))) := by
  suffices ¬ y + x.r ∈ evaln O (k + 1) cf.rfind' x ↔
  (¬0 ∈ evaln O (k + 1 - y) cf (Nat.pair x.l (y + x.r))) ∨
    ((∃ j ≤ y, evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r))=Option.none) ) ∨
    (¬ ∀ j < y, 0 ∉ evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r))) from by
      apply Iff.not at this
      simp
      simp [Option.ne_none_iff_exists'] at this
      assumption
  exact evaln_rfind_prop_not'


theorem usen_rfind_prop_aux'' {cf:Code} :
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
  have nlek : n≤k := by contrapose h; simp at h; simp [h]
  simp [nlek] at h ⊢
  have usen_base_dom : (usen O cf (k + 1) n).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind usen_base_dom] at h
  have evaln_base_dom : (evaln O (k + 1) cf n).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind evaln_base_dom] at h ⊢

  cases hevaln_base:(evaln O (k + 1) cf n).get evaln_base_dom with
  | zero => simp
  | succ _ =>
    simp [hevaln_base] at h ⊢
    have usen_indt_dom : ((usen O cf.rfind' k (Nat.pair n.l (n.r + 1)))).isSome := by contrapose h; simp at h; simp [h]
    clear h
    exact ih usen_indt_dom
theorem usen_rfind_prop_aux' {cf:Code} :
(usen O cf.rfind' (k + 1) n).isSome
→
(eval O cf.rfind' n).Dom
:= fun h ↦en2e (usen_rfind_prop_aux'' h)
theorem usen_rfind_prop_aux {cf:Code} :
(x ∈ usen O cf.rfind' (k + 1) n)
→
(eval O cf.rfind' n).Dom
:= by
  intro h
  have : (usen O cf.rfind' (k + 1) n).isSome := by exact Option.isSome_of_mem h
  exact usen_rfind_prop_aux' this
theorem use_rfind_prop (hu:(use O (rfind' cf) n).Dom):
∀j≤rfind'_obtain (u2e hu),
  (use O cf (Nat.pair n.l (n.r+j))).Dom
  -- and also the maximum of these is equal to the usen.
:= by
  intro j hjro
  rw [add_comm]
  exact e2u ((rfind'_obtain_prop (u2e hu)).right.left j hjro)
theorem usen_rfind_prop' (hu:(usen O (rfind' cf) (k + 1) n).isSome):
∀j≤rfind'_obtain (usen_rfind_prop_aux' hu),
  (usen O cf (k + 1 - j) (Nat.pair n.l (n.r+j))).isSome
  -- and also the maximum of these is equal to the usen.
:= by
  intro j hjro
  rw (config:={occs:=.pos [2]}) [add_comm]
  exact en2un ((nrfind'_obtain_prop' (un2en hu)).right.left j hjro)
theorem usen_rfind_prop (h:x ∈ usen O cf.rfind' (k + 1) n):
∀j≤rfind'_obtain (usen_rfind_prop_aux h),
  ∃y,y∈ (usen O cf (k + 1 - j) (Nat.pair n.l (n.r+j)))
  -- and also the maximum of these is equal to the usen.
:= by
  have := @usen_rfind_prop'
  simp [Option.isSome_iff_mem] at this
  exact fun j a ↦ this x h j a
lemma nrf_aux (h:(usen O (rfind' cf) k x).isSome) :
 k=k-1+1
:= by
  have : k≠0 := by
    contrapose h; simp at h; simp [h]
    simp [usen]
  have keqkM1P1 : k=k-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero this)
  exact keqkM1P1
lemma nrf (h:(usen O (rfind' cf) k x).isSome) :
x≤k-1
∧
(usen O cf k x).isSome
∧
(evaln O (k) cf x).isSome
:= by
  have keqkM1P1 := nrf_aux h
  simp (config:={singlePass:=true}) [keqkM1P1] at h ⊢

  simp [usen] at h
  have xlek : x≤k-1 := by
    contrapose h;
    simp [h, Option.bind]
  simp [xlek] at h ⊢
  have usen_base_dom : (usen O cf (k-1+1) x).isSome := by exact Option.isSome_of_isSome_bind h
  simp [isSome.bind usen_base_dom] at h
  simp [usen_base_dom]
  have evaln_base_dom : (evaln O (k -1+1) cf x).isSome := by exact un2en usen_base_dom
  simp [isSome.bind evaln_base_dom] at h ⊢
  simp [evaln_base_dom]
lemma nrfh (h:(usen O (rfind' cf) k x)=some y) : (if (evaln O (k) cf x).get (nrf (Option.isSome_of_mem h)).right.right = 0 then usen O cf (k) x
    else
      (usen O cf.rfind' (k - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦
        some (((usen O cf (k) x).get (nrf (Option.isSome_of_mem h)).right.left).max usen_indt)) = some y := by
  have := (nrf (Option.isSome_of_mem h))
  have : k≠0 := by
    contrapose h; simp at h; simp [h]
    simp [usen]
  have keqkM1P1 : k=k-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero this)
  rcases nrf (Option.isSome_of_mem h) with ⟨xlek,usen_base_dom,evaln_base_dom⟩
  simp (config:={singlePass:=true}) [keqkM1P1] at h ⊢ usen_base_dom evaln_base_dom

  simp [usen] at h
  simp [xlek] at h ⊢
  simp [isSome.bind usen_base_dom] at h
  simp [isSome.bind evaln_base_dom] at h ⊢
  exact h
lemma unrpeq2' :
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
lemma unrpeq2 :
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
lemma unrpeq0 :
(y ∈ usen O (rfind' cf) (k + 1) x)
↔
(
  ∃
  (evalnbasedom:(evaln O (k + 1) cf x).isSome)
  (evaln_ver_dom:(evaln O (k + 1) cf.rfind' x).isSome)
  ,
  -- (if (evaln O (k + 1) cf x).get evalnbasedom = 0 then usen O cf (k + 1) x
  (if (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r=0 then usen O cf (k + 1) x
  else
    (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦
      some (((usen O cf (k + 1) x).get (en2un evalnbasedom)).max usen_indt)) = some y) := by
  constructor
-- mp
  intro h
  have evaln_ver_dom:(evaln O (k + 1) cf.rfind' x).isSome := un2en (Option.isSome_of_mem h)
  simp [usen] at h
  have xlek : x≤k := evaln_xles evaln_ver_dom
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
  have xlek : x≤k := le_of_lt_succ (evaln_bound (Option.get_mem h1))
  simp [xlek]
  simp [isSome.bind (en2un h1)]
  simp [isSome.bind (h1)]
  simp_all [@unrpeq2 O k cf x h1 h2]

lemma unrpeq1 : (y∈(do
  guard (x≤k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) (Nat.pair x.l (i+x.r)))
    max := Nat.max max usen_i
  max :Option ℕ)) ↔ (
  ∃
  (evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome),
  ((forIn (List.range ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r + 1)).reverse 0 fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + x.r))).bind fun usen_i ↦ some (ForInStep.yield (r.max usen_i))) =
  some y)
) := by
  simp
  constructor
  intro h
  have xlek : x≤k := by
    contrapose h;
    simp [h, Option.bind]
  simp [xlek] at h ⊢
  have evaln_ver_dom : (evaln O (k+1) (rfind' cf) x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind evaln_ver_dom] at h
  use evaln_ver_dom

  intro h
  rcases h with ⟨h1,h2⟩
  have xlek : x≤k := by
    simp [evaln] at h1
    contrapose h1;
    simp [h1]
  simp [xlek]
  simp [isSome.bind h1]
  exact h2
lemma lemlemlem2
(a:ℕ)
(h1 : (evaln O (k + 1) cf x).isSome)
(u0:(usen O cf (k + 1) x).isSome)
(u1:(usen O cf (k + 1) (Nat.pair x.l (x.r + 1))).isSome)
(nrop2:(∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) (Nat.pair x.l (j + x.r))).isSome))
:
(forIn (List.range (roM1 + 1)).reverse (a.max ((usen O cf (k + 1) x).get (en2un h1))) fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + (x.r + 1)))).bind fun a ↦ some (ForInStep.yield (r.max a)))
    =
(forIn (List.range (roM1 + 1)).reverse (a.max ((usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).get asddom))
    fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + x.r))).bind fun usen_i ↦ some (ForInStep.yield (r.max usen_i)))
 := by

  induction roM1 generalizing a with
  | zero =>
    simp [isSome.bind u0]
    simp [isSome.bind u1]
    ac_nf
    rw (config:={occs:=.pos [2]}) [Nat.max_comm]
    apply congrArg
    apply congrFun
    apply congrArg
    apply usen_sing'

  | succ roM2 iihh =>

    simp (config:={singlePass:=true}) [listrwgen]
    simp

    have urom:(usen O cf (k +1 - (roM2+1)) (Nat.pair x.l ((roM2+1) + 1 + x.r))).isSome := by
      have := nrop2 (roM2+1+1) (Nat.le_refl (roM2 + 1 + 1))
      simp at this
      apply usen_mono_dom _ this
      exact Nat.sub_le_add_right_sub k (roM2 + 1) 1
    simp at urom
    rw [add_assoc] at urom
    rw (config:={occs:=.pos [3]}) [add_comm] at urom
    simp [isSome.bind urom]

    have urom2 : (usen O cf (k +1 - (roM2+1)) (Nat.pair x.l ((roM2+1) + x.r))).isSome := nrop2 (roM2+1) (le_add_right (roM2 + 1) 1)
    simp at urom2
    simp [isSome.bind urom2]

    have iihh1 := @iihh
      urom2
      (a.max ((usen O cf (k - roM2) (Nat.pair x.l (roM2 + 1 + (x.r + 1)))).get urom))
      (λ j hj ↦ (nrop2 j (le_add_right_of_le hj)))
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

theorem usen_rfind_prop2 :
(y ∈ usen O cf.rfind' (k + 1) x)
↔
y∈(do
  guard (x≤k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) (Nat.pair x.l (i+x.r)))
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
    (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦
      some (((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
    =
  (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (some (base'.max ((usen O cf (k + 1) x).get (en2un h1)))) else
    (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦
      some (base'.max $ ((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
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
    simp [isSome.bind $ en2un h1]
  | succ roM1 ih =>
    simp
    simp at ih
    simp (config:={singlePass:=true}) [listrwgen]
    simp
    intro asd
    intro h
    have usenindtdom : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).isSome := by
      contrapose h; simp at h; simp [h]
    simp [isSome.bind usenindtdom] at h ih
    have evalnindtdom := un2en usenindtdom
    have nrfindt := nrf usenindtdom

    have nrop := nrfind'_obtain_prop' h2
    have nrop6 := nrfind'_obtain_prop_6' h2
    rw [asd] at nrop nrop6
    have nrop2 : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) (Nat.pair x.l (j + x.r))).isSome) := fun j a ↦ en2un (nrop.right.left j a)
    have asddom : (usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome := by
      have := nrop2 (roM1+1) (le_rfl)
      simp at this
      exact this
    simp [isSome.bind asddom]



    have aux0 : (evaln O (k + 1) cf (Nat.pair x.l (x.r + 1))).isSome := Option.isSome_of_mem (evaln_mono (le_add_right k 1) (Option.get_mem nrfindt.right.right))
    have ih1 := @ih
      (Nat.pair x.l (x.r+1))
      aux0
      (Option.isSome_of_mem (evaln_mono (le_add_right k 1) (Option.get_mem evalnindtdom)))
      aux0
      (base.max ((usen O cf (k+1) x).get (en2un h1)))
      ?_
      ?_
    rotate_left
    ·
      simp [rfind'_obtain] at asd ⊢
      have := rfind'_obtain_prop_6 (en2e h2)
      simp [rfind'_obtain] at this
      rw [asd] at this
      have := this 1 (le_add_left 1 roM1)
      simp [Nat.add_comm] at this
      have := (Part.eq_get_iff_mem (en2e evalnindtdom)).mpr this
      rw [← this]
      rw [←add_assoc]
      simp only [reduceSubDiff, add_tsub_cancel_left]
    ·
      rw [←h]
      if hroM1:roM1=0 then
        simp [hroM1] at ⊢ nrop6 nrop
        have nropleft := nrop.left
        rw [add_comm] at nropleft
        have : ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).get usenindtdom) = ((usen O cf (k + 1) (Nat.pair x.l (x.r + 1))).get (en2un aux0)) := by
          have := nrop6 1 (le_rfl)
          simp at this
          have : k=k-1+1 := by exact nrf_aux usenindtdom
          simp (config:={singlePass:=true}) [this]
          simp [usen]
          simp [←this]
          simp [nropleft]
          exact usen_sing'
        rw [this]
      else
        clear ih
        simp [hroM1]
        have roM1M1: roM1 = roM1-1+1 := Eq.symm (succ_pred_eq_of_ne_zero hroM1)
        simp (config:={singlePass:=true}) [roM1M1] at *
        have : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1 + 1))).isSome := by
          have := nrop6 (1+1) (le_add_left (1 + 1) (roM1 - 1))
          simp only [reduceSubDiff] at this
          have := Option.isSome_of_mem this
          ac_nf at this ⊢
          simp at this ⊢
          exact usen_mono_dom (show k-1≤k from sub_le k 1) (en2un this)
        simp [isSome.bind this]
        apply congrArg
        apply congrArg

        have kkk : k=k-1+1 :=  nrf_aux usenindtdom
        simp [show (usen O cf.rfind' k (Nat.pair x.l (x.r + 1))) = (usen O cf.rfind' (k-1+1) (Nat.pair x.l (x.r + 1))) from congrFun
          (congrArg (usen O cf.rfind') kkk) (Nat.pair x.l (x.r + 1))]

        simp [usen]

        have auxdom1 : (evaln O k cf (Nat.pair x.l (x.r + 1))).isSome := by
          have := nrop.right.left 1 (le_add_left 1 (roM1 - 1 + 1))
          simp at this
          rwa [add_comm]
        have r1 : (evaln O k cf (Nat.pair x.l (x.r + 1))).get auxdom1 ≠ 0 := by
          have := nrop.right.right 1 (one_lt_succ_succ (roM1 - 1))
          simp at this
          rw [add_comm] at this
          contrapose this
          simp at this ⊢
          rw [←this]
          simp
        simp at this
        rw [add_comm] at this
        simp [←kkk]
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
    (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦
      some (((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
    =
  (if (evaln O (k + 1) cf.rfind' x).get h2 - x.r = 0 then (some (base'.max ((usen O cf (k + 1) x).get (en2un h1)))) else
    (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦
      some (base'.max $ ((usen O cf (k + 1) x).get (en2un h1)).max usen_indt))
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
  | zero => simp [isSome.bind $ en2un h1]
  | succ roM1 ih =>
    simp at ih ⊢
    intro asd h
    simp (config:={singlePass:=true}) [listrwgen] at h
    simp at h

    have nrop  := nrfind'_obtain_prop' h2
    have nrop4 := nrfind'_obtain_prop_4' h2
    have nrop6 := nrfind'_obtain_prop_6' h2
    rw [asd] at nrop nrop6 nrop4
    have nrop2 : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) (Nat.pair x.l (j + x.r))).isSome) := fun j a ↦ en2un (nrop.right.left j a)
    have asddom : (usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome := by
      have := nrop2 (roM1+1) (le_rfl)
      simp at this
      exact this
    simp [isSome.bind asddom] at h

    have usenindtdom : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).isSome := by
      have := nrop4 1 (le_add_left 1 roM1)
      simp at this
      rw [add_comm]
      exact en2un this
    have evalnindtdom := un2en usenindtdom
    have nrfindt := nrf usenindtdom

    have aux0 : (evaln O (k + 1) cf (Nat.pair x.l (x.r + 1))).isSome := by
      have := nrop.right.left 1 (le_add_left 1 roM1)
      simp at this
      rw [add_comm] at this
      exact evaln_mono_dom (show k≤k+1 from le_add_right k 1) this

    have ih1 := @ih
      (Nat.pair x.l (x.r+1))
      ?_
      ?_
      (base.max ((usen O cf (k+1) x).get (en2un h1)))
      ?_
      ?_
    rotate_left
    · exact Option.isSome_of_mem (evaln_mono (show k≤k+1 from le_add_right k 1) (Option.get_mem evalnindtdom))
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
      rw [←add_assoc]
      simp only [reduceSubDiff, add_tsub_cancel_left]
    ·
      simp
      have := @lemlemlem2 O k cf x roM1 (asddom) base h1 (en2un h1) (en2un aux0) (fun j a ↦ nrop2 j a)
      rw [this]
      exact h

    simp at ih1
    rw [←ih1]

    have usenindtdom : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).isSome := by
      have := nrop4 1 (le_add_left 1 roM1)
      rw [add_comm]
      exact en2un this
    simp [isSome.bind usenindtdom]
-- TODO:DUPLICATED (the below is duplciated from above)
    if hroM1:roM1=0 then
      simp [hroM1]

      simp [hroM1] at ⊢ nrop6 nrop
      have nropleft := nrop.left
      rw [add_comm] at nropleft
      have : ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).get usenindtdom) = ((usen O cf (k + 1) (Nat.pair x.l (x.r + 1))).get (en2un aux0)) := by
        have := nrop6 1 (le_rfl)
        simp at this
        have : k=k-1+1 := by exact nrf_aux usenindtdom
        simp (config:={singlePass:=true}) [this]
        simp [usen]
        simp [←this]
        simp [nropleft]
        exact usen_sing'
      rw [this]
    else
      clear ih
      simp [hroM1]
      have roM1M1: roM1 = roM1-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero hroM1)
      simp (config:={singlePass:=true}) [roM1M1] at *
      have : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1 + 1))).isSome := by
        have := nrop6 (1+1) (le_add_left (1 + 1) (roM1 - 1))
        simp only [reduceSubDiff] at this
        have := Option.isSome_of_mem this
        ac_nf at this ⊢
        simp at this ⊢
        exact usen_mono_dom (show k-1≤k from sub_le k 1) (en2un this)
      simp [isSome.bind this]
      apply congrArg
      apply congrArg

      have kkk : k=k-1+1 := by exact nrf_aux usenindtdom
      simp [show (usen O cf.rfind' k (Nat.pair x.l (x.r + 1))) = (usen O cf.rfind' (k-1+1) (Nat.pair x.l (x.r + 1))) from congrFun
        (congrArg (usen O cf.rfind') kkk) (Nat.pair x.l (x.r + 1))]

      simp [usen]

      have auxdom1 : (evaln O k cf (Nat.pair x.l (x.r + 1))).isSome := by
        have := nrop.right.left 1 (le_add_left 1 (roM1 - 1 + 1))
        simp at this
        rwa [add_comm]
      have r1 : (evaln O k cf (Nat.pair x.l (x.r + 1))).get auxdom1 ≠ 0 := by
        have := nrop.right.right 1 (one_lt_succ_succ (roM1 - 1))
        simp at this
        rw [add_comm] at this
        contrapose this
        simp at this ⊢
        rw [←this]
        simp
      simp at this
      rw [add_comm] at this
      simp [←kkk]
      simp [r1]
      apply congr
      apply congr
      exact rfl
      exact usen_sing'
      exact usen_sing'
theorem usen_rfind_prop2'
(h:(usen O (rfind' cf) (k + 1) x).isSome)
:
(usen O cf.rfind' (k + 1) x).get h
=
(do
  guard (x≤k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) (Nat.pair x.l (i+x.r)))
    max := Nat.max max usen_i
  max :Option ℕ).get (Option.isSome_of_mem (usen_rfind_prop2.mp (Option.get_mem h))) := by
  have := usen_rfind_prop2.mp (Option.get_mem h)
  exact
    Eq.symm
      (Option.get_of_eq_some (Option.isSome_of_mem (usen_rfind_prop2.mp (Option.get_mem h))) this)
theorem usen_rfind_prop2'' :
(usen O cf.rfind' (k + 1) x)=(do
  guard (x≤k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) (Nat.pair x.l (i+x.r)))
    max := Nat.max max usen_i
  max :Option ℕ)
  := by
    apply Option.eq_of_eq_some
    intro y
    exact usen_rfind_prop2
theorem usen_xles (h:(usen O c (s+1) x).isSome) : x≤s := le_of_lt_succ (usen_bound (Option.get_mem h))
theorem usen_sound : ∀ {c s n x}, x ∈ usen O c s n → x ∈ use O c n
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
    simp [←h]
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
    ·
      intro h1
      have h1 := h1.right
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
        ·
          have main := ih h3
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

    have nlek : n≤k := usen_xles (Option.isSome_of_mem h)
    simp [nlek] at this

    use h7
    constructor
    exact evaln_sound h8

    revert this
    revert urop1
    generalize 0=base
    -- revert 0
    induction h7 - n.r generalizing base with
    | zero =>
      -- simp [hind] at this
      simp
      intro h3 h4 this
      use (ForInStep.yield (base.max h1))
      constructor
      use h1
      constructor
      exact @hfih (k+1) (le_rfl) n h1 h2
      rfl
      simp_all
    | succ nn ih =>
      simp (config:={singlePass:=true}) [listrwgen]
      simp
      intro urop1
      have aux0 : (∀ j ≤ nn, ∃ y, usen O cf (k + 1 - j) (Nat.pair n.l (n.r + j)) = some y) := by
        intro j jnn
        exact urop1 j (le_add_right_of_le jnn)

      rcases urop1 (nn+1) (Nat.le_refl (nn + 1)) with ⟨h3,h4⟩
      simp at h4
      ac_nf at h4 ⊢
      simp [h4]

      have hf2 := @hfih (k-nn) (le_add_right_of_le (sub_le k nn)) (Nat.pair n.l (nn + (n.r+1))) h3 h4

      intro h5
      use (ForInStep.yield (base.max h3))
      constructor
      use h3
      exact ih (base.max h3) aux0 h5

lemma lemlemlem
{a n:ℕ}
(h6:h5 ∈ use O cf (Nat.pair n.l (nn + 1 + n.r)))
(rop3:∀ j ≤ nn + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
(h57dom:(use O cf n).Dom)
(h57def:h57=(use O cf n).get h57dom)
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
    simp [←(Part.eq_get_iff_mem this).mpr h6]
    ac_nf

  | succ nnn iihh =>
    -- sorry
    intro h6

    simp (config:={singlePass:=true}) [listrwgen]
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
    rw (config:={occs:=.pos [2]}) [Nat.max_comm]
lemma lemlemlem3
{a n use_steps:ℕ}
(h6:h5 ∈ use O cf (Nat.pair n.l (nn + 1 + n.r)))
(rop3:∀ j ≤ nn + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
(h57dom:(use O cf n).Dom)
(h57def:h57=(use O cf n).get h57dom)
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
    have : ∃z,z∈(usen O cf (kk + 1) (Nat.pair n.l (1 + n.r))) := by
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
    simp (config:={singlePass:=true}) [listrwgen] at hkk ⊢
    simp at hkk ⊢

    rcases hf h6 with ⟨g3,g4⟩
    have : ∃z,z∈(usen O cf (kk - nnn) (Nat.pair n.l (nnn + 1 + (1 + n.r)))) := by
      contrapose hkk
      simp at hkk
      have := Option.eq_none_iff_forall_ne_some.mpr hkk
      simp [this]
    rcases this with ⟨lmao3,lmao4⟩
    simp at lmao4
    simp [lmao4] at hkk ⊢
    rw [add_assoc] at g4
    simp [usen_sing lmao4 g4] at *

    have : ∃z,z∈(usen O cf (use_steps - nnn) (Nat.pair n.l (nnn + 1 + n.r))) := by
      contrapose hkk
      simp at hkk
      have := Option.eq_none_iff_forall_ne_some.mpr hkk
      simp (config:={singlePass:=true}) [listrwgen]
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
      rw (config:={occs:=.pos [2]}) [Nat.max_comm]
      exact hkk
    · exact Part.get_mem dom1
    ·
      rw (config:={occs:=.pos [2]}) [Nat.max_comm]
      have : g1 = ((use O cf (Nat.pair n.l (nnn + 1 + n.r))).get dom1) := by
        exact (Part.eq_get_iff_mem dom1).mpr (usen_sound g2)
      rw [this]
      exact iihh2

-- set_option diagnostics true in
set_option maxHeartbeats 1000000 in
theorem usen_complete {c n x} : x ∈ use O c n ↔ ∃ s, x ∈ usen O c s n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => usen_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ usen O  c (k + 1) n
  · exact ⟨k + 1, h⟩

  induction c generalizing n x with
      -- simp [use, usen, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    simp [use, usen, pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    -- constructor

    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    simp [use, usen, pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨y, hy, ⟨hx1,⟨hx2,⟨hx3,⟨hx4,hx5⟩⟩⟩⟩⟩
    -- rcases h with ⟨y, hy, ⟨hx1,hx2⟩⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx4 with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩

    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        ?_⟩

    use hx1
    constructor
    ·
      rcases usen_dom_iff_evaln_dom.mp (Exists.intro y hk₁) with ⟨b,hb⟩
      rcases evaln_complete.mp hx2 with ⟨kk,hkk⟩
      rw [evaln_sing hkk hb]
      exact evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hb
    ·
      refine ⟨_,usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂,
      (by subst hx5; exact Nat.max_comm hx3 y) ⟩
  | prec cf cg hf hg =>
    simp [use, usen, pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    revert h
    generalize n.l = n₁; generalize n.r = n₂
    -- induction' n₂ with m IH generalizing x n <;> simp [Option.bind_eq_some_iff]
    induction' n₂ with m IH generalizing x n
    ·
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    ·
      -- intro y hy hx
      intro h
      simp at h
      rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
      rcases IH h4 with ⟨k₁, nk₁, hk₁⟩
      rcases hg h6 with ⟨k₂, hk₂⟩

      refine ⟨(max k₁ k₂).succ,Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁,
            ?_
            ⟩

      simp
      subst h7
      simp_all only [Option.mem_def, sup_le_iff]
      obtain ⟨left, right⟩ := nk₁

      have aux1 : h5 ∈ (usen O cg (max k₁ k₂ + 1 + 1) (Nat.pair n₁ (Nat.pair m h1))) := by
        simp
        have : k₂+1 ≤ max k₁ k₂ + 1 + 1:= by
          apply Nat.add_le_add_iff_right.mpr
          apply le_add_right_of_le
          apply le_sup_right
        exact usen_mono this hk₂
      have aux2 : h3 ∈ (usen O (cf.prec cg) (max k₁ k₂ + 1) (Nat.pair n₁ m)) := by
        -- have aux_aux : Nat.pair n₁ m ≤ k₁ := by exact right
        have : Nat.rec (usen O cf (k₁ + 1) n₁) (fun n n_ih ↦
            (usen O (cf.prec cg) k₁ (Nat.pair n₁ n)).bind fun usen_prev ↦
            (evaln O k₁ (cf.prec cg) (Nat.pair n₁ n)).bind fun evaln_prev ↦
            (usen O cg (k₁ + 1) (Nat.pair n₁ (Nat.pair n evaln_prev))).bind fun usen_indt ↦
            some (usen_prev.max usen_indt)) m = (usen O (cf.prec cg) ( k₁ + 1) (Nat.pair n₁ m)) := by
          simp [usen]
          simp [right]

        rw [this] at hk₁

        have : (k₁ + 1) ≤ (max k₁ k₂ + 1) := by
          apply Nat.add_le_add_iff_right.mpr
          apply le_sup_left
        exact usen_mono this hk₁
      have aux0 : h1 ∈ (evaln O (max k₁ k₂ + 1) (cf.prec cg) (Nat.pair n₁ m)) := by
        rcases usen_dom_iff_evaln_dom.mp ⟨h3, aux2⟩ with ⟨hh1,hh2⟩
        rcases evaln_complete.mp h2 with ⟨hh3,hh4⟩
        rwa [evaln_sing hh2 hh4] at hh2
      rw [aux2]
      rw [aux0]
      simp
      rw [aux1]
      simp


  | rfind' cf hf =>
    -- #check use_rfind'_
    simp [use] at h
    suffices ∃k,x∈(do
  guard (n≤k);
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

    have rogeq : n.r≤h1 := eval_rfind_prop5 h2
    rw [show h1=h1-n.r+n.r from by simp [rogeq]] at h2
    clear rogeq



    have hdom1 := Part.dom_iff_mem.mpr ⟨h1-n.r+n.r,h2⟩
    have hdom : (use O cf.rfind' n).Dom := use_dom_iff_eval_dom.mpr hdom1
    have rop := rfind'_obtain_prop hdom1
    have rop4 := rfind'_obtain_prop_4 hdom1
    have rop6 := rfind'_obtain_prop_6 hdom1
    have urop1 := use_rfind_prop hdom
    have h145: rfind'_obtain (u2e hdom) = h1 - n.r := by
      simp [rfind'_obtain]
      simp [Part.eq_some_iff.mpr h2]
    simp [h145] at *
    clear h145

    revert h3
    revert h2
    revert urop1
    revert rop6
    revert rop4
    revert rop

    induction h1-n.r generalizing a n with
    | zero =>
      simp_all
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
      simp (config:={singlePass:=true}) [listrwgen]
      simp
      intro urop1 rop1 rop2 rop4 rop6 rop3 h2 h3 h5 h6 h7 h8

      have rop10 := rop1 1 (le_add_left 1 nn)
      have rop11 := e2u rop10
      have rop40 := rop4 1 (le_add_left 1 nn)
      have rop41 := e2u rop40

      have h57dom := rop3 0 (le_add_left 0 (nn + 1))
      simp at h57dom
      let h57 := (use O cf n).get h57dom

      have ih1 := @ih (Nat.pair n.l (1 + n.r)) (a.max h57) (rop40) rop41 ?_ ?_ ?_ ?_ ?_
      clear ih
      rotate_right 5
      · simp
        constructor
        -- rw [←add_assoc]
        ac_nf at urop1 ⊢
        -- exact urop1
        constructor
        intro j hj
        have := rop1 (j+1) (Nat.add_le_add_right hj 1)
        rw [←add_assoc]
        exact rop1 (j+1) (Nat.add_le_add_right hj 1)
        intro j hj
        rw [←add_assoc]
        exact rop2 (j+1) (Nat.add_le_add_right hj 1)
      · simp
        intro j hj
        -- ac_nf
        rw [←add_assoc]
        exact rop4 (j+1) (Nat.add_le_add_right hj 1)
      ·
        simp
        intro j hj
        rw [←add_assoc]
        rw [←add_assoc]
        exact rop6 (j+1) (Nat.add_le_add_right hj 1)
      ·
        simp
        intro j hj
        rw [add_comm]
        rw [←add_assoc]
        exact e2u (rop1 (j+1) (Nat.add_le_add_right hj 1))
      ·
        simp
        rw [←add_assoc]
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
      have : ∃z,z∈ (evaln O (kk + 1) cf.rfind' (Nat.pair n.l (1 + n.r))) := by
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
        rw [←h10]
        apply evaln_mono' (Option.isSome_of_mem h10) _
        grind
      simp [this]

      have : (usen O cf (use_steps-nn) (Nat.pair n.l (nn + 1 + n.r))) = some h5 := by
        rw [←h15]
        apply usen_mono' (Option.isSome_of_mem h15) _
        grind
      simp [this]

      have aux1 : usen O cf (use_steps + 1) n = some ((use O cf n).get h57dom) := by
        rw [←i2]
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

theorem use_eq_rfindOpt (c n) : use O c n = Nat.rfindOpt fun k => usen O c k n :=
  Part.ext fun x => by
    refine usen_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply usen_mono hl


theorem evaln_pair_dom (h:(evaln O (s+1) (pair cf cg) x).isSome) : (evaln O (s+1) cf x).isSome ∧ (evaln O (s+1) cg x).isSome := by
  have := evaln_xles h
  contrapose h
  push_neg at h
  simp [evaln, Seq.seq]
  simp [this]
  aesop? says
    intro a a_1
    simp_all only [Option.isSome_some, ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      forall_const]
theorem evaln_comp_dom_aux (h:(evaln O (s+1) (comp cf cg) x).isSome) : (evaln O (s+1) cg x).isSome := by
  have h':= h
  simp [evaln] at h'
  simp [evaln_xles h] at h'
  contrapose h'
  simp at h'
  simp [h']
theorem evaln_comp_dom
(h:(evaln O (s+1) (comp cf cg) x).isSome)
:
(evaln O (s+1) cg x).isSome
∧
(evaln O (s+1) cf ((evaln O (s+1) cg x).get (evaln_comp_dom_aux h))).isSome
:= by
  constructor
  · exact evaln_comp_dom_aux h
  ·
    have h' := h
    simp [evaln] at h'
    contrapose h'
    simp at h'
    simp [evaln_xles h]
    intro h1 h2
    simp_all only [Option.get_some]
theorem evaln_prec_dom_aux
(h:(evaln O (s+1) (prec cf cg) (Nat.pair x (i+1))).isSome)
:
(evaln O s (prec cf cg) (Nat.pair x i)).isSome
:= by
  have h':=h
  simp [evaln] at h' ⊢
  simp [evaln_xles h] at h'
  contrapose h'
  simp at h'
  simp [h']
theorem evaln_prec_dom'
(h:(evaln O (s+1) (prec cf cg) (Nat.pair x 0)).isSome)
:
(evaln O (s+1) cf x).isSome
:= by
  have h':= h
  simp [evaln] at h'
  simp [evaln_xles h] at h'
  exact h'
theorem evaln_prec_dom
(h:(evaln O (s+1) (prec cf cg) (Nat.pair x (i+1))).isSome)
:
(evaln O (s-i) cf x).isSome ∧
(
let evaln_prev := (evaln O s (prec cf cg) (Nat.pair x i)).get (evaln_prec_dom_aux h)
(evaln O (s+1) cg (Nat.pair x (Nat.pair i (evaln_prev)))).isSome
)
:= by
  induction i generalizing s with
  | zero =>
    have h':=h
    simp [evaln] at h' ⊢
    simp [evaln_xles h] at h'
    have := evaln_prec_dom_aux h
    have sG1 := evaln_sG1 this
    simp (config:={singlePass:=true}) [sG1] at h' ⊢
    simp [evaln] at h' ⊢
    simp [evaln_xles' (this)] at h' ⊢
    simp [← sG1] at h' ⊢
    contrapose h'
    simp at h' ⊢
    intro h1 h2
    simp_all [-sG1]
  | succ iM1 ih =>
    have h':=h
    simp [evaln] at h'
    simp [evaln_xles h] at h'
    constructor
    ·
      have aux0 := evaln_prec_dom_aux h
      have sG1 := evaln_sG1 aux0
      have aux1 := evaln_mono_dom (show s≤s+1 from le_add_right s 1) aux0
      have ih1 := @ih (s-1) ?_
      rotate_left
      ·
        rw [←sG1]
        exact aux0
      have : s - (iM1 + 1) = s - 1 - iM1 := by exact Simproc.sub_add_eq_comm s iM1 1
      rw [this]
      exact ih1.left

    · simp
      have aux0 := evaln_prec_dom_aux h
      simp [isSome.bind aux0] at h'
      exact h'
theorem usen_pair_dom (h:(usen O (pair cf cg) (s+1) x).isSome) : (usen O cf (s+1) x).isSome ∧ (usen O cg (s+1) x).isSome := by
  have := usen_xles h
  contrapose h
  push_neg at h
  simp [usen]
  simp [this]
  aesop
theorem usen_comp_dom_aux (h:(usen O (comp cf cg) (s+1) x).isSome) : (evaln O (s+1) cg x).isSome := by
  have hog := h
  simp [usen] at h
  simp [usen_xles hog] at h

  contrapose h
  simp at h
  simp [h]
theorem usen_comp_dom (h:(usen O (comp cf cg) (s+1) x).isSome) : (usen O cg (s+1) x).isSome ∧ (usen O cf (s+1) ((evaln O (s+1) cg x).get (usen_comp_dom_aux h))).isSome := by
  have hog := h
  simp [usen] at h
  simp [usen_xles hog] at h

  contrapose h
  simp at h
  simp
  intro a b c d e
  simp_all only [Option.isSome_some, Option.get_some, forall_const, reduceCtorEq, not_false_eq_true]
theorem usen_prec_dom_aux
(h:(usen O (prec cf cg) (s+1) (Nat.pair x (i+1))).isSome)
:
(evaln O s (prec cf cg) (Nat.pair x i)).isSome
:= by
  simp [usen] at h
  contrapose h
  simp
  aesop? says
    intro a a_1 a_2 a_3 a_4 a_5
    simp_all only [Option.isSome_some, not_true_eq_false]
theorem usen_prec_dom'
(h:(usen O (prec cf cg) (s+1) (Nat.pair x 0)).isSome)
:
(usen O cf (s+1) x).isSome
:= by
  have h':= h
  simp [usen] at h'
  simp [usen_xles h] at h'
  exact h'
theorem usen_prec_dom
(h:(usen O (prec cf cg) (s+1) (Nat.pair x (i+1))).isSome)
:
(usen O cf (s-i) x).isSome
∧
(
let eval_prev := (evaln O s (prec cf cg) (Nat.pair x i)).get (usen_prec_dom_aux h)
(usen O cg (s+1) (Nat.pair x (Nat.pair i eval_prev))).isSome)
:= by
  have h':=h
  simp [usen] at h'
  simp [usen_xles h] at h'
  simp [isSome.bind (en2un $ usen_prec_dom_aux h)] at h'
  simp [isSome.bind (usen_prec_dom_aux h)] at h'
  simp []

  induction i generalizing s with
  | zero =>
    have h':=h
    simp [usen] at h' ⊢
    simp [usen_xles h] at h'
    have eprev := usen_prec_dom_aux h
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev
    simp (config:={singlePass:=true}) [sG1] at eprev
    have := evaln_prec_dom' eprev
    rw [←sG1] at this eprev

    constructor
    · exact en2un this

    simp [isSome.bind uprev] at h'
    simp [isSome.bind eprev] at h'

    contrapose h'
    simp at h'
    simp [h']

  | succ iM1 ih =>
    have h':=h
    simp [usen] at h'
    simp [usen_xles h] at h'
    have eprev := usen_prec_dom_aux h
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev
    constructor
    ·
      have ih1 := @ih (s-1) ?_ ?_
      rotate_left
      · rwa [←sG1]
      ·
        rw [sG1] at uprev
        let u:=uprev
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
theorem usen_rfind'_dom
(h:(usen O (rfind' cf) (s+1) x).isSome) :
∀ j ≤ nrfind'_obtain (un2en h),
  (usen O cf (s+1-j) (Nat.pair x.l (j+x.r))).isSome := by
  have aux0 := (nrfind'_obtain_prop (un2en h)).right.left
  exact fun j a ↦ en2un (aux0 j a)
theorem usen_mono_pair (hh:(usen O (pair cf cg) (s+1) x).isSome):
  ((usen O cf (s+1) x).get ((usen_pair_dom hh).left) ≤ (usen O (pair cf cg) (s+1) x).get hh)
  ∧
  ((usen O cg (s+1) x).get ((usen_pair_dom hh).right) ≤ (usen O (pair cf cg) (s+1) x).get hh)
  := by
    simp only [usen]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.get_bind, Option.get_some, le_sup_left,
      le_sup_right, and_self]
theorem usen_mono_comp (hh:(usen O (comp cf cg) (s+1) x).isSome):
  ((usen O cg (s+1) x).get ((usen_comp_dom hh).left) ≤ (usen O (comp cf cg) (s+1) x).get hh)
  ∧
  ((usen O cf (s+1) ((evaln O (s+1) cg x).get (usen_comp_dom_aux hh))).get ((usen_comp_dom hh).right) ≤ (usen O (comp cf cg) (s+1) x).get hh)
  := by
    simp [usen]
theorem usen_mono_prec' (hh:(usen O (prec cf cg) (s+1) (Nat.pair x 0)).isSome):
((usen O cf (s+1) x).get (usen_prec_dom' hh) ≤ (usen O (prec cf cg) (s+1) (Nat.pair x 0)).get hh)
:= by
  simp [usen]
theorem usen_mono_prec_1 (hh:(usen O (prec cf cg) (s+1) (Nat.pair x (i+1))).isSome):
(usen O (prec cf cg) (s) (Nat.pair x i)).get (en2un $ usen_prec_dom_aux hh) ≤ (usen O (prec cf cg) (s+1) (Nat.pair x (i+1))).get hh
  := by
    simp [usen.eq_9]
-- todo: simplify below proof
theorem usen_mono_prec (hh:(usen O (prec cf cg) (s+1) (Nat.pair x (i+1))).isSome):
((usen O cf (s-i) x).get ((usen_prec_dom hh).left) ≤ (usen O (prec cf cg) (s+1) (Nat.pair x (i+1))).get hh)
∧
let eval_prev := (evaln O s (prec cf cg) (Nat.pair x i)).get (usen_prec_dom_aux hh)
(
(usen O cg (s+1) (Nat.pair x (Nat.pair i eval_prev))).get ((usen_prec_dom hh).right) ≤ (usen O (prec cf cg) (s+1) (Nat.pair x (i+1))).get hh
)
  := by
  induction i generalizing s with
  | zero =>
    simp only [usen]
    simp

    have h':=hh
    simp [usen] at h' ⊢
    simp [usen_xles hh] at h'
    have eprev := usen_prec_dom_aux hh
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev

    apply Or.inl
    simp (config:={singlePass:=true}) [sG1]
    simp [usen]
  | succ n ih =>
    have h':=hh
    simp [usen] at h' ⊢
    simp [usen_xles hh] at h'
    have eprev := usen_prec_dom_aux hh
    have uprev := en2un eprev
    have sG1 := evaln_sG1 eprev

    have ih1 := @ih (s-1) ?_
    rotate_left
    ·
      rw [←sG1]
      exact uprev
    simp at ih1
    have : s - (n + 1) = s-1-n := by exact Simproc.sub_add_eq_comm s n 1
    simp [this]
    simp [←sG1] at ih1
    apply Or.inl ih1.left


lemma cm_aux_0
{l}
{head :ℕ}
{tail : List ℕ}
(hhht : ∃ l'', l'' ++ l' = l)
(hht : head :: tail = l')
:
∃ l'':List ℕ, l'' ++ head :: tail = l
:= by
  grind
lemma cm_aux_1
{l}
{head :ℕ}
{tail : List ℕ}
(hhht : ∃ l'', l'' ++ l' = l)
(hht : head :: tail = l')
:
∃ l'', l'' ++ tail = l
:= by
  rcases hhht with ⟨h1,h2⟩
  use h1 ++ [head]
  aesop? says
    subst h2 hht
    simp_all only [List.append_assoc, List.cons_append, List.nil_append]
theorem clause_mono_2
{base1 base2 : ℕ}
{l:List ℕ}
{f:(a:ℕ)→(l':List ℕ)→(∃l'',l''++l'=l)→(a∈l')→ℕ}
(hf:∀ a head tail (m:a∈tail) (l':List ℕ) (hhht:∃l'',l''++l'=l) (hht:head::tail=l'), (f a (head :: tail) (cm_aux_0 hhht hht) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = f a tail (cm_aux_1 hhht hht) m)
{h:∀ (l') (base:ℕ) (htt:∃l'',l''++l'=l),  (forIn' (l') (base) fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l' (htt) h)))).Dom}
{h2:base1≤base2}
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
      exact ⟨head::h1,Eq.symm (List.append_cancel_left (congrArg (HAppend.hAppend tail) (congrArg (List.cons head) (_root_.id (Eq.symm h2)))))⟩
    have ihmain :
    ∀ (l' : List ℕ) (base : ℕ) (htt:∃ l'', l'' ++ l' = tail),
       (forIn' l' base fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l' (httconv htt) h)))).Dom
      := by
      intro l' base h1
      rcases h1 with ⟨l'',hl''⟩
      have : (head::l'') ++ l' = head :: tail := by simp [hl'']
      exact h l' base  ⟨(head::l''),this⟩
    let addendum := (f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self))
    have ihmain2 : base1.max addendum ≤ base2.max addendum := by exact sup_le_sup_right h2 addendum
    have ihmain0 : (∀ (a head : ℕ) (tail_1 : List ℕ) (m : a ∈ tail_1) (l' : List ℕ) (hhht : ∃ l'', l'' ++ l' = tail)
    (hht : head :: tail_1 = l'), f a (head :: tail_1) (httconv (cm_aux_0 hhht hht)) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail_1) a m)) = f a tail_1 (httconv (cm_aux_1 hhht hht)) m) := by
      intro a head tail_1 m l' hhht hht
      exact hf a head tail_1 m l' (httconv hhht) hht

    have ih1 := @ih (base1.max addendum) (base2.max addendum) (fun a l' h hl => f a l' (httconv h) hl) ihmain0 ihmain ihmain2

    simp [show f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self) = addendum from rfl]

    have aux (a:ℕ) (m:a∈tail): (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = (f a tail (httconv ⟨[],rfl⟩) m):= by
      exact hf a head tail m (head :: tail) ⟨[],rfl⟩ rfl
    have :
    (fun a m (b:ℕ) ↦ Part.some (ForInStep.yield (b.max (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))))))
    =
    fun a m (b:ℕ) ↦ Part.some (ForInStep.yield (b.max (f a tail (httconv ⟨[],rfl⟩) m)))
    := by
      funext a m b
      simp [aux a m]

    simp [this]
    exact ⟨ih1.left, le_of_max_le_left ih1.right⟩
theorem clause_mono_2_opt
{base1 base2 : ℕ}
{l:List ℕ}
{f:(a:ℕ)→(l':List ℕ)→(∃l'',l''++l'=l)→(a∈l')→ℕ}
(hf:∀ a head tail (m:a∈tail) (l':List ℕ) (hhht:∃l'',l''++l'=l) (hht:head::tail=l'), (f a (head :: tail) (cm_aux_0 hhht hht) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = f a tail (cm_aux_1 hhht hht) m)
{h:∀ (l') (base:ℕ) (htt:∃l'',l''++l'=l),  (forIn' (l') (base) fun a h b ↦ some (ForInStep.yield (b.max (f a l' (htt) h)))).isSome}
{h2:base1≤base2}
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
      exact ⟨head::h1,Eq.symm (List.append_cancel_left (congrArg (HAppend.hAppend tail) (congrArg (List.cons head) (_root_.id (Eq.symm h2)))))⟩
    have ihmain :
    ∀ (l' : List ℕ) (base : ℕ) (htt:∃ l'', l'' ++ l' = tail),
       (forIn' l' base fun a h b ↦ some (ForInStep.yield (b.max (f a l' (httconv htt) h)))).isSome
      := by
      intro l' base h1
      rcases h1 with ⟨l'',hl''⟩
      have : (head::l'') ++ l' = head :: tail := by simp [hl'']
      exact h l' base  ⟨(head::l''),this⟩
    let addendum := (f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self))
    have ihmain2 : base1.max addendum ≤ base2.max addendum := by exact sup_le_sup_right h2 addendum
    have ihmain0 : (∀ (a head : ℕ) (tail_1 : List ℕ) (m : a ∈ tail_1) (l' : List ℕ) (hhht : ∃ l'', l'' ++ l' = tail)
    (hht : head :: tail_1 = l'), f a (head :: tail_1) (httconv (cm_aux_0 hhht hht)) (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail_1) a m)) = f a tail_1 (httconv (cm_aux_1 hhht hht)) m) := by
      intro a head tail_1 m l' hhht hht
      exact hf a head tail_1 m l' (httconv hhht) hht
    have ih1 := @ih (base1.max addendum) (base2.max addendum) (fun a l' h hl => f a l' (httconv h) hl) ihmain0 ihmain ihmain2

    simp [show f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self) = addendum from rfl]

    have aux (a:ℕ) (m:a∈tail): (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = (f a tail (httconv ⟨[],rfl⟩) m):= by
      exact hf a head tail m (head :: tail) ⟨[],rfl⟩ rfl

    have :
    (fun a m (b:ℕ) ↦ some (ForInStep.yield (b.max (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))))))
    =
    fun a m (b:ℕ) ↦ some (ForInStep.yield (b.max (f a tail (httconv ⟨[],rfl⟩) m)))
    := by
      funext a m b
      simp [aux a m]
    simp [this]
    exact ⟨ih1.left,le_of_max_le_left ih1.right⟩


theorem le_of_le_sub {a b :ℕ}(h:a≤b-c): a≤b := by
  grind

lemma listrevlem (h:∃ l'':List ℕ, l'' ++ l' = (List.range x).reverse) : ∃ y, l'=(List.range y).reverse∧y≤x := by
  rcases h with ⟨h1,h2⟩
  induction h1 generalizing x with
  | nil =>
    simp at h2
    aesop
  | cons head tail ih =>
    simp at h2
    have : x>0 := by
      grind only [=_ List.cons_append, = List.range_zero, List.reverse_nil, → List.eq_nil_of_append_eq_nil]
    have : tail ++ l' = (List.range (x-1)).reverse := by
      rw [show x=x-1+1 from (Nat.sub_eq_iff_eq_add this).mp rfl] at h2
      simp [listrwgen] at h2
      simp_all only [List.reverse_inj, gt_iff_lt]
    have := @ih (x-1) this

    grind
lemma listrevlem2 (h:∃ l'':List ℕ, l'' ++ l' = (List.range x).reverse) (h2:a∈l') : a<x := by
  have := listrevlem h
  grind

theorem usen_mono_rfind'
(hh:(usen O (rfind' cf) (s+1) x).isSome):
∀ hj:j ≤ nrfind'_obtain (un2en hh),
  (usen O cf (s+1-j) (Nat.pair x.l (j+x.r))).get (usen_rfind'_dom hh j hj) ≤ (usen O (rfind' cf) (s+1) x).get hh
  := by

  intro hjro
  have rop := nrfind'_obtain_prop (un2en hh)
  let ro := nrfind'_obtain (un2en hh)
  have rwro : nrfind'_obtain (un2en hh) = ro := rfl
  simp [rwro] at rop hjro
  have rop1 := rop.left
  have rop2 := rop.right.left
  have rop3 := rop.right.right
  have rop4 := nrfind'_obtain_prop_4 (un2en hh)
  simp [rwro] at rop4

  have aux3 := rop2 0 (Nat.zero_le ro)
  simp at aux3
  have aux5 := rop2 j hjro

  simp [usen_rfind_prop2']
  -- simp [usen]
  -- simp [Part.Dom.bind (u2e hh)]
  -- simp [isSome.bind (un2en hh)]
  -- simp [Part.Dom.bind (e2u aux3)]
  -- simp [Part.Dom.bind (aux3)]
  have rwro2 : (evaln O (s+1) (rfind' cf) x).get (un2en hh) - x.r = ro := rfl
  simp [rwro2]

  simp only [forIn_eq_forIn']

  -- simp (config := { singlePass := true }) [List.reverse]
  have domaux1 {i} (h : i ∈ (List.range (ro + 1)).reverse) : i≤ro := by
    grind
  have :
      (fun i h r ↦
      (usen O cf (s+1-i) (Nat.pair x.l (i + x.r))).bind fun use_i
      ↦ some (ForInStep.yield (r.max use_i))
      : (i : ℕ) → i ∈ (List.range (ro + 1)).reverse → ℕ → Option (ForInStep ℕ))
    = (fun i h r ↦
        some (ForInStep.yield (r.max
        -- ((use O cf (Nat.pair x.l (i + x.r))).get (e2u $ rop2 (ro-i) (sub_le ro i)))
        ((usen O cf (s+1-i) (Nat.pair x.l (i + x.r))).get (en2un $ rop2 i (domaux1 h)))
        ))

      : (i : ℕ) → i ∈ (List.range (ro + 1)).reverse → ℕ → Option (ForInStep ℕ)) := by
        funext i h r
        -- simp [Part.Dom.bind (e2u $ rop2 (ro-i) (sub_le ro i))]
        simp [isSome.bind (en2un $ rop2 i (domaux1 h))]
  simp [this]


  have listrw : (List.range (ro + 1)).reverse = ro :: (List.range ro).reverse := by
    simp
    exact List.range_succ
  simp [listrw]
  -- have : (List.range' 0 (ro + 1)) = (List.range' 0 (ro + 1))
  -- (List.range' k (ro + 1 - k))


  -- show 3 things.
  -- 1. that basecase ≤ forIn l ~
  -- 2. that use @ j ≤ forin range j ~
  -- 3. that forin range j ~ ≤ forin range full.
  -- simp only [forIn_eq_forIn']
  have : (usen O cf (s+1) x).isSome := by exact en2un aux3
  have domaux2 : (usen O cf (s+1-ro) (Nat.pair x.l (ro + x.r))).isSome := en2un $ rop2 ro le_rfl
  have domaux3aux {a' k} (h0:k≤ro) (h:a' ∈ (List.range k).reverse) : a' ∈ (List.range ro).reverse  := by
    simp at h ⊢
    exact Nat.lt_of_lt_of_le h h0
    -- exact?
  have domaux3 (a' k m) (h0:k≤ro) := en2un (rop2 a' (domaux1 (List.forIn'_congr._proof_1 listrw a' (List.mem_cons_of_mem ro (domaux3aux h0 m)))))
  have forInDom {k :ℕ} (base:ℕ) (h:k≤ro):
  (forIn' (List.range k).reverse (base) fun a' m b ↦
        some (ForInStep.yield (b.max ((usen O cf (s+1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' k m h))))).isSome := by
    induction k generalizing base with
    | zero =>
      simp
    | succ n ih =>
      simp [listrwgen, -forIn'_eq_forIn]
      have auxdom4 : (usen O cf (s+1-n) (Nat.pair x.l (n + x.r))).isSome := by
        aesop? says
          rename_i hjro_1 this_1
          simp_all [ro]
          apply domaux3
          on_goal 2 => simp_all only [ro]
          on_goal 2 => rfl
          simp_all only [List.mem_reverse, List.mem_range]
          exact h
      have := @ih (base.max ((usen O cf (s+1-n) (Nat.pair x.l (n + x.r))).get auxdom4)) (le_of_succ_le h)
      aesop? says
        simp_all only [implies_true, not_false_eq_true, and_self,List.mem_reverse, List.mem_range, ro]

  have auxdom5:(usen O cf (s+1-j) (Nat.pair x.l (j + x.r))).isSome:= by (expose_names; exact usen_rfind'_dom hh j hjro_1)
  have auxdom8 (k:ℕ):(usen O cf (s+1-(ro-k)) (Nat.pair x.l (ro - k + x.r))).isSome:= usen_rfind'_dom hh (ro-k) (sub_le ro k)
  have auxdom6:= forInDom ((usen O cf (s+1-ro) (Nat.pair x.l (ro + x.r))).get domaux2) hjro
  have auxdom9 (k:ℕ):= forInDom ((usen O cf (s+1-(ro-k)) (Nat.pair x.l (ro -k + x.r))).get (auxdom8 k)) (sub_le ro k)
  have auxdom7:= forInDom ((usen O cf (s+1-ro) (Nat.pair x.l (ro + x.r))).get domaux2) le_rfl
  have auxdom10 :=forInDom ((usen O cf (s+1-j) (Nat.pair x.l (j + x.r))).get auxdom5) hjro
  have main2:
    -- (use O cf (Nat.pair x.l (j + x.r))).get auxdom5 ≤ (forIn' (List.range j).reverse ((use O cf (Nat.pair x.l (ro + x.r))).get domaux2) fun a' m b ↦ Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (a' + x.r))).get (domaux3 a' j m hjro))))).get auxdom6 := by
    (usen O cf (s+1-j) (Nat.pair x.l (j + x.r))).get auxdom5 ≤ (forIn' (List.range j).reverse ((usen O cf (s+1-j) (Nat.pair x.l (j + x.r))).get (auxdom5)) fun a' m b ↦ some (ForInStep.yield (b.max ((usen O cf (s+1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' j m hjro))))).get auxdom10:= by
      -- wait this should be literally just an application of main1.
      let base := (usen O cf (s+1-j) (Nat.pair x.l (j + x.r))).get auxdom5
      simp [show (usen O cf (s+1-j) (Nat.pair x.l (j + x.r))).get auxdom5 = base from rfl]
      let f (a : ℕ) (l' : List ℕ) (h2:∃ l'':List ℕ, l'' ++ l' = (List.range j).reverse) (h3:a ∈ l')
            := (usen O cf (s+1-a) (Nat.pair x.l (a + x.r))).get (
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
        have : h1≤ro := by (expose_names; exact Nat.le_trans h3 hjro_1)
        exact forInDom base this
      have := (@clause_mono_2_opt base base (List.range j).reverse f (fun a head tail m l' hhht hht ↦ rfl) bigaux (le_rfl)).right

      apply this
  -- here we are saying, starting calculations from j, we'll get smaller results bc we're not taking into account the values j~ro.

  have main3 :
    ∀k,
    (forIn' (List.range (ro-k)).reverse ((usen O cf (s+1-(ro-k)) (Nat.pair x.l ((ro-k) + x.r))).get (auxdom8 k)) fun a' m b ↦ some (ForInStep.yield (b.max ((usen O cf (s+1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' (ro-k) m (sub_le ro k)))))).get (auxdom9 k)
    ≤
    (forIn' (List.range ro).reverse ((usen O cf (s+1-ro) (Nat.pair x.l (ro + x.r))).get domaux2) fun a' m b ↦ some (ForInStep.yield (b.max ((usen O cf (s+1-a') (Nat.pair x.l (a' + x.r))).get (domaux3 a' ro m (le_rfl)))))).get auxdom7
    := by
      intro k
      induction k with
      | zero =>
        simp
      | succ n ih =>
        -- do cases on if ro-n≤0
        cases Nat.eq_zero_or_pos (ro - n) with
        | inl hh =>
          simp [show ro-(n+1)=ro-n-1 from rfl]
          have : ro-n-1=ro-n := by exact sub_one_eq_self.mpr hh
          simp [this]
          exact ih
        | inr hh =>
          -- we want to say:
          -- ih:has all calculations from 0 to ro-k
          -- want to show: all calculations from 0 to ro-k-1
          -- i need to show that lhs of goal is leq lhs of ih.
          -- for that, i need a theorem saying that in this max forin thing,
          -- if everything is the same but the basecase of L is leq R
          -- then L leq R.
          have ronrw0 : ro-(n+1)=ro-n-1 := rfl
          simp [ronrw0]
          have ronrw : ro-n = ro-n-1+1 := by exact Eq.symm (Nat.sub_add_cancel hh)
          simp (config := { singlePass := true }) [ronrw] at ih
          simp [listrwgen (ro-n-1)] at ih

          have domaux10 : (usen O cf (s+1-(ro - n - 1 + 1)) (Nat.pair x.l (ro - n - 1 + 1 + x.r))).isSome := by
            rw [←ronrw]
            exact auxdom8 n
          have domaux11 : (usen O cf (s+1-(ro - n - 1)) (Nat.pair x.l (ro - n - 1 + x.r))).isSome := by
            rw [←ronrw0]
            exact auxdom8 (n + 1)
          let base2 := (((usen O cf (s+1-(ro - n - 1 + 1)) (Nat.pair x.l (ro - n - 1 + 1 + x.r))).get domaux10).max
          ((usen O cf (s+1-(ro - n - 1 )) (Nat.pair x.l (ro - n - 1 + x.r))).get domaux11))
          let base1 := (usen O cf (s+1-(ro - n - 1 )) (Nat.pair x.l (ro - n - 1 + x.r))).get domaux11
          have base1_le_base2 : base1≤base2 := by
            exact Nat.le_max_right ((usen O cf (s+1-(ro - n - 1 + 1)) (Nat.pair x.l (ro - n - 1 + 1 + x.r))).get domaux10) base1
          -- #check clause_mono_1
          let f (a : ℕ) (l' : List ℕ) (h2:∃ l'':List ℕ, l'' ++ l' = (List.range (ro - n - 1)).reverse) (h3:a ∈ l')
            := (usen O cf (s+1-a) (Nat.pair x.l (a + x.r))).get (
              by
                exact domaux3 a (ro - (n + 1)) (List.forIn'_congr._proof_1 (congrArg (fun x ↦ (List.range x).reverse) ronrw0) a (by
                  simp; exact listrevlem2 h2 h3
                  )) (sub_le ro (n + 1))
            )

          let auxaxuaxuaxuaxa : ∀ (l' : List ℕ) (base : ℕ) (htt : ∃ l'', l'' ++ l' = (List.range (ro - n - 1)).reverse),
        (forIn' l' base fun a h b ↦ some (ForInStep.yield (b.max (f a l' htt h)))).isSome := by
            intro l' base htt
            unfold f
            rcases listrevlem htt with ⟨h1,h2,h3⟩
            simp [h2]
            have : h1≤ro := by exact le_of_le_sub (le_of_le_sub h3)
            exact forInDom base this
          -- let f (a : ℕ) (l : List ℕ) (h:a ∈ l) :ℕ := usen O cf (s+1-) (Nat.pair x.l (a + x.r))
          have mainclause := @clause_mono_2_opt base1 base2 (List.range (ro - n - 1)).reverse f (fun a head tail m l' hhht hht ↦ rfl) auxaxuaxuaxuaxa base1_le_base2
          -- have := Nat.le_trans mainclause.left ih
          have : s-(ro - n - 1 ) =  s+1-(ro - n - 1 + 1):= by grind
          simp (config:={singlePass:=true}) [this] at ih
          exact Nat.le_trans mainclause.left ih




  have :=(main3 (ro-j))
  have aux92: ro-(ro-j)=j:= by (expose_names; exact Nat.sub_sub_self hjro_1)
  simp [aux92] at this
  apply le_trans main2 this

def up_to_usen.induction
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
    motive (.rfind' cf) s x
    )
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

-- At a high level, this is an induction proof, using the inductive hypothesis on subterms obtained from unfolding evaln and usen.
theorem usen_principle {O₁ O₂} {s c x}
  (hh:(evaln O₁ s c x).isSome)
  (hO: ∀ i<(usen O₁ c s x).get (en2un hh), O₁ i = O₂ i) :
  evaln O₁ s c x = evaln O₂ s c x ∧ usen O₁ c s x = usen O₂ c s x
:= by
  have sG1 := evaln_sG1 hh
  have xles : x≤s-1 := evaln_xles' hh
  rw [sG1] at ⊢ hh
  have hO: ∀ i<(usen O₁ c (s-1+1) x).get (en2un hh), O₁ i = O₂ i := by
    simp [←sG1]
    exact fun i a ↦ hO i a

  expose_names
  clear hO_1 hh_1 sG1 xles

  induction c,s,x using up_to_usen.induction with
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
    · exact λ x h ↦ hO x (le_trans h (usen_mono_pair (en2un hh)).left)
    have ih_cg := hcg ?_ ?_; rotate_left
    · exact (evaln_pair_dom hh).right
    · exact λ x h ↦ hO x (le_trans h (usen_mono_pair (en2un hh)).right)

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
    if h:¬x≤s-1 then simp [h,Option.bind]
    else
    simp at h; simp [h]; clear h

    have ih_cg := hcg ?_ ?_; rotate_left
    · exact (evaln_comp_dom hh).left
    · exact λ x h ↦ hO x (le_trans h (usen_mono_comp (en2un hh)).left)

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
    · have aux := λ x h ↦ hO x (le_trans h (usen_mono_comp (en2un hh)).right)
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
    if h:¬x≤s-1 then simp [h,Option.bind]
    else
    simp at h; simp [h]; clear h

    cases hxr:x.r with
    | zero =>
      simp only [rec_zero]
      rw [hxr] at hh
      simp only [hxr] at hO

      have ih_cf := hcf x.l ?_ ?_; rotate_left
      · exact evaln_prec_dom' hh
      · exact λ x h ↦ hO x (le_trans h (usen_mono_prec' (en2un hh)))

      simp [ih_cf]
    | succ xrM1 =>
      -- rewriting/simplifying
      rw [hxr] at hh ih
      simp only [hxr] at hO;
      simp only []

      -- we want to show that the subexpression involving evaln and usen are equivalent, using the inductive hypothesis.
      have aux00 := evaln_prec_dom_aux hh
      have aux02 := λ x h ↦ hO x (le_trans h (usen_mono_prec_1 (en2un hh)))
      have : s-1-1+1=s-1 := by exact Eq.symm (evaln_sG1 aux00)
      simp (config:={singlePass:=true}) [←this] at aux00 aux02

      have ih_c := ih (s-1) ?_ (Nat.pair x.l xrM1) ?_ ?_ ?_; rotate_left
      · exact sub_le s 1
      · exact pair_lt_pair_right x.l (lt_add_one xrM1)
      · exact aux00
      · exact aux02

      simp [this] at ih_c aux00
      have aux11 := evaln_prec_dom hh

      have ih_cg := hcg
        (Nat.pair x.l (Nat.pair xrM1 ((evaln O₁ (s-1) (cf.prec cg) (Nat.pair x.l xrM1)).get (aux00)))) (aux11.right)
        λ x h ↦ hO x (le_trans h (usen_mono_prec (en2un hh)).right)

      rw [← ih_c.left]
      rw [← ih_c.right]
      simp only [isSome.bind aux00]
      simp only [isSome.bind $ en2un aux00]
      simp [ih_cg]

  | hrfind' cf s x hcf =>
    rcases nrfind'_obtain_prop hh with ⟨nrop1,nrop2,nrop3⟩
    let nro := nrfind'_obtain hh
    have rwnro : nrfind'_obtain hh = nro := rfl
    simp only [rwnro, Option.mem_def] at nrop1 nrop2
    have ihAll : ∀ j ≤ nro,
      evaln O₁ (s-1+1-j) cf  (Nat.pair x.l (j + x.r)) = evaln O₂ (s-1+1-j) cf (Nat.pair x.l (j + x.r))
      ∧
      usen O₁ cf (s-1+1-j)  (Nat.pair x.l (j + x.r)) = usen O₂ cf (s-1+1-j) (Nat.pair x.l (j + x.r))
    := by
      intro j hjro
      have sG1j : s-1+1-j-1+1 = s-1+1-j := by exact (evaln_sG1 (nrop2 j hjro)).symm
      rw [←sG1j]

      have aux1 : (evaln O₁ (s-1+1-j-1+1) cf (Nat.pair x.l (j + x.r))).isSome := by
        rw [sG1j]
        exact nrop2 j hjro

      apply hcf (Nat.pair x.l (j + x.r)) ((s-1+1-j)) ?_ ?_; rotate_left
      ·
        simp [sG1j]
        exact λ x h ↦ hO x (le_trans h (usen_mono_rfind' (en2un hh) (show j≤nrfind'_obtain hh from hjro)))
      · exact aux1

    have aux0 : (evaln O₂ (s-1+1) cf.rfind' x).isSome := by
      apply evaln_rfind_as_eval_rfind_reverse
      simp
      use nro
      constructor
      · rw [←(ihAll nro le_rfl).left]
        exact nrop1
      intro j hjro
      have hjro : j≤nro := by exact le_of_succ_le hjro
      rw [←(ihAll j hjro).left]
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
      · rw [←(ihAll nro le_rfl).left]
        exact nrop1
      constructor
      · intro j hjro
        rw [←(ihAll j hjro).left]
        exact nrop2 j hjro
      · intro j hjro
        rw [←(ihAll j (le_of_succ_le hjro)).left]
        exact nrop3 j hjro

    simp [main1]

    -- we rephrase the proof to be of the for loop form found in use, rather than the inductive form of usen
    suffices
    (do
  guard (x≤s-1);
  let guard ← evaln O₁ (s-1+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O₁ cf (s-1+1-i) (Nat.pair x.l (i+x.r)))
    max := Nat.max max usen_i
  max :Option ℕ)
  =
  (do
  guard (x≤s-1);
  let guard ← evaln O₂ (s-1+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O₂ cf (s-1+1-i) (Nat.pair x.l (i+x.r)))
    max := Nat.max max usen_i
  max :Option ℕ)
  from by
      have rw1 := @usen_rfind_prop2'' O₁ (s-1) x cf
      rw [←rw1] at this
      have rw2 := @usen_rfind_prop2'' O₂ (s-1) x cf
      rw [←rw2] at this
      exact this
    simp

    simp [evaln_xles hh]
    rw [←main1]
    simp [isSome.bind hh]

    have a2 := λ j hj ↦ (ihAll j hj).right
    have a0 : (evaln O₁ (s - 1 + 1) cf.rfind' x).get hh - x.r = nro := by exact rwnro
    rw [a0]
    clear rwnro nrop3 nrop1 aux0 hO a0 main1 hcf ihAll

    have a4 := a2 0 (Nat.zero_le nro)
    simp at a4

    generalize 0=b at ⊢
    revert nrop2
    revert a2
    induction nro generalizing b with
    | zero => simp [←a4]
    | succ nron ih =>
      intro a2 nrop2
      simp (config:={singlePass:=true}) [listrwgen]; simp

      have := a2 (nron+1) (le_rfl)
      simp at this; simp [←this]; clear this

      have := en2un $ nrop2 (nron+1) (Nat.le_refl (nron + 1))
      simp at this
      simp [isSome.bind this]
      exact @ih
        ((b.max ((usen O₁ cf (s - 1 - nron) (Nat.pair x.l (nron + 1 + x.r))).get this)))
        (λ j hj ↦ a2 j (le_add_right_of_le hj))
        (λ j hj ↦ nrop2 j (le_add_right_of_le hj))

lemma usen_sing'' : (usen O c s1 x).get h1 = (use O c x).get h2 := by
  rcases usen_complete.mp (Part.get_mem h2) with ⟨h3,h4⟩
  simp at h4
  have h5 : (usen O c h3 x).isSome := by exact Option.isSome_of_mem h4
  have : (use O c x).get h2 = (usen O c h3 x).get h5 := by exact Eq.symm (Option.get_of_eq_some h5 h4)
  rw [this]
  exact usen_sing'
lemma evaln_sound' (h:(evaln O s c x).isSome) : eval O c x = Part.some ((evaln O s c x).get h)
:= by
  have := evaln_sound (Option.get_mem h)
  exact Part.eq_some_iff.mpr this
lemma usen_sound' (h:(usen O c s x).isSome) : use O c x = Part.some ((usen O c s x).get h)
:= by
  have := usen_sound (Option.get_mem h)
  exact Part.eq_some_iff.mpr this

theorem use_principle {O₁ O₂} {c x}
(hh:(eval O₁ c x).Dom)
(hO: ∀ i<(use O₁ c x).get (e2u hh), O₁ i = O₂ i) :
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

theorem use_principle_evaln {O₁ O₂:ℕ→ℕ} {s c x} (hh:(evaln O₁ s c x).isSome) (hO: ∀ i<(usen O₁ c s x).get (en2un hh), O₁ i = O₂ i) : evaln O₁ s c x = evaln O₂ s c x :=
  (usen_principle hh hO).left
theorem use_principle_usen {O₁ O₂:ℕ→ℕ} {s c x} (hh:(evaln O₁ s c x).isSome) (hO: ∀ i<(usen O₁ c s x).get (en2un hh), O₁ i = O₂ i) : usen O₁ c s x = usen O₂ c s x :=
  (usen_principle hh hO).right
theorem use_principle_eval {O₁ O₂:ℕ→ℕ} {c x} (hh:(eval O₁ c x).Dom) (hO: ∀ i<(use O₁ c x).get (e2u hh), O₁ i = O₂ i) : eval O₁ c x = eval O₂ c x :=
  (use_principle hh hO).left
theorem use_principle_use {O₁ O₂:ℕ→ℕ} {c x} (hh:(eval O₁ c x).Dom) (hO: ∀ i<(use O₁ c x).get (e2u hh), O₁ i = O₂ i) : use O₁ c x = use O₂ c x :=
  (use_principle hh hO).right


/-
What does rfind' do?
rfind' cf (x,i) = the smallest (i+j) s.t. `[cf](x,i+j)=0`

So to calculate `rfind' cf x`, we will need to calculate
`[cf]` on all inputs from `x` to `(x.l, rfind' cf x)`

-/
