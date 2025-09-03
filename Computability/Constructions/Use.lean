import Computability.Constructions.CovRec

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset






open Nat.RecursiveIn.Code
namespace Nat.RecursiveIn.Code
protected theorem isSome.bind {o : Option α} (h : o.isSome) (f : α → Option β) : o.bind f = f (o.get h) := by
  have : o = some (o.get h) := by exact Option.eq_some_of_isSome h
  ext b
  constructor
  intro h2
  rw [this] at h2
  simp only [Option.bind_some] at h2
  exact h2

  intro h2
  rw [this]
  simp only [Option.bind_some]
  exact h2
theorem listrwgen (n): (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
  simp
  exact List.range_succ

theorem ne_of_mem_imp_not_mem {y:Part ℕ} (h:x∈y) (h2:x≠z) : z∉y := by
  have aux: y=Part.some x := by exact Part.eq_some_iff.mpr h
  rw [aux]
  aesop? says
    subst aux
    simp_all only [ne_eq, Part.mem_some_iff]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [not_true_eq_false]
theorem opt_ne_of_mem_imp_not_mem {y:Option ℕ} (h:x∈y) (h2:x≠z) : z∉y := by
  aesop
lemma rfind'_geq_xr (h:(eval O (rfind' cf) x).Dom) : (eval O cf.rfind' x).get h ≥ x.r := by simp [eval]
abbrev en2e : (evaln O s c x).isSome → (eval O c x).Dom := by
  intro h
  have : (evaln O s c x).get (h) ∈ evaln O s c x := by exact Option.get_mem h
  have := evaln_sound (Option.get_mem h)
  exact Part.dom_iff_mem.mpr (⟨(evaln O s c x).get (h),this⟩)
theorem evaln_eq_eval (h:(evaln O s c x).isSome) : (evaln O s c x).get h = (eval O c x).get (en2e h) := by
  have := evaln_sound (Option.get_mem h)
  exact Eq.symm (Part.get_eq_of_mem this (en2e h))
lemma nrfind'_geq_xr (h:(evaln O (s) (rfind' cf) x).isSome) : (evaln O (s) (rfind' cf) x).get h ≥ x.r := by
  rw [evaln_eq_eval]
  exact rfind'_geq_xr (en2e h)
def rfind'_obtain (h:(eval O (rfind' cf) x).Dom) : ℕ := ((eval O (rfind' cf) x).get h)-x.r
def nrfind'_obtain (h:(evaln O s (rfind' cf) x).isSome) : ℕ := ((evaln O s (rfind' cf) x).get h)-x.r
theorem nrop_eq_rop (h:(evaln O s (rfind' cf) x).isSome) : nrfind'_obtain h = rfind'_obtain (en2e h) := by
  unfold nrfind'_obtain
  unfold rfind'_obtain
  rw [evaln_eq_eval h]

-- TODO:
-- the below theorem should follow more or less straightforwardly from n_rfind'_obtain_prop.
theorem rfind'_obtain_prop
(h:(eval O (rfind' cf) x).Dom) :
0∈(eval O cf (Nat.pair x.l (rfind'_obtain h+x.r)))
∧ (∀ j ≤ rfind'_obtain h, (eval O cf (Nat.pair x.l (j+x.r))).Dom)
∧ (∀ j < rfind'_obtain h, ¬0∈(eval O cf (Nat.pair x.l (j+x.r))))
:= by
  let rf_result := (eval O cf.rfind' x).get h
  have aux0 : rf_result ∈ eval O cf.rfind' x := by exact Part.get_mem h

  have aux2 : rfind'_obtain h = rf_result - x.r:= by exact rfl
  -- have aux3 : rf_result = m := by exact?
  have aux3 : rf_result ∈ eval O cf.rfind' x := by exact Part.get_mem h
  simp [eval] at aux3
  rcases aux3 with ⟨a,⟨⟨lll,rrr⟩,ha⟩⟩
  have aux4: rf_result - x.r = a := by exact (Nat.sub_eq_iff_eq_add (rfind'_geq_xr h)).mpr (_root_.id (Eq.symm ha))

  constructor
  · subst aux4
    simp_all only [rf_result]
  rw [aux2]
  rw [aux4]
  constructor
  ·
    intro j
    intro hja

    cases lt_or_eq_of_le hja with
    | inl hja =>
      rcases rrr hja with ⟨witness,⟨hwitness,_⟩⟩
      have exform : ∃ a, a ∈ eval O cf (Nat.pair x.l (j + x.r)) := by exact Exists.intro witness hwitness


      exact Part.dom_iff_mem.mpr exform
    | inr hja =>
      rw [hja]

      have exform : ∃ a', a' ∈ eval O cf (Nat.pair x.l (a + x.r)) := by exact Exists.intro 0 lll
      exact Part.dom_iff_mem.mpr exform
  · intro j
    intro hja
    rcases rrr hja with ⟨witness,⟨hwitness_1,hwitness_2⟩⟩
    exact ne_of_mem_imp_not_mem hwitness_1 hwitness_2
theorem rfind'_obtain_prop_4 (h:(eval O (rfind' cf) x).Dom) : ∀ j ≤ rfind'_obtain h, (eval O (rfind' cf) (Nat.pair x.l (j+x.r))).Dom := by
  have rop := rfind'_obtain_prop h
  let ro := rfind'_obtain h
  have rwro : rfind'_obtain h = ro := rfl
  simp [rwro] at rop ⊢
  have rop1 := rop.left
  have rop2 := rop.right.left
  have rop3 := rop.right.right

  intro j
  intro hjro
  simp [eval]
  use ro-j
  constructor
  have : (ro - j + (j + x.r)) = ro + x.r := by grind
  simp [this]
  exact rop1
  intro m hm
  rw [← (Nat.add_assoc m j x.r)]
  have : m+j ≤ ro := by exact le_of_succ_le (add_lt_of_lt_sub hm)
  exact rop2 (m+j) this
lemma forall_mem_part {y:Part ℕ} (h1:y.Dom) (h2:∀ x ∈ y, x = c ) : c∈y := by
  contrapose h2
  simp
  use y.get h1
  constructor
  exact Part.get_mem h1
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  have : y.get h1 ∈ y := by exact Part.get_mem h1
  contradiction
lemma forall_mem_option {y:Option ℕ} (h1:y.isSome) (h2:∀ x ∈ y, x = c ) : c∈y := by
  contrapose h2
  simp
  use y.get h1
  constructor
  exact Option.eq_some_of_isSome h1
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  have : y.get h1 ∈ y := by exact Option.eq_some_of_isSome h1
  contradiction
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
∀ j ≤ rfind'_obtain h,
(rfind'_obtain h)+x.r ∈ (eval O (rfind' cf) (Nat.pair x.l (j+x.r)))  := by
  have rop := rfind'_obtain_prop h
  let ro := rfind'_obtain h
  have rwro : rfind'_obtain h = ro := rfl
  simp [rwro] at rop ⊢
  have rop1 := rop.left
  have rop2 := rop.right.left
  have rop3 := rop.right.right
  have rop4 := rfind'_obtain_prop_4 h
  simp [rwro] at rop4

  intro j hjro

  have := @rfind'_prop O cf (Nat.pair x.l (j + x.r)) (ro-j) (rop4 j hjro)
  have hjro2 :  ro - j + (j + x.r) = ro+x.r := by grind
  simp [hjro2] at this
  apply (this).mpr ?_
  constructor
  exact rop1
  constructor
  intro j2 hj2
  rw [←add_assoc]
  exact rop2 (j2+j) (add_le_of_le_sub hjro hj2)
  intro j2 hj2
  rw [←add_assoc]
  exact rop3 (j2+j) (add_lt_of_lt_sub hj2)



theorem evaln_rfind_as_eval_rfind'
(h:(evaln O s (rfind' c) x).isSome)
:
((evaln O s (rfind' c) x).get h)
∈
((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) x)
:= by

  have wrap : unpaired
    (fun a m ↦ Part.map (fun x ↦ x + m) (Nat.rfind fun n ↦ (fun x ↦ decide (x = 0)) <$> eval O c (Nat.pair a (n + m))))
    x = (eval O (rfind' c) x) := by simp only [eval]
  rw [wrap]
  exact evaln_sound (Option.get_mem h)
theorem evaln_rfind_base (h:(evaln O (s+1) (rfind' cf) x).isSome) : (evaln O (s+1) (cf) x).isSome := by
  contrapose h
  simp at h
  simp [evaln]
  intro h1
  intro h2
  intro h3
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
  simp_all
  intro h4
  intro h5
  intro h6
  grind only [Option.not_isSome, Option.get_some, Option.isSome_some]



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
        contrapose h4
        simp at h4
        simp
        rw [h4] at rwasd
        rw [show 0=(Option.some 0).get (Option.isSome_some) from rfl] at rwasd

        exact Option.get_inj.mp rwasd
      simp [this]
      have halt2 := evaln_rfind_indt h hh this
      have := nrfind'_geq_xr halt2
      simp at this
      exact ne_of_lt this
    | succ roM1 ih =>
      have := @ih (s-1) (Nat.pair x.l (x.r+1)) ?_ ?_
      -- simp_all
      simp
      simp at this
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
        simp
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
            rw [add_assoc] at h4
            rw (config:={occs:=.pos [2]})[add_comm] at h4
            exact h4
      · cases s with
      | zero => simp_all [evaln]
      | succ n =>
        simp at this
        rw [add_assoc]
        rw (config:={occs:=.pos [3]}) [add_comm]
        exact this
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
          | zero =>
            simp [evaln] at halt2
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
      · simp
        rw [show h1 - 1 + (1 + x.r) = h1+x.r from by grind]
        exact ih_aux_1
      ·
        intro j hjro
        simp
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


lemma evaln_rfind_as_eval_rfind''_aux
(h:(evaln O (s+1) (rfind' c) x).isSome)
:
((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> evaln O ((s+1)-n) c (Nat.pair a (n + m))).map (· + m)) x).Dom := by
  have := evaln_rfind_as_eval_rfind h
  apply Part.dom_iff_mem.mpr
  exact Exists.intro ((evaln O (s + 1) c.rfind' x).get h) this
theorem evaln_rfind_as_eval_rfind''
(h:(evaln O (s+1) (rfind' c) x).isSome)
:
((evaln O (s+1) (rfind' c) x)) = Option.some
(((Nat.unpaired fun a m => (Nat.rfind fun n => (fun x => x = 0) <$> evaln O ((s+1)-n) c (Nat.pair a (n + m))).map (· + m)) x).get (evaln_rfind_as_eval_rfind''_aux h)) := by
  have h1:= evaln_rfind_as_eval_rfind h
  have h2: (evaln O (s + 1) c.rfind' x).get h = (unpaired
    (fun a m ↦
      Part.map (fun x ↦ x + m)
        (Nat.rfind fun n ↦ (fun x ↦ decide (x = 0)) <$> ↑(evaln O (s + 1 - n) c (Nat.pair a (n + m)))))
    x).get (evaln_rfind_as_eval_rfind''_aux h) := by exact Eq.symm (Part.get_eq_of_mem h1 (evaln_rfind_as_eval_rfind''_aux h))
  rw [←h2]
  exact Option.eq_some_of_isSome h

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
    have := @ih (s-1) (Nat.pair x.l (x.r+1)) ?_ ?_
    simp [evaln]
    -- have := @ih (x) ?_ ?_

    rotate_left
    · simp
      rw [←sss]
      rw (config:={occs:=.pos [2]}) [add_comm]
      rwa [←add_assoc]
    · simp
      intro j hj
      have := @h3 (j+1) (Nat.add_lt_add_right hj 1)
      simp at this
      rw [←sss]
      rw (config:={occs:=.pos [2]}) [add_comm]
      rwa [←add_assoc]
    have xles : x≤s := by

      contrapose h2
      simp at h2
      -- have : s < (Nat.pair x.l (1 + x.r)) := by exact?
      have contra : s-n < (Nat.pair x.l (n + 1 + x.r)) := calc
        s-n ≤ s                  := sub_le s n
        _ < x                    := h2
        _ = Nat.pair x.l x.r     := Eq.symm pair_lr
        _ < Nat.pair x.l (n+1+x.r) := by
          apply pair_lt_pair_right x.l
          grind
      intro he
      have := evaln_bound he
      have := lt_trans contra this
      simp at this
    simp [xles]
    -- simp [xles] at this
    -- exact this
    -- have xles2 : (Nat.pair x.l (x.r + 1) ≤ s) := by sorry
    -- simp [xles2] at this

    have := @h3 0 (zero_lt_succ n)
    simp at this
    simp [isSome.bind this]
    if hhhh:(evaln O (s + 1) c x).get this = 0 then
      simp [hhhh]
    else
      simp [hhhh]
      rw [sss]
      (expose_names; exact this_2)

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

  let rf_result := (evaln O (s+1) cf.rfind' x).get h
  have aux0 : rf_result ∈ evaln O (s+1) cf.rfind' x := by exact Option.get_mem h

  have aux2 : nrfind'_obtain (h) = rf_result - x.r:= by
    simp [nrfind'_obtain,rf_result]
  have aux3 : rf_result = (evaln O (s+1) cf.rfind' x).get h := by exact rfl

  have := evaln_rfind_as_eval_rfind h
  rw [←aux3] at this
  clear aux3
  have aux3 := this
  clear this
  simp at aux3

  rcases aux3 with ⟨a,⟨⟨lll,rrr⟩,ha⟩⟩
  have aux4: rf_result - x.r = a := by exact Eq.symm (Nat.eq_sub_of_add_eq ha)

  constructor
  ·
    simp [aux2]
    simp_all only [rf_result]
  rw [aux2]
  rw [aux4]
  constructor
  ·
    intro j
    intro hja

    cases lt_or_eq_of_le hja with
    | inl hja =>
      rcases rrr hja with ⟨witness,⟨hwitness,_⟩⟩
      exact Option.isSome_of_mem hwitness
    | inr hja =>
      rw [hja]
      exact Option.isSome_of_mem lll
  · intro j
    intro hja
    rcases rrr hja with ⟨witness,⟨hwitness_1,hwitness_2⟩⟩

    exact opt_ne_of_mem_imp_not_mem hwitness_1 hwitness_2
theorem n_rfind'_obtain_prop'
(h:(evaln O (s+1) (rfind' cf) x).isSome) :
0∈(evaln O (s+1-(rfind'_obtain (en2e h))) cf (Nat.pair x.l (rfind'_obtain (en2e h)+x.r)))
∧ (∀ j ≤ rfind'_obtain (en2e h), (evaln O (s+1-j) cf  (Nat.pair x.l (j+x.r))).isSome)
∧ (∀ j < rfind'_obtain (en2e h), ¬0∈(evaln O (s+1-j) cf (Nat.pair x.l (j+x.r))))
:= by
  rw [←nrop_eq_rop h]
  exact nrfind'_obtain_prop h

theorem nrfind'_obtain_prop_4 (h:(evaln O (s+1) (rfind' cf) x).isSome) :
∀ j ≤ nrfind'_obtain h, (evaln O (s+1-j) (rfind' cf) (Nat.pair x.l (j+x.r))).isSome := by
  have rop := nrfind'_obtain_prop h
  let ro := nrfind'_obtain h
  have rwro : nrfind'_obtain h = ro := rfl
  simp [rwro] at rop ⊢
  have rop1 := rop.left
  have rop2 := rop.right.left
  have rop3 := rop.right.right

  intro j
  intro hjro
  apply evaln_rfind_as_eval_rfind_reverse' ?_
  simp
  use ro-j
  constructor
  have : (ro - j + (j + x.r)) = ro + x.r := by grind
  simp [this]
  have : s + 1 - j - (ro - j) = s+1-ro := by exact Nat.sub_sub_sub_cancel_right hjro
  rw [this]
  exact rop1
  intro m hm
  rw [← (Nat.add_assoc m j x.r)]
  have : m+j ≤ ro := by exact le_of_succ_le (add_lt_of_lt_sub hm)
  have := rop2 (m+j) this
  have : (s + 1 - j - m) = (s + 1 - (m + j)) := by exact Eq.symm (Simproc.sub_add_eq_comm (s + 1) m j)
  rwa [this]
lemma mem_shambles
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
  constructor
  intro h1
  have : y=nrfind'_obtain (h) := by
    unfold nrfind'_obtain
    simp_all
  rw [this]
  have : s≠0 := by
    intro ss
    simp [ss, evaln] at h
  have : s=s-1+1 := by
    exact Eq.symm (succ_pred_eq_of_ne_zero this)

  simp (config:={singlePass:=true}) [this] at h ⊢
  exact nrfind'_obtain_prop h

  have : s≠0 := by
    intro ss
    simp [ss, evaln] at h
  have : s=s-1+1 := by
    exact Eq.symm (succ_pred_eq_of_ne_zero this)
  simp (config:={singlePass:=true}) only [this] at h ⊢
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
  have rop1 := rop.left
  have rop2 := rop.right.left
  have rop3 := rop.right.right
  have rop4 := nrfind'_obtain_prop_4 h
  simp [rwro] at rop4

  intro j hjro

  have := @nrfind'_prop O (s+1-j) cf (Nat.pair x.l (j + x.r)) (ro-j) (rop4 j hjro)
  have hjro2 :  ro - j + (j + x.r) = ro+x.r := by grind
  simp [hjro2] at this
  apply (this).mpr ?_
  constructor
  -- have : (s + 1 - j - (ro - j)) = s + 1 - ro := by exact Nat.sub_sub_sub_cancel_right hjro
  rw [show (s + 1 - j - (ro - j)) = s + 1 - ro from Nat.sub_sub_sub_cancel_right hjro]
  exact rop1
  constructor
  intro j2 hj2
  rw [←add_assoc]
  have rop2':=rop2 (j2+j) (add_le_of_le_sub hjro hj2)
  rwa [show s + 1 - j - j2=s + 1 - (j2 + j) from Eq.symm (Simproc.sub_add_eq_comm (s + 1) j2 j)]
  intro j2 hj2
  rw [←add_assoc]
  have rop3' := rop3 (j2+j) (add_lt_of_lt_sub hj2)
  rwa [show s + 1 - j - j2=s + 1 - (j2 + j) from Eq.symm (Simproc.sub_add_eq_comm (s + 1) j2 j)]


-- /--
-- we define the use `max(all naturals queried to the oracle)+1`
-- use=0 when no queries are made.
-- use=none when the computation diverges.
-- -/
open Classical in
noncomputable def use (O:ℕ→ℕ) (c:Code) (x:ℕ) : Part ℕ :=
match c with
| zero        => 0
| succ        => 0
| left        => 0
| right       => 0
| oracle      => x+1
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
| _,0              => fun _=> Option.none
| zero      , s+1  => fun x=> do guard (x≤s); return 0
| succ      , s+1  => fun x=> do guard (x≤s); return 0
| left      , s+1  => fun x=> do guard (x≤s); return 0
| right     , s+1  => fun x=> do guard (x≤s); return 0
| oracle    , s+1  => fun x=> do guard (x≤s); return x+1
| pair cf cg, s+1  => fun x=>
  do
    guard (x≤s);
    let usen_cf ← usen O cf (s+1) x
    let usen_cg ← usen O cg (s+1) x
    return Nat.max usen_cf usen_cg
| comp cf cg, s+1  => fun x=>
  do
    guard (x≤s);
    let usen_cg ← usen O cg (s+1) x
    let evaln_cg ← evaln O (s+1) cg x
    let usen_cf ← usen O cf (s+1) evaln_cg
    return Nat.max usen_cf usen_cg
| prec cf cg, s+1 => fun x=> do
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
| rfind' cf, s+1 => fun x =>
  do
    guard (x≤s);
    let usen_base ← usen O cf (s+1) x
    let evaln_base ← evaln O (s+1) cf x
    if evaln_base=0 then usen_base else
    let usen_indt ← usen O (rfind' cf) s (Nat.pair x.l (x.r+1))
    Nat.max usen_base usen_indt

-- theorem test (h:∀ (a : ℕ), ¬x = some a) : x=Option.none := by exact Option.eq_none_iff_forall_ne_some.mpr h

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
      | succ k =>
        exact hpair k cf cg hcf hcg
    | comp cf cg hcf hcg =>
      cases k with
      | zero   => exact h0 (.comp cf cg)
      | succ k =>
        exact hcomp k cf cg hcf hcg
    | prec cf cg hcf hcg =>
      cases k with
      | zero   => exact h0 (.prec cf cg)
      | succ k =>
        apply hprec k cf cg
        exact hcf
        exact hcg
        exact ih k (Nat.lt_succ_self _) (.prec cf cg)
    | rfind' cf hcf =>
      cases k with
      | zero   => exact h0 (.rfind' cf)
      | succ k =>
        apply hrfind k cf
        intro x' hle
        grind only

-- TODO: replace ind with an explicit induction scheme
private def ind : ℕ → Code → ℕ
| 0, _ => 0
| s+1, zero => 0
| s+1, succ => 0
| s+1, left => 0
| s+1, right => 0
| s+1, oracle => 0
| s+1, pair cf cg => ind (s+1) cf + ind (s+1) cg
| s+1, comp cf cg => ind (s+1) cf + ind (s+1) cg
-- | 0, prec cf cg => ind 0 cf + ind 0 cg
| s+1, prec cf cg =>
  -- ∑ i ∈ Finset.range (s+1),
  -- (ind i cf + ind i cg)
  ind (s+1) cf
  + ind (s+1) cg
  + ind s (prec cf cg)
  -- +
  -- ind s cf +
  -- ind s cg
-- | 0, rfind' cf => 0
| s+1, rfind' cf =>
  ind (s+1) cf
  + ind s (rfind' cf)
#check ind.induct
#check Nat.strong_induction_on

private theorem bound_lemma (h:Nat.pair a (b+1)≤s+1) : (Nat.pair a b≤s):= by
  exact le_of_lt_succ (Nat.lt_of_lt_of_le (pair_lt_pair_right a (lt_add_one b)) h)
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
    | inl h =>
      simp [h]

      constructor
      ·
        intro hh
        intro a ha
        have := (@hcf x).not
        simp only [Option.ne_none_iff_exists'] at this
        obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
        exact hcg.mp (Option.eq_none_iff_forall_ne_some.mpr (hh a2 ha2))

      · intro hh
        intro a ha
        apply Option.eq_none_iff_forall_ne_some.mp
        have := (@hcf x).not
        simp only [Option.ne_none_iff_exists'] at this
        obtain ⟨a2,ha2⟩ := this.mp ⟨a,ha⟩
        exact hcg.mpr (hh a2 ha2)
    | inr h => simp [h]
  | case8 s cf cg hcf hcg =>
    simp [usen,evaln]
    cases Classical.em (x≤s) with
    | inl h =>
      simp [h]
      constructor
      · intro hh
        intro a ha
        have := (@hcg x).not
        simp only [Option.ne_none_iff_exists'] at this
        obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
        have := hh a2 ha2 a ha
        have := Option.eq_none_iff_forall_ne_some.mpr this
        exact hcf.mp (Option.eq_none_iff_forall_ne_some.mpr (hh a2 ha2 a ha))
      · intro hh
        intro a ha
        intro a3
        intro ha3
        apply Option.eq_none_iff_forall_ne_some.mp
        have := (@hcf x).not
        simp only [Option.ne_none_iff_exists'] at this
        exact hcf.mpr (hh a3 ha3)
    | inr h => simp [h]
  | case9 s cf cg hcf hcg ih =>
    simp [usen,evaln]
    cases Classical.em (x≤s) with
    | inl h =>
      simp [h]
      cases hxr:x.r with
      | zero =>
        simp
        exact hcf
      | succ xrM1 =>
      simp only [Option.bind_eq_none_iff, reduceCtorEq, imp_false]

      constructor
      ·
        intro hh
        intro a ha
        have := (@ih (Nat.pair x.l xrM1)).not
        simp only [Option.ne_none_iff_exists'] at this
        obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
        have := hh a2 ha2 a ha
        have := Option.eq_none_iff_forall_ne_some.mpr this
        exact hcg.mp this
      · intro hh
        intro a ha
        intro a3
        intro ha3

        apply Option.eq_none_iff_forall_ne_some.mp
        have := hh a3 ha3
        exact hcg.mpr this
    | inr h => simp [h]
  | case10 s cf hcf ih =>
    simp [usen,evaln]
    cases Classical.em (x≤s) with
    | inl h =>
      simp [h]
      constructor
      ·
        intro hh
        intro a ha


        have := (@hcf x).not

        simp only [Option.ne_none_iff_exists'] at this
        obtain ⟨a2,ha2⟩ := this.mpr ⟨a,ha⟩
        -- #check hh a2 (sorry) a2 ha2 a ha
        have := hh a2 ha2 a ha
        -- have := hh a2 (sorry) a2 ha2 a ha

        cases a with
        | zero =>
          simp at this
        | succ n =>
          simp at this ⊢
          have := Option.eq_none_iff_forall_ne_some.mpr this
          exact ih.mp this


      · intro hh
        intro a ha
        intro a3
        intro ha3

        have := hh a3 ha3

        cases a3 with
        | zero =>
          simp at this
        | succ n =>
          simp at this ⊢
          apply Option.eq_none_iff_forall_ne_some.mp
          exact ih.mpr this
    | inr h => simp [h]

theorem usen_dom_iff_evaln_dom : (∃a,a∈(usen O c s x)) ↔ (∃b,b∈(evaln O s c x)) := by
  have := (@usen_none_iff_evaln_none O c s x).not
  simp [Option.eq_none_iff_forall_ne_some] at this
  exact this
lemma isSome_iff_not_none : (¬o=Option.none)↔(o.isSome) := by
  apply Iff.intro
  · intro a
    simp [Option.eq_none_iff_forall_ne_some] at a
    rcases a with ⟨h1,h2⟩
    exact Option.isSome_of_mem h2
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [Option.isSome_none, Bool.false_eq_true]
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
    refine ⟨h1,guard_imp hl' h2,
    h3,hg n h3 h4,
    h5,evaln_mono hl h6,
    h7,hf h5 h7 h8,
    h9⟩


  · -- prec cf cg
    revert h
    simp only [bind]
    induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
    ·
      intros g h
      exact ⟨Nat.le_trans g hl', hf n.l x h⟩
    ·
      intros g x1 hx1 x2 hx2 x3 hx3 hmax
      refine ⟨Nat.le_trans g hl',
      x1,usen_mono hl' hx1,
      x2,by rw [evaln_mono hl' hx2],
      x3,
      by (expose_names; exact hg (Nat.pair n.l (Nat.pair n_1 x2)) x3 hx3), hmax
      ⟩

  · -- rfind' cf
    simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
      simp only [bind, Option.bind_eq_some_iff] at h ⊢

    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩

    refine ⟨h1,guard_imp hl' h2,
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
      refine ⟨h8,usen_mono hl' h9, h10⟩
theorem usen_mono_contra : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → usen O c k₂ n = Option.none → usen O c k₁ n = Option.none := by
  intro k₁ k₂ c n k1k2 opt
  contrapose opt
  have := usen_mono k1k2 (Option.get_mem (Option.isSome_iff_ne_none.mpr opt))
  refine Option.ne_none_iff_exists'.mpr ?_
  exact Exists.intro ((usen O c k₁ n).get (Option.isSome_iff_ne_none.mpr opt)) this
theorem usen_mono_dom : ∀ {k₁ k₂ c n}, k₁ ≤ k₂ → (usen O c k₁ n).isSome → (usen O c k₂ n).isSome := by
  intro k1 k2 c n k1k2 h1
  exact Option.isSome_of_mem (usen_mono k1k2 (Option.get_mem h1))
-- theorem Part.dom_imp_ex_some {x:Part ℕ} (h:x.Dom) : ∃ y, x=Part.some y := by
--   have h0 := Part.dom_iff_mem.mp h
--   rcases h0 with ⟨y,hy⟩
--   use y
--   exact Part.eq_some_iff.mpr hy
theorem Part.dom_imp_some {x:Part ℕ} (h:x.Dom) : x=Part.some (x.get h) := by
  exact Part.get_eq_iff_eq_some.mp rfl

lemma part_add {x y : ℕ}: Part.some x + Part.some y = Part.some (x+y) := by
  exact Part.some_add_some x y
theorem use_dom_iff_eval_dom : (use O c x).Dom ↔ (eval O c x).Dom := by
  induction c generalizing x with
  | zero => exact Eq.to_iff rfl
  | succ => exact Eq.to_iff rfl
  | left => exact Eq.to_iff rfl
  | right => exact Eq.to_iff rfl
  | oracle =>
    simp [use,eval]
    suffices Part.some (x+1) = @HAdd.hAdd (Part ℕ) (Part ℕ) (Part ℕ) instHAdd (Part.some x) 1 from by
      rw [←this]
      exact trivial
    have := Part.some_add_some x 1
    rw [←this]
    exact rfl
  | pair cf cg hcf hcg =>
    simp [use,eval]
    simp [Seq.seq]
    simp_all only []
  | comp cf cg hcf hcg =>
    simp [use,eval]
    simp [Seq.seq]
    simp_all only [and_exists_self]
  | prec cf cg hcf hcg =>
    simp [use,eval]
    simp [Seq.seq]
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
    have rop1 := rop.left
    have rop2 := rop.right.left
    have rop3 := rop.right.right
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
        simp_all only [le_refl, ro]
        split
        next x_1 b heq => simp_all only [le_refl, Part.some_dom]
        next x_1 b heq => simp_all only [le_refl, Part.some_dom]
    | succ n ih =>
      simp (config:={singlePass:=true}) [listrwgen]
      simp
      intro rop2
      have := rop2 (n+1) (le_rfl)
      have := hcf.mpr this
      simp [Part.Dom.bind this]
      use this
      have ih1 := ih (a.max ((use O cf (Nat.pair x.l (n + 1 + x.r))).get this)) ?_
      rotate_left
      ·
        intro j hj
        have := rop2 (j) (le_add_right_of_le hj)
        exact this
      exact ih1

abbrev e2u : (eval O c x).Dom → (use O c x).Dom := use_dom_iff_eval_dom.mpr
abbrev u2e : (use O c x).Dom → (eval O c x).Dom := use_dom_iff_eval_dom.mp
abbrev en2un : (evaln O s c x).isSome → (usen O c s x).isSome := usen_dom_iff_evaln_dom'.mpr
abbrev un2en : (usen O c s x).isSome → (evaln O s c x).isSome := usen_dom_iff_evaln_dom'.mp

lemma eval_rfind_prop5 :
-- x∈eval O (rfind' cf) (Nat.pair a b)→b≤x := by
x∈eval O (rfind' cf) y→y.r≤x := by
  simp [eval]
  grind
lemma evaln_rfind_prop5 :
x∈evaln O s (rfind' cf) y→y.r≤x := by
  intro h
  exact eval_rfind_prop5 (evaln_sound h)

lemma evaln_sing (h1:a∈(evaln O s1 c x)) (h2:b∈(evaln O s2 c x)): a=b := by
  cases Classical.em (s1≤s2) with
  | inl h =>
    have := evaln_mono h h1
    simp_all only [Option.mem_def, Option.some.injEq]
  | inr h =>
    have := evaln_mono (Nat.le_of_not_ge h) h2
    simp_all only [Option.mem_def, Option.some.injEq]
lemma usen_sing (h1:a∈(usen O c s1 x)) (h2:b∈(usen O c s2 x)): a=b := by
  cases Classical.em (s1≤s2) with
  | inl h =>
    have := usen_mono h h1
    simp_all only [Option.mem_def, Option.some.injEq]
  | inr h =>
    have := usen_mono (Nat.le_of_not_ge h) h2
    simp_all only [Option.mem_def, Option.some.injEq]
lemma usen_sing' : (usen O c s1 x).get h1 = (usen O c s2 x).get h2 := usen_sing (Option.get_mem h1) (Option.get_mem h2)
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
    | inl hh =>
      simp [hh,h]
    | inr hh =>
      simp [hh, Option.bind]
      contrapose hh
      simp
      exact le_of_lt_succ (evaln_bound h.left)


    intro h
    simp [evaln]
    cases em (x≤k) with
    | inl hh =>
      cases h with
      | inl h =>
        simp [hh]
        cases em (evaln O (k + 1) cf x=Option.none) with
        | inl hhh => simp [hhh]
        | inr hhh =>
          have : ∃z,z∈ evaln O (k + 1) cf x := by exact Option.ne_none_iff_exists'.mp hhh
          rcases this with ⟨h13,h14⟩
          simp_all
          intro cont
          have := evaln_rfind_prop5 cont
          simp at this
      | inr h => simp [h]
    | inr hh =>
      simp [hh, Option.bind]

  | succ yM1 ih =>
  have rwadd : yM1 + 1 + x.r = yM1 + (x.r + 1) := by
    rw [add_assoc]
    rw (config:={occs:=.pos [2]}) [add_comm]

  constructor

  intro this
  -- contrapose this
  -- simp at this ⊢
  -- simp [evaln]

  -- sorry

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
      apply Or.inr
      apply Or.inl
      use 0
      simpa
    | inr hh =>
    have : ∃z,z∈ evaln O (kM1+1 + 1) cf x := by exact Option.ne_none_iff_exists'.mp hh
    rcases this with ⟨h13,h14⟩
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
        exact le_add_left 1 yM1
        simp
        rw (config:={occs:=.pos [2]}) [add_comm]
        assumption
      | succ h1M1 =>
        simp at h3
        use h1M1+1+1
        constructor
        simp
        exact h2
        simp
        have : h1M1 + 1 + 1 + x.r =(h1M1 + 1 + (x.r + 1)) := by
          grind
        rw [this]
        assumption
    | inr h =>
      apply Or.inr
      apply Or.inr
      rcases h with ⟨h1,h2,h3⟩
      cases h1 with
      | zero =>
        simp_all
        use 1
        constructor
        exact Nat.lt_add_of_pos_left h2
        simp
        rw (config:={occs:=.pos [2]}) [add_comm]
        assumption
      | succ h1M1 =>
        simp at h3
        use h1M1+1+1
        constructor
        simp
        exact h2
        simp
        have : h1M1 + 1 + 1 + x.r =(h1M1 + 1 + (x.r + 1)) := by
          grind
        rw [this]
        assumption

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
  | inr hh =>
    simp [hh, Option.bind]
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
      rw [←h3]
      rw [add_assoc]
      rw (config:={occs:=.pos [3]}) [add_comm]
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
      rw [←h3]
      rw [add_assoc]
      rw (config:={occs:=.pos [3]}) [add_comm]
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
      -- exact this
      -- assumption
      -- apply Iff.not at this
      -- simp
      -- simp [Option.ne_none_iff_exists'] at this
      -- assumption
-- theorem evaln_rfind_prop_not :

-- (evaln O (k + 1) cf.rfind' x=Option.none) ↔
--   (¬0 ∈ evaln O (k + 1 - y) cf (Nat.pair x.l (y + x.r))) ∨
--     ((∃ j ≤ y, evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r))=Option.none) ) ∨
--     (¬ ∀ j < y, 0 ∉ evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r)))
-- := by
--   suffices ¬ y + x.r ∈ evaln O (k + 1) cf.rfind' x ↔
--   (¬0 ∈ evaln O (k + 1 - y) cf (Nat.pair x.l (y + x.r))) ∨
--     ((∃ j ≤ y, evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r))=Option.none) ) ∨
--     (¬ ∀ j < y, 0 ∉ evaln O (k + 1 - j) cf (Nat.pair x.l (j + x.r))) from by



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
theorem Option.isSome_iff_mem {o:Option β}: o.isSome ↔ (∃z,z∈o) := by
  have h1 := @Option.isSome_iff_exists β o
  simp [h1]
theorem usen_rfind_prop' (hu:(usen O (rfind' cf) (k + 1) n).isSome):
∀j≤rfind'_obtain (usen_rfind_prop_aux' hu),
  (usen O cf (k + 1 - j) (Nat.pair n.l (n.r+j))).isSome
  -- and also the maximum of these is equal to the usen.
:= by
  intro j hjro
  rw (config:={occs:=.pos [2]}) [add_comm]
  exact en2un ((n_rfind'_obtain_prop (un2en hu)).right.left j hjro)
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
  have usen_base_dom : (usen O cf (k-1+1) x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind usen_base_dom] at h
  simp [usen_base_dom]
  have evaln_base_dom : (evaln O (k -1+1) cf x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind evaln_base_dom] at h ⊢
  simp [evaln_base_dom]
  -- exact h
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
  -- simp [usen_base_dom]
  simp [isSome.bind evaln_base_dom] at h ⊢
  exact h
  -- simp [evaln_base_dom]
  -- contrapose h;
  -- simp at h;
  -- simp [usen]
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
  have h1 := n_rfind'_obtain_prop evaln_ver_dom
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
  simp [usen] at h
  have xlek : x≤k := by
    contrapose h;
    simp [h, Option.bind]
  simp [xlek] at h
  have usen_base_dom : (usen O cf (k+1) x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind usen_base_dom] at h
  -- simp [usen_base_dom]
  have evaln_base_dom : (evaln O (k+1) cf x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind evaln_base_dom] at h ⊢
  simp [evaln_base_dom]
  have evaln_ver_dom:(evaln O (k + 1) cf.rfind' x).isSome := by
    simp [evaln]
    simp [xlek]
    simp [isSome.bind evaln_base_dom] at ⊢

    contrapose h; simp at h;
    simp [evaln] at h
    simp [xlek] at h

    simp [h]
  simp [isSome.bind evaln_base_dom] at h ⊢
  simp [evaln_base_dom]

  have evalnbasedom : (evaln O (k + 1) cf x).isSome := by
    contrapose h; simp at h; simp [h]
    simp_all only [Option.isSome_none, Bool.false_eq_true]
  exact h


-- mpr
  intro h
  rcases h with ⟨h1,h2⟩
  simp [usen]
  -- #check
  have xlek : x≤k := le_of_lt_succ (evaln_bound (Option.get_mem h1))
  simp [xlek]
  simp [isSome.bind (en2un h1)]
  simp [isSome.bind (h1)]
  exact h2

lemma unrpeq1 : (y∈(do
  guard (x≤k);
  let guard ← evaln O (k+1) (rfind' cf) x;
  let ro := guard - x.r
  let mut max := 0
  for i in List.reverse (List.range (ro+1)) do
    let usen_i ← (usen O cf (k+1-i) (Nat.pair x.l (i+x.r)))
    max := Nat.max max usen_i
  max :Option ℕ)) ↔ (
  -- have h1:(usen O cf (k + 1) x).isSome
  -- x≤k
  -- ∧
  ∃
  -- (h1:(usen O cf (k + 1) x).isSome)
  -- (h2:(evaln O (k + 1) cf x).isSome)
  (evaln_ver_dom : (evaln O (k + 1) cf.rfind' x).isSome),
  ((forIn (List.range ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r + 1)).reverse 0 fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + x.r))).bind fun usen_i ↦ some (ForInStep.yield (r.max usen_i))) =
  some y)
) := by
  simp
  constructor
  intro h
  -- contrapose h
  -- simp at h
  have xlek : x≤k := by
    contrapose h;
    simp [h, Option.bind]
  simp [xlek] at h ⊢
  have evaln_ver_dom : (evaln O (k+1) (rfind' cf) x).isSome := by contrapose h; simp at h; simp [h]
  simp [isSome.bind evaln_ver_dom] at h
  use evaln_ver_dom
  intro h
  rcases h with ⟨h1,h2,h3⟩
  simp [h1]
  simp [isSome.bind h2]
  exact h3
lemma lemlemlem2
(a:ℕ)
(h1 : (evaln O (k + 1) cf x).isSome)
(u0:(usen O cf (k + 1) x).isSome)
(u1:(usen O cf (k + 1) (Nat.pair x.l (x.r + 1))).isSome)
-- (urom:(usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome)
(nrop2:(∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) (Nat.pair x.l (j + x.r))).isSome))
-- (urom:(usen O cf (k +1 - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome)
-- (urom2:(usen O cf (k +1 - roM1) (Nat.pair x.l (roM1 + x.r))).isSome)
-- (h6:h5 ∈ use O cf (Nat.pair n.l (nn + 1 + n.r)))
-- (rop3:∀ j ≤ nn + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
-- (h57dom:(use O cf n).Dom)
-- (h57def:h57=(use O cf n).get h57dom)
-- (aux123 : (use O cf n).Dom)
-- (i2 : usen O cf (i1 + 1) n = some ((use O cf n).get aux123))
-- (hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, usen O cf (k + 1) n = some x)
-- (hkk : (forIn (List.range (nn + 1)).reverse (a.max h57) fun i r ↦
--     (usen O cf (kk + 1 - i) (Nat.pair n.l (i + (1 + n.r)))).bind fun a ↦ some (ForInStep.yield (r.max a))) =
--   some x)
(hkk:(forIn (List.range (roM1 + 1)).reverse (a.max ((usen O cf (k + 1) x).get (en2un h1))) fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + (x.r + 1)))).bind fun a ↦ some (ForInStep.yield (r.max a)))=some y)
:
(forIn (List.range (roM1 + 1)).reverse (a.max ((usen O cf (k + 1) x).get (en2un h1))) fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + (x.r + 1)))).bind fun a ↦ some (ForInStep.yield (r.max a)))
    =
(forIn (List.range (roM1 + 1)).reverse (a.max ((usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).get asddom))
    fun i r ↦
    (usen O cf (k + 1 - i) (Nat.pair x.l (i + x.r))).bind fun usen_i ↦ some (ForInStep.yield (r.max usen_i)))
 := by
  -- revert h6
  -- induction roM1 generalizing h5 n a with
  induction roM1 generalizing a with
  | zero =>
    simp
    simp [isSome.bind u0]
    simp [isSome.bind u1]
    -- simp [Nat.max_comm]
    simp [add_comm]
    rw (config:={occs:=.pos [2]}) [Nat.max_comm]
    apply congrArg
    rw [Nat.max_comm]
    rw (config:={occs:=.pos [2]}) [Nat.max_comm]
    apply congrArg
    apply usen_sing'

  | succ roM2 iihh =>

    -- intro h6

    simp (config:={singlePass:=true}) [listrwgen]
    simp (config:={singlePass:=true}) [listrwgen] at hkk
    simp at hkk
    simp

    have urom:(usen O cf (k +1 - (roM2+1)) (Nat.pair x.l ((roM2+1) + 1 + x.r))).isSome := by
      have := nrop2 (roM2+1+1) (Nat.le_refl (roM2 + 1 + 1))
      simp at this
      apply usen_mono_dom _ this
      exact Nat.sub_le_add_right_sub k (roM2 + 1) 1
    simp at urom
    rw [add_assoc] at urom
    rw (config:={occs:=.pos [3]}) [add_comm] at urom
    simp [isSome.bind urom] at hkk ⊢

    have urom2:(usen O cf (k +1 - (roM2+1)) (Nat.pair x.l ((roM2+1) + x.r))).isSome := nrop2 (roM2+1) (le_add_right (roM2 + 1) 1)
    simp at urom2
    simp [isSome.bind urom2] at hkk ⊢



    have iihh1 := @iihh urom2 (a.max ((usen O cf (k - roM2) (Nat.pair x.l (roM2 + 1 + (x.r + 1)))).get urom)) ?_ ?_
    -- have iihh1 := @iihh ?_ ((use O cf (Nat.pair x.l (nnn + 1 + x.r))).get dom1) (a.max h5) ?_
    simp at iihh1
    rotate_left
    clear iihh
    ·
      intro j hj
      have := nrop2 j (le_add_right_of_le hj)
      exact this
    ·
      simp
      simp [Nat.max_comm] at hkk
      exact hkk



    simp [Nat.max_comm]
    rw [iihh1]
    simp [Nat.max_comm]
    have : ((usen O cf (k - roM2) (Nat.pair x.l (roM2 + 1 + (x.r + 1)))).get urom) = ((usen O cf (k - (roM2 + 1)) (Nat.pair x.l (roM2 + 1 + 1 + x.r))).get asddom) := by
      have : (roM2 + 1 + (x.r + 1)) = (roM2 + 1 + 1 + x.r) := by grind
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
-- att4
  constructor
  -- sorry
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

  induction (evaln O (k + 1) cf.rfind' x).get h2 - x.r generalizing y base h2 x with
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

    have nrop := n_rfind'_obtain_prop h2
    rw [asd] at nrop
    have nrop2 : (∀ j ≤ roM1 + 1, (usen O cf (k + 1 - j) (Nat.pair x.l (j + x.r))).isSome) := fun j a ↦ en2un (nrop.right.left j a)
    have asddom : (usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome := by
      have := nrop2 (roM1+1) (le_rfl)
      simp at this
      exact this
    simp [isSome.bind asddom]



    have aux0 : (evaln O (k + 1) cf (Nat.pair x.l (x.r + 1))).isSome := Option.isSome_of_mem (evaln_mono (show k≤k+1 from le_add_right k 1) (Option.get_mem nrfindt.right.right))
    have ih1 := @ih
      (Nat.pair x.l (x.r+1))
      -- (if roM1 = 0 then (base.max ((usen O cf (k + 1) x).get (en2un h1))) else (((usen O cf (k + 1) x).get (en2un h1)).max ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).get usenindtdom)))
      (y)
      ?_
      ?_
      ?_
      -- (base.max ((usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).get asddom))
      (base.max ((usen O cf (k+1) x).get (en2un h1)))
      ?_
      ?_
    rotate_left
    ·
      exact aux0
    ·

      exact Option.isSome_of_mem (evaln_mono (show k≤k+1 from le_add_right k 1) (Option.get_mem evalnindtdom))
    ·
      exact aux0
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
        simp [hroM1]
        have : ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).get usenindtdom) = ((usen O cf (k + 1) (Nat.pair x.l (x.r + 1))).get (en2un aux0)) := by sorry
        rw [this]
      else
        clear ih
        simp [hroM1]
        have roM1M1: roM1 = roM1-1+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero hroM1)
        simp (config:={singlePass:=true}) [roM1M1] at *
        have : (usen O cf.rfind' k (Nat.pair x.l (x.r + 1 + 1))).isSome := by
          have := nrop2 2 (le_add_left 2 (roM1 - 1))
          have := usen_mono_dom (show k + 1 - 2 ≤ k from by grind) this

          exact this
          sorry
        simp [isSome.bind this]
        apply congrArg
        apply congrArg

        have : k=k-1+1 := by sorry
        simp (config:={singlePass:=true}) [this]
        rw [usen.eq_10]

        sorry

    simp at ih1
    have := @lemlemlem2 O k cf x roM1 y (asddom) base h1 (en2un h1) (en2un aux0) (fun j a ↦ nrop2 j a) ih1
    rw [this] at ih1
    rw [ih1]

-- mpr
  intro h
  rcases h with ⟨h2,h3⟩
  have h1 : (evaln O (k + 1) cf x).isSome := by exact (nrf (en2un h2)).right.right
  use h1
  use h2

  revert h3
  induction (evaln O (k + 1) cf.rfind' x).get h2 - x.r generalizing y with
  | zero =>
    simp
    simp [isSome.bind $ en2un h1]
  | succ roM1 ih =>
    simp
    simp at ih
    intro h
    simp (config:={singlePass:=true}) [listrwgen] at h
    simp at h

    have asddom : (usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome := by sorry
    simp [isSome.bind asddom] at h

    sorry









-- att4
  sorry




    constructor
    simp

    intro h
    have hdom : (usen O (rfind' cf) (k + 1) x).isSome := by exact Option.isSome_of_mem h
    have h_og := h
    rcases nrf hdom with ⟨xlek,usen_base_dom,evaln_base_dom⟩
    have h := nrfh h


    -- simp at ⊢
    -- have : (usen O cf.rfind' (k + 1) x).isSome := by exact
    have evaln_ver_dom := un2en $ Option.isSome_of_mem h_og
    -- #check
    simp [isSome.bind evaln_ver_dom]
    -- let h7 := (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom
    -- rw [show (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom = h7 from rfl]
    -- simp [usen] at h
    -- have xlek : x≤k := by contrapose h; simp [h, Option.bind]
    -- simp [xlek] at h ⊢
    -- have usen_base_dom := nrf_usen_base_dom hdom
    -- simp [isSome.bind usen_base_dom] at h
    -- have evaln_base_dom : (evaln O (k + 1) cf x).isSome := by contrapose h; simp at h; simp [h]
    -- simp [isSome.bind evaln_base_dom] at h ⊢
    simp [show x≤k from sorry]
    -- att3
    expose_names
    let base:=0
    have rwbase : 0=base := rfl
    have : (if (evaln O (k + 1) cf x).get ((nrf (Option.isSome_of_mem h_1)).right.right) = 0 then usen O cf (k + 1) x else (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦ some (((usen O cf (k + 1) x).get ((nrf (Option.isSome_of_mem h_1)).right.left)).max usen_indt))
      =
      Nat.max <$> some base <*>  (if (evaln O (k + 1) cf x).get ((nrf (Option.isSome_of_mem h_1)).right.right) = 0 then usen O cf (k + 1) x else (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦ some (((usen O cf (k + 1) x).get ((nrf (Option.isSome_of_mem h_1)).right.left)).max usen_indt)) := by sorry
    rw [this] at h
    clear this

    have h :
    Nat.max <$> some base <*>  (if(evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r=0 then usen O cf (k + 1) x else (usen O cf.rfind' (k + 1 - 1) (Nat.pair x.l (x.r + 1))).bind fun usen_indt ↦ some (((usen O cf (k + 1) x).get ((nrf (Option.isSome_of_mem h_1)).right.left)).max usen_indt)) =some y := by sorry
    -- have h2 : (some y)= (some y).max 0 := by
    -- generalize 0=base at ⊢
    rw [rwbase]
    -- rw [show (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r = (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r-1+1 from by grind]
    -- revert contra_for_base_case
    revert h
    have basecaseaux (next_halt:(evaln O k cf.rfind' (Nat.pair x.l (x.r + 1))).isSome): ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r=0)→ (evaln O (k + 1) cf  x).get evaln_base_dom =0 := by
      contrapose

      intro h
      simp [evaln]
      simp [h]
      have := nrfind'_geq_xr (next_halt)
      simp at this
      -- grind -- this works
      sorry
    -- revert basecaseaux
    generalize base=gbase at h ⊢
    -- induction (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r-1 generalizing base with
    induction (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r generalizing gbase with
    | zero =>
      -- intro contra_for_base_case
      simp (config:={singlePass:=true}) [listrwgen]
      simp

      -- non 2 version
      simp [isSome.bind usen_base_dom]
      intro basecaseaux
      -- simp [basecaseaux]

      simp_all

      -- problem is max includes indt in h, while goal doesnt
      -- non 2 version


      have usen_nextbase_dom : (usen O cf k (Nat.pair x.l (1 + x.r))).isSome := by
        rw [add_comm]
        exact usen_nextbase_dom
      simp [isSome.bind usen_nextbase_dom]
      simp [isSome.bind usen_base_dom]
      simp (config:={singlePass:=true}) [nrf_aux usen_indt_dom ] at *

      simp [usen] at h
      have evaln_nextbase_dom := un2en usen_nextbase_dom
      have evaln_nextbase_zero : (evaln O (k-1 + 1) cf (Nat.pair x.l (x.r+1))).get evaln_nextbase_dom = 0 := by
        contrapose contra_for_base_case
        simp
        simp (config:={singlePass:=true}) [nrf_aux usen_indt_dom ] at evaln_ver_dom evaln_base_dom
        simp (config:={singlePass:=true}) [evaln] at evaln_ver_dom
        simp [xlek] at evaln_ver_dom
        simp [isSome.bind evaln_base_dom] at evaln_ver_dom


        have : evaln O (k - 1 + 1 + 1) cf.rfind' x = some x.r := by
          simp (config:={singlePass:=true}) [evaln]
          simp [xlek]
          simp [isSome.bind evaln_base_dom]
          intro h1
          contradiction
        sorry
      -- simp [add_comm] at evaln_nextbase_zero

      simp [evaln_nextbase_zero] at h
      -- sorry
      rw [←h]
      rw [←Nat.max_assoc]
      rw [Nat.max_comm]
      rw (config:={occs:=.pos [2]}) [Nat.max_comm]
      simp [add_comm]

    | succ roM1 ih =>
      simp (config:={singlePass:=true}) [listrwgen]
      simp



      have hehe_dom : (usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome := by
      -- have hehe_dom : (usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).isSome := by

        sorry
      simp [isSome.bind hehe_dom] at h ⊢
      -- intro hhh
      simp at ih

      -- sorry
      have := ih (gbase.max ((usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).get hehe_dom)) ?_ ?_
      -- have := ih (base.max ((usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).get hehe_dom)) ?_
      -- have := ih (h_og) (base.max ((usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).get hehe_dom)) ?_
      rotate_left
      ·
        -- aesop
        sorry
      ·

        intro g1
        intro g2

        sorry
      exact fun h ↦ this
      -- problem with non2: need to show rom1≠0,
      -- exact this
      exact this
      -- exact this hhh
      sorry

      exact fun contra_for_base_case ↦
        ih (base.max ((usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).get hehe_dom))
          contra_for_base_case




















    sorry
    -- att2
    cases hevaln_base:(evaln O (k + 1) cf x).get evaln_base_dom with
    | zero =>
      have : (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom = 0 := by sorry
      simp [this, isSome.bind usen_base_dom]
      simp [hevaln_base] at h
      simp [usen] at h_og
      sorry
      simp_all [hevaln_base, this]
      -- simp_all [this, isSome.bind usen_base_dom]

      sorry
      simp_all only [↓reduceIte]
    | succ _ =>
    simp [hevaln_base] at h ⊢
    have usen_indt_dom : ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1)))).isSome := by contrapose h; simp at h; simp [h]

    -- have nrf2 := @nrf O cf k (Nat.pair x.l (x.r + 1)) exact?%
    have nrf2 := nrf (usen_indt_dom)
    have nrf2_aux := nrf_aux (usen_indt_dom)

    have usen_nextbase_dom : (usen O cf k (Nat.pair x.l ( x.r+1))).isSome := by
      exact nrf2.right.left
    simp [isSome.bind usen_indt_dom] at h ⊢
    -- simp (config:={singlePass:=true}) [listrwgen]
    -- simp

    have contra_for_base_case : (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r ≠ 0 := by
      simp [evaln]
      simp [hevaln_base]
      have := nrfind'_geq_xr (un2en usen_indt_dom)
      simp at this
      exact Nat.sub_ne_zero_iff_lt.mpr this

    -- cases hevaln_base2:(evaln O (k + 1) cf x).get evaln_base_dom with
    -- | zero =>
    --   have : (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom = 0 := by sorry
    --   simp [this, isSome.bind usen_base_dom]
    --   simp [hevaln_base] at h
    --   simp [usen] at h_og
    --   sorry
    --   simp_all [hevaln_base, this]
    --   -- simp_all [this, isSome.bind usen_base_dom]

    --   sorry
    --   simp_all only [↓reduceIte]
    -- | succ _ =>
    -- have contra_for_base_case2 : (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r -1 ≠ 0 := by
    --   simp [evaln]
    --   simp [hevaln_base]
    --   simp (config:={singlePass:=true}) [nrf2_aux]
    --   simp [evaln]

    --   have
    --   have := nrfind'_geq_xr (un2en usen_indt_dom)
    --   simp at this

      -- exact Nat.sub_ne_zero_iff_lt.mpr this

    rw [show ((usen O cf (k + 1) x).get usen_base_dom).max ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).get usen_indt_dom)= (((usen O cf (k + 1) x).get usen_base_dom).max ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1))).get usen_indt_dom)).max 0 from by simp ] at h
    generalize 0=base at h ⊢
    -- rw [show (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r = (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r-1+1 from by grind]
    revert contra_for_base_case

    -- induction (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r-1 generalizing base with
    induction (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom -x.r generalizing base with
    | zero =>
      -- intro contra_for_base_case
      simp (config:={singlePass:=true}) [listrwgen]
      simp

      -- non 2 version
      simp [isSome.bind usen_base_dom]
      -- problem is max includes indt in h, while goal doesnt
      -- non 2 version


      have usen_nextbase_dom : (usen O cf k (Nat.pair x.l (1 + x.r))).isSome := by
        rw [add_comm]
        exact usen_nextbase_dom
      simp [isSome.bind usen_nextbase_dom]
      simp [isSome.bind usen_base_dom]
      simp (config:={singlePass:=true}) [nrf_aux usen_indt_dom ] at *

      simp [usen] at h
      have evaln_nextbase_dom := un2en usen_nextbase_dom
      have evaln_nextbase_zero : (evaln O (k-1 + 1) cf (Nat.pair x.l (x.r+1))).get evaln_nextbase_dom = 0 := by
        contrapose contra_for_base_case
        simp
        simp (config:={singlePass:=true}) [nrf_aux usen_indt_dom ] at evaln_ver_dom evaln_base_dom
        simp (config:={singlePass:=true}) [evaln] at evaln_ver_dom
        simp [xlek] at evaln_ver_dom
        simp [isSome.bind evaln_base_dom] at evaln_ver_dom


        have : evaln O (k - 1 + 1 + 1) cf.rfind' x = some x.r := by
          simp (config:={singlePass:=true}) [evaln]
          simp [xlek]
          simp [isSome.bind evaln_base_dom]
          intro h1
          contradiction
        sorry
      -- simp [add_comm] at evaln_nextbase_zero

      simp [evaln_nextbase_zero] at h
      -- sorry
      rw [←h]
      rw [←Nat.max_assoc]
      rw [Nat.max_comm]
      rw (config:={occs:=.pos [2]}) [Nat.max_comm]
      simp [add_comm]

    | succ roM1 ih =>
      simp (config:={singlePass:=true}) [listrwgen]
      simp



      have hehe_dom : (usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).isSome := by
      -- have hehe_dom : (usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).isSome := by

        sorry
      simp [isSome.bind hehe_dom] at h ⊢
      -- intro hhh

      have := ih (base.max ((usen O cf (k - roM1) (Nat.pair x.l (roM1 + 1 + x.r))).get hehe_dom)) ?_
      -- have := ih (base.max ((usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).get hehe_dom)) ?_
      -- have := ih (h_og) (base.max ((usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).get hehe_dom)) ?_
      rotate_left
      ·

        sorry
      -- problem with non2: need to show rom1≠0,
      -- exact this
      exact this hhh
      sorry

      exact fun contra_for_base_case ↦
        ih (base.max ((usen O cf (k - (roM1 + 1)) (Nat.pair x.l (roM1 + 2 + x.r))).get hehe_dom))
          contra_for_base_case


    simp [usen] at h
    have xlek : x≤k := by contrapose h; simp [h, Option.bind]
    simp [xlek] at h ⊢
    have usen_base_dom : (usen O cf (k + 1) x).isSome := by contrapose h; simp at h; simp [h]
    simp [isSome.bind usen_base_dom] at h
    have evaln_base_dom : (evaln O (k + 1) cf x).isSome := by contrapose h; simp at h; simp [h]
    simp [isSome.bind evaln_base_dom] at h ⊢

    cases hevaln_base:(evaln O (k + 1) cf x).get evaln_base_dom with
    | zero =>
      have : (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom = 0 := by sorry
      simp [this, isSome.bind usen_base_dom]
      simp_all only [↓reduceIte]
    | succ _ =>
      simp [hevaln_base] at h ⊢
      have usen_indt_dom : ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1)))).isSome := by contrapose h; simp at h; simp [h]
      simp [isSome.bind usen_indt_dom] at h ⊢
      simp (config:={singlePass:=true}) [listrwgen]
      simp


      have hehe_dom : (usen O cf (k + 1 - ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r))
          (Nat.pair x.l ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r + x.r))).isSome := by sorry
      simp [isSome.bind hehe_dom] at h ⊢


    -- simp
    induction k+1 generalizing x with
    | zero => simp [usen,evaln]
    | succ k ih =>
      constructor
      intro h
      have h_og := h

      simp at ih ⊢
      -- have : (usen O cf.rfind' (k + 1) x).isSome := by exact
      have evaln_ver_dom := un2en $ Option.isSome_of_mem h
      -- #check
      simp [isSome.bind evaln_ver_dom]
      simp [usen] at h ih

      have xlek : x≤k := by contrapose h; simp [h, Option.bind]
      simp [xlek] at h ⊢
      have usen_base_dom : (usen O cf (k + 1) x).isSome := by contrapose h; simp at h; simp [h]
      simp [isSome.bind usen_base_dom] at h
      have evaln_base_dom : (evaln O (k + 1) cf x).isSome := by contrapose h; simp at h; simp [h]
      simp [isSome.bind evaln_base_dom] at h ⊢

      cases hevaln_base:(evaln O (k + 1) cf x).get evaln_base_dom with
      | zero =>
        have : (evaln O (k + 1) cf.rfind' x).get evaln_ver_dom = 0 := by sorry
        simp [this, isSome.bind usen_base_dom]
        simp_all only [↓reduceIte]
      | succ _ =>
        simp [hevaln_base] at h ⊢
        have usen_indt_dom : ((usen O cf.rfind' k (Nat.pair x.l (x.r + 1)))).isSome := by contrapose h; simp at h; simp [h]
        simp [isSome.bind usen_indt_dom] at h ⊢
        simp (config:={singlePass:=true}) [listrwgen]
        simp


        have hehe_dom : (usen O cf (k + 1 - ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r))
            (Nat.pair x.l ((evaln O (k + 1) cf.rfind' x).get evaln_ver_dom - x.r + x.r))).isSome := by sorry
        simp [isSome.bind hehe_dom] at h ⊢




        have usen_indt_dom : ((usen O cf.rfind' k (Nat.pair n.l (n.r + 1)))).isSome := by contrapose h; simp at h; simp [h]
        clear h
        exact ih usen_indt_dom


      sorry


    sorry


theorem usen_sound : ∀ {c s n x}, x ∈ usen O c s n → x ∈ use O c n
:= by
-- | _, 0, n, x, h => by simp [usen] at h
-- | c, k + 1, n, x, h => by
  intro c k n x h
  induction k,c using CodeNatK.induction generalizing x n with
  | h0 c => simp [usen] at h
  | hzero k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
  | hsucc k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
  | hleft k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
  | hright k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
  | horacle k =>
    simp [use, usen, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨_, h⟩ := h
    simp [←h]
    suffices Part.some (n+1) = @HAdd.hAdd (Part ℕ) (Part ℕ) (Part ℕ) instHAdd (Part.some n) 1 from by
      rw [←this]
      exact Part.mem_some_iff.mpr rfl
    have := Part.some_add_some n 1
    rw [←this]
    exact rfl
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
      apply hf
      exact h1
    · simp
      intro hh1
      intro hh
      -- have hh := hh.right
      simp [Option.bind_eq_some_iff] at hh
      rcases hh with ⟨hh,⟨h3,⟨h4,⟨h5,⟨h7,⟨h8,h9⟩⟩⟩⟩⟩⟩

      use h4
      constructor
      · exact evaln_sound h5
      · use hh
        constructor
        ·
          -- #check
          -- have main := usen_sound h3
          have main := ih h3
          simp [use] at main
          exact main
        · use h7
          constructor
          · exact @hg (Nat.pair n.l (Nat.pair m h4)) h7 h8
          · exact h9
  | hrfind k cf hfih =>
    -- have hf := hfih (k+1) (le_rfl)
    simp [use]
    have := usen_rfind_prop2.mp h
    have urop1 := usen_rfind_prop h
    -- have urop11 := urop1 1
    rcases urop1 0 (zero_le (rfind'_obtain (usen_rfind_prop_aux h))) with ⟨h1,h2⟩
    simp at h2

    rcases usen_dom_iff_evaln_dom.mp ⟨x,h⟩ with ⟨h7,h8⟩
    have h145: rfind'_obtain (usen_rfind_prop_aux h) = h7 - n.r := by
      simp [rfind'_obtain]
      simp [Part.eq_some_iff.mpr (evaln_sound h8)]
    simp [h145] at *

    -- simp [h8] at this
    simp_all

    have nlek : n≤k := by
      contrapose this
      simp [this, Option.bind]
    simp [nlek] at this

    use h7
    constructor
    exact evaln_sound h8

    -- let asd := h7 - n.r
    -- have rwasd : h7 - n.r = asd := rfl
    -- rw [rwasd]
    -- rw [rwasd] at this
    revert this
    revert urop1
    generalize 0=a
    -- revert 0
    induction h7 - n.r generalizing a with
    | zero =>
      -- simp [hind] at this
      simp
      intro h3 h4 this
      use (ForInStep.yield (a.max h1))
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
        have := urop1 j (le_add_right_of_le jnn)
        exact this

      rcases urop1 (nn+1) (Nat.le_refl (nn + 1)) with ⟨h3,h4⟩
      simp at h4
      rw (config:={occs:=.pos [1]}) [add_comm] at h4
      simp [h4]
      have hknn : k-nn-1+1=k-nn := by
        contrapose h4
        simp at h4
        have : k-nn=0 := by grind
        simp [this,usen]


      -- hfih (k+1) (le_rfl)
      have hf2 := @hfih (k-nn) (by grind) (Nat.pair n.l (nn + 1 + n.r)) h3 h4
      -- simp at this
      -- have hf2 := this h4

      intro h5
      use (ForInStep.yield (a.max h3))
      constructor
      use h3
      simp
      have ih1 := ih (a.max h3) aux0
      clear ih
      have ih2 := ih1 h5
      clear ih1
      exact ih2

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
  induction nn generalizing h5 n a with
  | zero =>
    simp
    intro h6

    have : use O cf n = Part.some h57 := by
      exact Part.get_eq_iff_eq_some.mp (_root_.id (Eq.symm h57def))
    simp_all
    have := rop3 1 (le_rfl)
    rw [add_comm] at this
    simp [Part.Dom.bind this]
    have : h5 = ((use O cf (Nat.pair n.l (1 + n.r))).get this) := by
      exact (Part.eq_get_iff_mem this).mpr h6
    simp [←this]
    rw (config:={occs:=.pos [2]}) [Nat.max_comm]

  | succ nnn iihh =>

    intro h6

    simp (config:={singlePass:=true}) [listrwgen]
    simp

    have dom1 : (use O cf (Nat.pair n.l (nnn + 1 + n.r))).Dom := by
      have := rop3 (nnn+1) (le_add_right (nnn + 1) 1)
      rw [show n.r + (nnn + 1) = nnn + 1 + n.r from by grind] at this
      exact this
    simp [Part.Dom.bind dom1]
    have dom2 : (use O cf (Nat.pair n.l (nnn + 1 + (1 + n.r)))).Dom := by
      rw [show (nnn + 1 + (1 + n.r)) = nnn + 1 + 1 + n.r from by grind]
      exact Part.dom_iff_mem.mpr ⟨h5,h6⟩
    simp [Part.Dom.bind dom2]



    have iihh1 := @iihh ((use O cf (Nat.pair n.l (nnn + 1 + n.r))).get dom1) (a.max h5) (Nat.pair n.l (n.r)) ?_
    simp at iihh1
    clear iihh
    rotate_right
    ·
      intro j hj
      have := rop3 j (le_add_right_of_le hj)
      simpa

    have iihh2 := iihh1 h57dom ?_ ?_
    clear iihh1
    rotate_left
    ·
      exact h57def
    · exact Part.get_mem dom1

    rw [iihh2]


    have : (use O cf (Nat.pair n.l (nnn + 1 + (1 + n.r)))).get dom2 = h5 := by
      simp [show (nnn + 1 + (1 + n.r)) = nnn + 1 + 1 + n.r from by grind]
      exact
        Part.get_eq_of_mem h6
          (congrArg (fun x ↦ use O cf (Nat.pair n.l x))
              (have this := lemlemlem._proof_1_5 nnn rop3 h57dom h57def h6 dom1 dom2 iihh2;
              this) ▸
            dom2)
    rw [this]
    rw (config:={occs:=.pos [2]}) [Nat.max_comm]
lemma lemlemlem2
{a n:ℕ}
(h6:h5 ∈ use O cf (Nat.pair n.l (nn + 1 + n.r)))
(rop3:∀ j ≤ nn + 1, (use O cf (Nat.pair n.l (n.r + j))).Dom)
(h57dom:(use O cf n).Dom)
(h57def:h57=(use O cf n).get h57dom)
(aux123 : (use O cf n).Dom)
(i2 : usen O cf (i1 + 1) n = some ((use O cf n).get aux123))
(hf : ∀ {n x : ℕ}, x ∈ use O cf n → ∃ k, usen O cf (k + 1) n = some x)
(hkk : (forIn (List.range (nn + 1)).reverse (a.max h57) fun i r ↦
    (usen O cf (kk + 1 - i) (Nat.pair n.l (i + (1 + n.r)))).bind fun a ↦ some (ForInStep.yield (r.max a))) =
  some x)
:
(  forIn (List.range (nn + 1)).reverse (a.max (h57)) fun i r ↦
    (usen O cf (kk+1-i) (Nat.pair n.l (i + (1 + n.r)))).bind fun use_i ↦ some (ForInStep.yield (r.max use_i)))
    =
((forIn (List.range (nn + 1)).reverse (a.max h5) fun i r ↦
    (usen O cf (kk.max i1 + 1 + 1 - i) (Nat.pair n.l (i + n.r))).bind fun usen_i ↦
      some (ForInStep.yield (r.max usen_i))))
 := by
  revert h6
  induction nn generalizing h5 n a with
  | zero =>
    simp
    intro h6
    simp_all

    -- have : use O cf n = Part.some h57 := by
    --   exact Part.get_eq_iff_eq_some.mp (_root_.id (Eq.symm h57def))
    -- have : h57 ∈ (use O cf n) := by exact
    --   (Part.get_eq_iff_mem h57dom).mp (_root_.id (Eq.symm h57def))
    -- rcases hf this with ⟨g1,g2⟩
    have : i1+1≤ kk.max i1 + 1 + 1 := by grind
    have := usen_mono this i2
    simp at this
    simp [this]


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



    -- simp [←this]
    rw (config:={occs:=.pos [2]}) [Nat.max_comm]
    exact hkk.symm

  | succ nnn iihh =>

    intro h6

    simp (config:={singlePass:=true}) [listrwgen]
    simp (config:={singlePass:=true}) [listrwgen] at hkk
    simp at hkk
    simp

    -- simplify the goal



    rcases hf h6 with ⟨g3,g4⟩
    have : ∃z,z∈(usen O cf (kk - nnn) (Nat.pair n.l (nnn + 1 + (1 + n.r)))) := by
      contrapose hkk
      simp at hkk
      have := Option.eq_none_iff_forall_ne_some.mpr hkk
      simp [this]
    rcases this with ⟨lmao3,lmao4⟩
    simp at lmao4
    simp [lmao4] at hkk
    simp [lmao4]
    rw [add_assoc] at g4
    -- rw [show ( nnn + 1 + 1 + n.r )= nnn + 1 + (1 + n.r)) from by grind] at g4
    #check usen_sing lmao4 g4
    simp [usen_sing lmao4 g4] at *


    have rtdom := rop3 (nnn+1) (le_add_right (nnn + 1) 1)
    rw [add_comm] at rtdom
    let rtval := (use O cf (Nat.pair n.l (nnn + 1 + n.r))).get rtdom
    -- have : use O cf (Nat.pair n.l (nnn + 1 + n.r)) = Part.some h57 := by
    --   exact Part.get_eq_iff_eq_some.mp (_root_.id (Eq.symm h57def))
    have : ∃z,z∈(usen O cf (kk.max i1 + 1 - nnn) (Nat.pair n.l (nnn + 1 + n.r))) := by
      contrapose hkk
      simp at hkk
      have := Option.eq_none_iff_forall_ne_some.mpr hkk
      simp (config:={singlePass:=true}) [listrwgen]
      have : (usen O cf (kk + 1 - nnn) (Nat.pair n.l (nnn + (1 + n.r)))) = Option.none := by
        rw [add_assoc] at this

        have ineq1: kk + 1 - nnn ≤ kk.max i1 + 1 - nnn := by grind
        simp [usen_mono_contra ineq1 this]
      simp [this]
    -- simp [this]
    -- have : rtval ∈ (use O cf (Nat.pair n.l (nnn + 1 + n.r))) := by exact Part.get_mem rtdom
    rcases this with ⟨g1,g2⟩
    simp at g2
    simp [g2]

    -- have : i1+1≤ kk.max i1 + 1 := by grind
    -- have := usen_mono this g2
    -- simp at this
    -- simp [this]



    -- simp [usen_sing lmao4 g4] at hkk

    have dom1 : (use O cf (Nat.pair n.l (nnn + 1 + n.r))).Dom := by
      have := rop3 (nnn+1) (le_add_right (nnn + 1) 1)
      rw [show n.r + (nnn + 1) = nnn + 1 + n.r from by grind] at this
      exact this
    -- simp [Part.Dom.bind dom1]
    -- have dom2 : (use O cf (Nat.pair n.l (nnn + 1 + (1 + n.r)))).Dom := by
    --   rw [show (nnn + 1 + (1 + n.r)) = nnn + 1 + 1 + n.r from by grind]
    --   exact Part.dom_iff_mem.mpr ⟨h5,h6⟩
    -- simp [Part.Dom.bind dom2]



    have iihh1 := @iihh ((use O cf (Nat.pair n.l (nnn + 1 + n.r))).get dom1) (a.max h5) (Nat.pair n.l (n.r)) ?_
    simp at iihh1
    clear iihh
    rotate_right
    ·
      intro j hj
      have := rop3 j (le_add_right_of_le hj)
      simpa

    have iihh2 := iihh1 h57dom ?_ ?_ ?_ ?_ ?_
    clear iihh1
    rotate_left
    ·
      exact h57def
    · exact h57dom
    · exact i2
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
-- set_option maxHeartbeats 50000 in
theorem usen_complete {c n x} : x ∈ use O c n ↔ ∃ s, x ∈ usen O c s n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => usen_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ usen O  c (k + 1) n
  · exact ⟨k + 1, h⟩

  induction c generalizing n x with
      -- simp [use, usen, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    simp [use, usen, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    -- constructor

    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    simp [use, usen, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨y, hy, ⟨hx1,⟨hx2,⟨hx3,⟨hx4,hx5⟩⟩⟩⟩⟩
    -- rcases h with ⟨y, hy, ⟨hx1,hx2⟩⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx4 with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    -- exact
    --   ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
    --     usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
    --     usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
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
    simp [use, usen, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    revert h
    generalize n.l = n₁; generalize n.r = n₂
    -- induction' n₂ with m IH generalizing x n <;> simp [Option.bind_eq_some_iff]
    induction' n₂ with m IH generalizing x n
    ·
      intro h
      -- simp [use] at h
      -- use n+1
      -- constructor
      -- exact le_add_right n 1
      -- simp at h
      -- simp [Option.bind_eq_some_iff]
      -- have : Nat.rec (use O cf n.l) (fun iM1 IH ↦
      -- (eval O (cf.prec cg) (Nat.pair n.l iM1)).bind fun IH_N ↦
      --   IH.bind fun y ↦ Part.map y.max (use O cg (Nat.pair n.l (Nat.pair iM1 IH_N)))) n.r = 2 := by sorry
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    ·
      -- intro y hy hx
      intro h
      simp at h
      rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩

      -- #check IH h4
      -- #check hg h6
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
        #check evaln_sing hh2 hh4
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
    -- generalize 0=a at h
    -- generalize 0=a at *
    rcases h with ⟨h1,h2,h3⟩

    have rogeq : n.r≤h1 := eval_rfind_prop5 h2
      -- have := rfind'_geq_xr hdom1
    rw [show h1=h1-n.r+n.r from by simp [rogeq]] at h2
    clear rogeq



    have hdom1 := Part.dom_iff_mem.mpr ⟨h1-n.r+n.r,h2⟩
    have hdom : (use O cf.rfind' n).Dom := use_dom_iff_eval_dom.mpr hdom1
    #check rfind'_obtain_prop hdom1
    have rop := rfind'_obtain_prop hdom1
    have rop4 := rfind'_obtain_prop_4 hdom1
    have rop6 := rfind'_obtain_prop_6 hdom1
    have urop1 := use_rfind_prop hdom
    -- have unrop := usen_rfind_prop
    -- have h144: rfind'_obtain (hdom1) = h1 - n.r := by
    --   simp [rfind'_obtain]
    --   simp [Part.eq_some_iff.mpr h2]
    have h145: rfind'_obtain (u2e hdom) = h1 - n.r := by
      simp [rfind'_obtain]
      simp [Part.eq_some_iff.mpr h2]
    simp [h145] at *
    clear h145


    -- have rothm : h1-n.r=h1

    revert h3
    revert h2
    revert urop1
    revert rop6
    revert rop4
    revert rop
    -- revert rogeq



    induction h1-n.r generalizing a n with
    | zero =>
      -- sorry
      simp_all
      intro urop1
      intro rop1
      -- intro rop2
      -- intro rop4
      intro h2
      intro rop6
      intro h4
      intro h5
      intro h6
      intro h7
      intro h8


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
      have aux2 := evaln_mono (show (h9) ≤ (h9 - 1).max (h14 + 1) + 1 from by grind) h10
      simp at aux2
      simp [aux2]
      have aux0 := usen_mono (show (h14 + 1) ≤ (h9 - 1).max (h14 + 1) + 1 from by grind) h15
      simp at aux0
      simp [aux0]



    | succ nn ih =>
      -- here, ih is wrong. nn should depend on n in the x∈ clause
      simp (config:={singlePass:=true}) [listrwgen]
      simp
      intro urop1 rop1 rop2
      intro rop4
      intro rop6
      -- intro rop5
      intro rop3
      intro h2 h3 h5 h6 h7 h8
      -- intro h2 h3


      have rop10 := rop1 1 (le_add_left 1 nn)
      have rop11 := e2u rop10
      have rop40 := rop4 1 (le_add_left 1 nn)
      -- rw [add_comm] at rop40
      have rop41 := e2u rop40


      have h57dom := rop3 0 (le_add_left 0 (nn + 1))
      simp at h57dom
      let h57 := (use O cf n).get h57dom

      -- have ih1 := @ih (Nat.pair n.l (1 + n.r)) (a.max h5) (rop40) rop41 ?_ ?_ ?_ ?_ ?_
      have ih1 := @ih (Nat.pair n.l (1 + n.r)) (a.max h57) (rop40) rop41 ?_ ?_ ?_ ?_ ?_
      clear ih
      rotate_right 5
      -- rotate_right
      · simp
        constructor
        rw [←add_assoc]
        exact urop1
        constructor
        intro j hj
        rw [←add_assoc]
        exact rop1 (j+1) (Nat.add_le_add_right hj 1)
        intro j hj
        rw [←add_assoc]
        exact rop2 (j+1) (Nat.add_le_add_right hj 1)
      · simp
        intro j hj
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


      -- use kk
      have nlek : (n ≤ kk.max i1 + 1) := by
        contrapose i2
        simp at i2
        have : i1+1<n := by grind

        intro h16
        have contra := usen_bound h16
        have : n<n := by
          exact Nat.lt_trans contra this
        simp at this
      have nlek2 : (Nat.pair n.l (1 + n.r) ≤ kk) := by
        contrapose hkk
        simp [hkk,Option.bind]

      use (Nat.max kk (i1))+1
      simp [nlek] at ⊢
      simp [nlek2] at hkk
      -- rcases evaln_complete.mp (h2)
      -- have hh22 := evaln_sing h22 h20
      -- simp at h22
      -- rw [h22] at hkk
      -- rw [hh22] at hkk







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

      simp [-ge_iff_le,-le_of_subsingleton,-le_refl,-Nat.le_refl] at hkk
      have : nn + 1 + n.r - (1 + n.r) + 1 = nn + 1 := by
        rw [add_assoc]
        rw [Nat.add_sub_cancel_right nn (1+n.r)]
      rw [this] at hkk
      clear this




      rcases evaln_complete.mp h2 with ⟨h9,h10⟩
      rcases hf h6 with ⟨h14,h15⟩
      rcases usen_dom_iff_evaln_dom.mp ⟨h5,h15⟩ with ⟨h16,h17⟩

      -- use (Nat.max (h9-1) (h14+1)+nn)
      -- rcases usen_dom_iff_evaln_dom.mpr ⟨nn + 1 + n.r,h10⟩ with ⟨h12,h13⟩
      -- have aux2 := evaln_mono (show (h9) ≤ (h9 - 1).max (h14 + 1) + nn + 1 from by grind) h10
      -- simp at aux2
      -- simp [aux2]
      -- simp only [Option.bind]

      have : (evaln O (kk.max i1 + 1 + 1) cf.rfind' n) = some (nn + 1 + n.r) := by sorry
      simp [this]

      have : (usen O cf (kk.max i1 +1 - nn) (Nat.pair n.l (nn + 1 + n.r))) = some h5 := by sorry
      simp [this]


      have lemlem2 := @lemlemlem2 O cf nn h5 h57 i1 kk x a n (h6) (fun j a ↦ rop3 j a) (h57dom) rfl h57dom i2 (fun a ↦ hf a) (hkk)
      simp_all only [Option.mem_def]

  | oracle =>
    simp [use] at h
    use (n+1)
    simp [usen]
    rw [show @OfNat.ofNat (Part ℕ) 1 One.toOfNat1 = Part.some 1 from rfl] at h
    rw [Part.some_add_some n 1] at h
    exact (Part.mem_some_iff.mp h).symm
  | _ =>
    simp [use] at h
    use (n+1)
    simp [usen]
    rw [show @OfNat.ofNat (Part ℕ) 0 Zero.toOfNat0 = Part.some 0 from rfl] at h
    exact (Part.mem_some_iff.mp h).symm

theorem asodnioasndasidnioasdnaiosdnaiodnioasdioandsnda {n:ℕ}: (nn + 1 + n.r - n.r + n.r) = nn +1 +n.r := by
  simp only [add_tsub_cancel_right]

theorem use_eq_rfindOpt (c n) : use O c n = Nat.rfindOpt fun s => usen O c s n :=
  Part.ext fun x => by
    refine usen_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply usen_mono hl






theorem eval_pair_dom (h:(eval O (pair cf cg) x).Dom) : (eval O cf x).Dom ∧ (eval O cg x).Dom := by
  contrapose h
  push_neg at h
  simp [eval, Seq.seq]
  by_cases hh:(eval O cf x).Dom
  · exact fun a ↦ h hh
  · simp [Part.eq_none_iff'.mpr hh]
theorem eval_comp_dom_aux (h:(eval O (comp cf cg) x).Dom) : (eval O cg x).Dom := by exact Part.Dom.of_bind h
theorem eval_comp_dom
(h:(eval O (comp cf cg) x).Dom)
:
(eval O cg x).Dom
∧
(eval O cf ((eval O cg x).get (eval_comp_dom_aux h))).Dom
:= by
  constructor
  · contrapose h
    push_neg at h
    simp [eval]
    intro hdom
    exact fun a ↦ h hdom
  · simp [eval] at h
    contrapose h
    simp
    intro hdom
    exact h
theorem eval_prec_dom_aux
(h:(eval O (prec cf cg) (Nat.pair x (i+1))).Dom)
:
(eval O (prec cf cg) (Nat.pair x i)).Dom
:= by
  simp [eval] at h ⊢
  contrapose h
  simp [h]
theorem eval_prec_dom'
(h:(eval O (prec cf cg) (Nat.pair x 0)).Dom)
:
(eval O cf x).Dom
:= by
  simp [eval] at h
  exact h
theorem eval_prec_dom
(h:(eval O (prec cf cg) (Nat.pair x (i+1))).Dom)
:
(eval O cf x).Dom ∧
(
let eval_prev := (eval O (prec cf cg) (Nat.pair x i)).get (eval_prec_dom_aux h)
(eval O cg (Nat.pair x (Nat.pair i (eval_prev)))).Dom
)
:= by
  induction i with
  | zero =>
    simp [eval] at h ⊢
    aesop? says
      obtain ⟨w, h⟩ := h
      simp_all only [and_self]
  | succ n ih =>
    simp [eval] at h ⊢

    simp_all only
    obtain ⟨w, h⟩ := h
    obtain ⟨w, h⟩ := w
    simp_all only [and_true]
    have : (eval O (cf.prec cg) (Nat.pair x (n + 1))).Dom := by (expose_names; exact eval_prec_dom_aux h_1)
    exact (ih this).left

theorem use_pair_dom (h:(use O (pair cf cg) x).Dom) : (use O cf x).Dom ∧ (use O cg x).Dom := by
  exact exists_prop.mp h
theorem use_comp_dom_aux (h:(use O (comp cf cg) x).Dom) : (eval O cg x).Dom := by
  simp [use] at h
  contrapose h
  simp [Seq.seq]
  exact fun a x_1 a ↦ h x_1
theorem use_comp_dom (h:(use O (comp cf cg) x).Dom) : (use O cg x).Dom ∧ (use O cf ((eval O cg x).get (use_comp_dom_aux h))).Dom := by
  simp [use,Seq.seq] at h
  aesop? says
    simp_all only [true_and]
    obtain ⟨left, right⟩ := h
    obtain ⟨w, h⟩ := right
    simp_all only
theorem use_prec_dom_aux
(h:(use O (prec cf cg) (Nat.pair x (i+1))).Dom)
:
(eval O (prec cf cg) (Nat.pair x i)).Dom
:= by
  simp [use] at h
  contrapose h
  simp [Seq.seq]
  aesop? says
    intro a x_1
    simp_all only [not_true_eq_false]
theorem use_prec_dom'
(h:(use O (prec cf cg) (Nat.pair x 0)).Dom)
:
(use O cf x).Dom
:= by
  simp [use] at h
  exact h
theorem use_prec_dom
(h:(use O (prec cf cg) (Nat.pair x (i+1))).Dom)
:
(use O cf x).Dom
∧
(
let eval_prev := (eval O (prec cf cg) (Nat.pair x i)).get (use_prec_dom_aux h)
(use O cg (Nat.pair x (Nat.pair i eval_prev))).Dom)
:= by
  simp [use,Seq.seq] at h
  simp []
  induction i with
  | zero =>
    simp
    aesop? says
      simp_all only [rec_zero, eval_prec_zero, true_and]
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := right
      simp_all only
  | succ n ih =>
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_1⟩ := left
    obtain ⟨w, h⟩ := right
    obtain ⟨w_1, h_2⟩ := right_1
    simp_all only [and_true]
    simp at ih
    exact (ih (e2u w) h_2).left


theorem use_rfind'_dom
(h:(use O (rfind' cf) x).Dom) :
∀ j ≤ rfind'_obtain (u2e h),
  (use O cf (Nat.pair x.l (j+x.r))).Dom := by
  have aux0 := (rfind'_obtain_prop (u2e h)).right.left
  exact fun j a ↦ e2u (aux0 j a)

theorem use_mono_pair (hh:(use O (pair cf cg) x).Dom):
  ((use O cf x).get ((use_pair_dom hh).left) ≤ (use O (pair cf cg) x).get hh)
  ∧
  ((use O cg x).get ((use_pair_dom hh).right) ≤ (use O (pair cf cg) x).get hh)
  := by
    simp only [use, Seq.seq]
    simp [Part.Dom.bind ((use_pair_dom hh).left)]
theorem use_mono_comp (hh:(use O (comp cf cg) x).Dom):
  ((use O cg x).get ((use_comp_dom hh).left) ≤ (use O (comp cf cg) x).get hh)
  ∧
  ((use O cf ((eval O cg x).get (use_comp_dom_aux hh))).get ((use_comp_dom hh).right) ≤ (use O (comp cf cg) x).get hh)
  := by
    simp only [use, Seq.seq]
    simp [Part.Dom.bind ((use_comp_dom hh).left)]
    simp [Part.Dom.bind (use_comp_dom_aux hh)]
theorem use_mono_prec' (hh:(use O (prec cf cg) (Nat.pair x 0)).Dom):
((use O cf x).get (use_prec_dom' hh) ≤ (use O (prec cf cg) (Nat.pair x 0)).get hh)
:= by
  simp [use]
theorem use_mono_prec_1 (hh:(use O (prec cf cg) (Nat.pair x (i+1))).Dom):
(use O (prec cf cg) (Nat.pair x i)).get (e2u $ use_prec_dom_aux hh) ≤ (use O (prec cf cg) (Nat.pair x (i+1))).get hh
  := by
    simp  [use.eq_8]
    have : (Nat.rec (use O cf x)
        (fun iM1 IH ↦
          (eval O (cf.prec cg) (Nat.pair x iM1)).bind fun IH_N ↦
            Part.map Nat.max IH <*> use O cg (Nat.pair x (Nat.pair iM1 IH_N)))
        i) = (use O (cf.prec cg) (Nat.pair x i)) := by simp [use]
    simp [this]
    simp [Seq.seq]
    simp [Part.bind, Part.assert]
-- todo: simplify below proof
theorem use_mono_prec (hh:(use O (prec cf cg) (Nat.pair x (i+1))).Dom):
((use O cf x).get ((use_prec_dom hh).left) ≤ (use O (prec cf cg) (Nat.pair x (i+1))).get hh)
∧
let eval_prev := (eval O (prec cf cg) (Nat.pair x i)).get (use_prec_dom_aux hh)
(
(use O cg (Nat.pair x (Nat.pair i eval_prev))).get ((use_prec_dom hh).right) ≤ (use O (prec cf cg) (Nat.pair x (i+1))).get hh
)
  := by
    induction i with
    | zero =>
      simp only [use, Seq.seq]
      simp [Part.Dom.bind ((use_prec_dom hh).left)]
      have := eval_prec_dom_aux (u2e hh)
      simp at this
      simp [Part.Dom.bind (this)]
    | succ n ih =>
      have h3' := eval_prec_dom_aux (u2e hh)
      simp only at h3'
      have h5' := eval_prec_dom_aux h3'

      have stupidrewrite : (Nat.rec (use O cf x)
                  (fun iM1 IH ↦
                    (eval O (cf.prec cg) (Nat.pair x iM1)).bind fun IH_N ↦
                      IH.bind fun y ↦ Part.map y.max (use O cg (Nat.pair x (Nat.pair iM1 IH_N))))
                  n) = use O (prec cf cg) (Nat.pair x n) := by
                  simp [use]
                  rfl
      have h8 := eval_prec_dom (h3')
      simp at h8
      have h9 := h8.right
      have ihsimp := @ih (e2u h3')
      have ihsimp := ihsimp.left

      simp only [use, Seq.seq, unpair_pair] at ihsimp ⊢
      simp [Part.Dom.bind (use_prec_dom_aux hh)] at ihsimp ⊢
      simp only [Part.Dom.bind (h5')] at ihsimp ⊢
      simp [stupidrewrite] at ihsimp ⊢
      simp [Part.Dom.bind (e2u h5')] at ihsimp ⊢
      simp [Part.Dom.bind (e2u h9)] at ihsimp ⊢

      aesop? says
        rename_i ihsimp_1
        simp_all only [and_self, implies_true, and_true]
        obtain ⟨left, right⟩ := ihsimp_1
        cases ihsimp with
        | inl h => simp_all only [true_or]
        | inr h_1 => simp_all only [true_or, or_true]


lemma httconv' {l'} (htt : ∃ l'', l'' ++ l' = tail) : ∃ l'', l'' ++ l' = head :: tail := by
  rcases htt with ⟨h1,h2⟩
  exact ⟨head::h1,Eq.symm (List.append_cancel_left (congrArg (HAppend.hAppend tail) (congrArg (List.cons head) (_root_.id (Eq.symm h2)))))⟩
lemma cm_aux_0
{l}
{head :ℕ}
(hhht : ∃ l'', l'' ++ l' = l)
(hht : head :: tail = l')
:
∃ l'':List ℕ, l'' ++ head :: tail = l
:= by
  grind
lemma cm_aux_1
{l}
{head :ℕ}
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

-- {l:List ℕ}
-- {h:(forIn l (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
{h:∀ (l') (base:ℕ) (htt:∃l'',l''++l'=l),  (forIn' (l') (base) fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l' (htt) h)))).Dom}
{h2:base1≤base2}
-- (hr:r≤ro)
:
((forIn' l base1 fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base1 (⟨[],rfl⟩))
≤
(forIn' l base2 fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base2 (⟨[],rfl⟩)))
∧
(base1 ≤ (forIn' l base2 fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l ⟨[],rfl⟩ h)))).get (h l base2 (⟨[],rfl⟩)))
:= by
  -- simp [forIn'_eq_forIn]
  induction l generalizing base1 base2 with
  | nil => simpa
  | cons head tail ih =>
    -- have : head :: tail = l := by exact?
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
    -- have aaaa (l'): (∃ l'', l'' ++ l' = head :: tail) →  (∃ l'', l'' ++ l' = tail) := by sorry
    -- have ih1 := @ih (base1.max addendum) (base2.max addendum) f ihmain ihmain2

    simp [show f head (head :: tail) ⟨[],rfl⟩ (List.mem_cons_self) = addendum from rfl]

    have aux (a:ℕ) (m:a∈tail): (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))) = (f a tail (httconv ⟨[],rfl⟩) m):= by
      refine hf a head tail m (head :: tail) ⟨[],rfl⟩ rfl
      -- refine
      -- grind
      -- grind
      -- have := hf a head tail m (?_)
      -- exact hf a head tail m rfl
      -- exact hf a head tail m
    have :
    (fun a m (b:ℕ) ↦ Part.some (ForInStep.yield (b.max (f a (head :: tail) ⟨[],rfl⟩ (List.mem_cons_of_mem head (List.forIn'_congr._proof_1 (Eq.refl tail) a m))))))
    =
    fun a m (b:ℕ) ↦ Part.some (ForInStep.yield (b.max (f a tail (httconv ⟨[],rfl⟩) m)))
    := by
      funext a m b
      simp [aux a m]

    simp [this]
    -- exact?
    -- simp [this]
    constructor
    have ihmain3 : base1 ≤ base2.max addendum  := by exact le_sup_of_le_left h2
    exact ih1.left
    have := ih1.right
    exact le_of_max_le_left this


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
theorem use_mono_rfind'
(hh:(use O (rfind' cf) x).Dom):
∀ hj:j ≤ rfind'_obtain (u2e hh),
  (use O cf (Nat.pair x.l (j+x.r))).get (use_rfind'_dom hh j hj) ≤ (use O (rfind' cf) x).get hh
  := by

  intro hjro
  have rop := rfind'_obtain_prop (u2e hh)
  let ro := rfind'_obtain (u2e hh)
  have rwro : rfind'_obtain (u2e hh) = ro := rfl
  simp [rwro] at rop hjro
  have rop1 := rop.left
  have rop2 := rop.right.left
  have rop3 := rop.right.right
  have rop4 := rfind'_obtain_prop_4 (u2e hh)
  simp [rwro] at rop4

  have aux3 := rop2 0 (zero_le ro)
  simp at aux3
  have aux5 := rop2 j hjro

  simp [use]
  simp [Part.Dom.bind (u2e hh)]
  -- simp [Part.Dom.bind (e2u aux3)]
  -- simp [Part.Dom.bind (aux3)]
  have rwro2 : (eval O (rfind' cf) x).get (u2e hh) - x.r = ro := rfl
  simp [rwro2]

  simp only [forIn_eq_forIn']

  -- simp (config := { singlePass := true }) [List.reverse]
  have domaux1 {i} (h : i ∈ (List.range (ro + 1)).reverse) : i≤ro := by
    grind
  have :
      (fun i h r ↦
      (use O cf (Nat.pair x.l (i + x.r))).bind fun use_i
      ↦ Part.some (ForInStep.yield (r.max use_i))
      : (i : ℕ) → i ∈ (List.range (ro + 1)).reverse → ℕ → Part (ForInStep ℕ))
    = (fun i h r ↦
        Part.some (ForInStep.yield (r.max
        -- ((use O cf (Nat.pair x.l (i + x.r))).get (e2u $ rop2 (ro-i) (sub_le ro i)))
        ((use O cf (Nat.pair x.l (i + x.r))).get (e2u $ rop2 i (domaux1 h)))
        ))

      : (i : ℕ) → i ∈ (List.range (ro + 1)).reverse → ℕ → Part (ForInStep ℕ)) := by
        funext i h r
        -- simp [Part.Dom.bind (e2u $ rop2 (ro-i) (sub_le ro i))]
        simp [Part.Dom.bind (e2u $ rop2 i (domaux1 h))]
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
  have : (use O cf x).Dom := by exact e2u aux3
  have domaux2 : (use O cf (Nat.pair x.l (ro + x.r))).Dom := e2u $ rop2 ro le_rfl
  have domaux3aux {a' k} (h0:k≤ro) (h:a' ∈ (List.range k).reverse) : a' ∈ (List.range ro).reverse  := by
    simp at h ⊢
    exact Nat.lt_of_lt_of_le h h0
    -- exact?
  have domaux3 (a' k m) (h0:k≤ro) := e2u (rop2 a' (domaux1 (List.forIn'_congr._proof_1 listrw a' (List.mem_cons_of_mem ro (domaux3aux h0 m)))))
  have forInDom {k :ℕ} (base:ℕ) (h:k≤ro):
  (forIn' (List.range k).reverse (base) fun a' m b ↦
        Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (a' + x.r))).get (domaux3 a' k m h))))).Dom := by
    induction k generalizing base with
    | zero =>
      simp
    | succ n ih =>
      simp [listrwgen, -forIn'_eq_forIn]
      have auxdom4 : (use O cf (Nat.pair x.l (n + x.r))).Dom := by
        aesop? says
          rename_i hjro_1 this_1
          simp_all [ro]
          apply domaux3
          on_goal 2 => simp_all only [ro]
          on_goal 2 => rfl
          simp_all only [List.mem_reverse, List.mem_range]
          exact h
      have := @ih (base.max ((use O cf (Nat.pair x.l (n + x.r))).get auxdom4)) (le_of_succ_le h)
      aesop? says
        simp_all only [implies_true, not_false_eq_true, and_self, and_true, List.mem_range'_1, and_imp, forIn'_eq_forIn,
        List.mem_reverse, List.mem_range, ro]

  have auxdom5:(use O cf (Nat.pair x.l (j + x.r))).Dom:= by (expose_names; exact use_rfind'_dom hh j hjro_1)
  have auxdom8 (k:ℕ):(use O cf (Nat.pair x.l (ro - k + x.r))).Dom:= use_rfind'_dom hh (ro-k) (sub_le ro k)
  have auxdom6:= forInDom ((use O cf (Nat.pair x.l (ro + x.r))).get domaux2) hjro
  have auxdom9 (k:ℕ):= forInDom ((use O cf (Nat.pair x.l (ro -k + x.r))).get (auxdom8 k)) (sub_le ro k)
  have auxdom7:= forInDom ((use O cf (Nat.pair x.l (ro + x.r))).get domaux2) le_rfl
  have auxdom10 :=forInDom ((use O cf (Nat.pair x.l (j + x.r))).get auxdom5) hjro
  have main2:
    -- (use O cf (Nat.pair x.l (j + x.r))).get auxdom5 ≤ (forIn' (List.range j).reverse ((use O cf (Nat.pair x.l (ro + x.r))).get domaux2) fun a' m b ↦ Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (a' + x.r))).get (domaux3 a' j m hjro))))).get auxdom6 := by
    (use O cf (Nat.pair x.l (j + x.r))).get auxdom5 ≤ (forIn' (List.range j).reverse ((use O cf (Nat.pair x.l (j + x.r))).get (auxdom5)) fun a' m b ↦ Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (a' + x.r))).get (domaux3 a' j m hjro))))).get auxdom10:= by
      -- wait this should be literally just an application of main1.
      let base := (use O cf (Nat.pair x.l (j + x.r))).get auxdom5
      simp [show (use O cf (Nat.pair x.l (j + x.r))).get auxdom5 = base from rfl]
      let f (a : ℕ) (l' : List ℕ) (h2:∃ l'':List ℕ, l'' ++ l' = (List.range j).reverse) (h3:a ∈ l')
            := (use O cf (Nat.pair x.l (a + x.r))).get (
              by
                rcases listrevlem h2 with ⟨h4,h5,h6⟩
                rw [h5] at h3
                exact domaux3 a h4 h3 (Nat.le_trans h6 hjro)
            )
      have bigaux : ∀ (l' : List ℕ) (base : ℕ) (htt : ∃ l'', l'' ++ l' = (List.range j).reverse),
      (forIn' l' base fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l' htt h)))).Dom := by
        intro l' base htt
        unfold f
        rcases listrevlem htt with ⟨h1,h2,h3⟩
        simp [h2]
        have : h1≤ro := by (expose_names; exact Nat.le_trans h3 hjro_1)
        exact forInDom base this
      have := (@clause_mono_2 base base (List.range j).reverse f (fun a head tail m l' hhht hht ↦ rfl) bigaux (le_rfl)).right

      apply this
  -- here we are saying, starting calculations from j, we'll get smaller results bc we're not taking into account the values j~ro.

  have main3 :
    ∀k,
    (forIn' (List.range (ro-k)).reverse ((use O cf (Nat.pair x.l ((ro-k) + x.r))).get (auxdom8 k)) fun a' m b ↦ Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (a' + x.r))).get (domaux3 a' (ro-k) m (sub_le ro k)))))).get (auxdom9 k)
    ≤
    (forIn' (List.range ro).reverse ((use O cf (Nat.pair x.l (ro + x.r))).get domaux2) fun a' m b ↦ Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (a' + x.r))).get (domaux3 a' ro m (le_rfl)))))).get auxdom7
    := by
      intro k
      induction k with
      | zero =>
        simp
      | succ n ih =>
        -- do cases on if ro-n≤0
        cases eq_zero_or_pos (ro - n) with
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
          #check listrwgen (ro-n-1)
          simp [listrwgen (ro-n-1)] at ih

          have domaux10 : (use O cf (Nat.pair x.l (ro - n - 1 + 1 + x.r))).Dom := by
            rw [←ronrw]
            exact auxdom8 n
          have domaux11 : (use O cf (Nat.pair x.l (ro - n - 1 + x.r))).Dom := by
            rw [←ronrw0]
            exact auxdom8 (n + 1)
          let base2 := (((use O cf (Nat.pair x.l (ro - n - 1 + 1 + x.r))).get domaux10).max
          ((use O cf (Nat.pair x.l (ro - n - 1 + x.r))).get domaux11))
          let base1 := (use O cf (Nat.pair x.l (ro - n - 1 + x.r))).get domaux11
          have base1_le_base2 : base1≤base2 := by
            exact Nat.le_max_right ((use O cf (Nat.pair x.l (ro - n - 1 + 1 + x.r))).get domaux10) base1
          -- #check clause_mono_1
          let f (a : ℕ) (l' : List ℕ) (h2:∃ l'':List ℕ, l'' ++ l' = (List.range (ro - n - 1)).reverse) (h3:a ∈ l')
            := (use O cf (Nat.pair x.l (a + x.r))).get (
              by
                exact domaux3 a (ro - (n + 1)) (List.forIn'_congr._proof_1 (congrArg (fun x ↦ (List.range x).reverse) ronrw0) a (by
                  simp; exact listrevlem2 h2 h3
                  )) (sub_le ro (n + 1))
            )

          let auxaxuaxuaxuaxa : ∀ (l' : List ℕ) (base : ℕ) (htt : ∃ l'', l'' ++ l' = (List.range (ro - n - 1)).reverse),
        (forIn' l' base fun a h b ↦ Part.some (ForInStep.yield (b.max (f a l' htt h)))).Dom := by
            intro l' base htt
            unfold f
            rcases listrevlem htt with ⟨h1,h2,h3⟩
            simp [h2]
            have : h1≤ro := by exact le_of_le_sub (le_of_le_sub h3)
            exact forInDom base this
          -- let f (a : ℕ) (l : List ℕ) (h:a ∈ l) :ℕ := use O cf (Nat.pair x.l (a + x.r))
          have mainclause := @clause_mono_2 base1 base2 (List.range (ro - n - 1)).reverse f (fun a head tail m l' hhht hht ↦ rfl) auxaxuaxuaxuaxa base1_le_base2
          exact Nat.le_trans mainclause.left ih




  have :=(main3 (ro-j))
  have aux92: ro-(ro-j)=j:= by (expose_names; exact Nat.sub_sub_self hjro_1)
  simp [aux92] at this
  apply le_trans main2 this


#check Option
theorem up_to_usen (hh:y∈(evaln O₁ s c x)) (hO: ∀ i≤(usen O₁ c s x).getD 0, O₁ i = O₂ i) : evaln O₁ s c x = evaln O₂ s c x := by
  sorry
-- Custom strong induction principle
def CodeNat.induction
  {motive : Code → ℕ → Prop}
  (hzero : ∀ x, motive .zero x)
  (hsucc : ∀ x, motive .succ x)
  (hleft : ∀ x, motive .left x)
  (hright : ∀ x, motive .right x)
  (horacle : ∀ x, motive .oracle x)
  (hpair : ∀ cf cg,
    (∀ x, motive cf x) →
    (∀ x, motive cg x) →
    ∀ x, motive (.pair cf cg) x)
  (hcomp : ∀ cf cg,
    (∀ x, motive cf x) →
    (∀ x, motive cg x) →
    ∀ x, motive (.comp cf cg) x)
  (hprec : ∀ cf cg,
    (∀ x, motive cf x) →
    (∀ x, motive cg x) →
    (∀ x, (∀ x' < x, motive (.prec cf cg) x') → motive (.prec cf cg) x))
  (hrfind' : ∀ cf,
    (∀ x, motive cf x) →
    (∀ x, (∀ x' < x, motive (.rfind' cf) x') → motive (.rfind' cf) x))
  : ∀ c x, motive c x := by
    intro c
    induction c with
    | zero => exact fun x => hzero x
    | succ => exact fun x => hsucc x
    | left => exact fun x => hleft x
    | right => exact fun x => hright x
    | oracle => exact fun x => horacle x
    | pair cf cg ihcf ihcg => exact fun x => hpair cf cg (ihcf) (ihcg) x
    | comp cf cg ihcf ihcg => exact fun x ↦ hcomp cf cg ihcf ihcg x
    | prec cf cg ihcf ihcg  =>
      intro x
      apply hprec cf cg ihcf ihcg x
      intro x' hlt
      apply @Nat.strongRecOn (fun n => motive (.prec cf cg) n) x' (fun n ih => ?_)
      exact hprec cf cg ihcf ihcg n ih
    | rfind' cf ihcf =>
      intro x
      apply hrfind' cf ihcf x
      intro x' hlt
      apply @Nat.strongRecOn (fun n => motive (.rfind' cf ) n) x' (fun n ih => ?_)
      exact hrfind' cf ihcf n ih

theorem up_to_use (hh:(eval O₁ c x).Dom) (hO: ∀ i≤(use O₁ c x).get (e2u hh), O₁ i = O₂ i) : eval O₁ c x = eval O₂ c x := by
  -- have h:x≤use O₁ c x
  -- induction x using Nat.strong_induction_on with
  -- | h x ih =>
  -- induction c×x with

    -- sorry
  induction c,x using CodeNat.induction with
  | hzero x => simp [eval]
  | hsucc x => simp [eval]
  | hleft x => simp [eval]
  | hright x => simp [eval]
  | horacle x =>
    have h1:x≤(use O₁ oracle x).get (e2u hh) := by simp [use]
    simp [eval]
    exact hO x h1
  | hpair cf cg hcf hcg x =>
    simp only [eval]
    have h1:
    (∀ i ≤ (use O₁ cf x).get (e2u (eval_pair_dom hh).left), O₁ i = O₂ i)
    :=by
      intro xx
      intro hxx
      have hxx2 := le_trans hxx (use_mono_pair (e2u hh)).left
      exact hO xx hxx2
    have h2:
    (∀ i ≤ (use O₁ cg x).get (e2u (eval_pair_dom hh).right), O₁ i = O₂ i)
    :=by
      intro xx
      intro hxx
      have hxx2 := le_trans hxx (use_mono_pair (e2u hh)).right
      exact hO xx hxx2
    rw [hcf x (eval_pair_dom hh).left h1]
    rw [hcg x (eval_pair_dom hh).right h2]
  | hcomp cf cg hcf hcg x =>
    simp only [eval]
    have h1:
    (∀ i ≤ (use O₁ cg x).get (e2u (eval_comp_dom hh).left), O₁ i = O₂ i)
    :=by
      intro xx
      intro hxx
      have hxx2 := le_trans hxx (use_mono_comp (e2u hh)).left
      exact hO xx hxx2
    have ih1 := hcg x (eval_comp_dom hh).left h1
    rw [ih1]

    have h2:
    (∀ i ≤ (use O₁ cf ((eval O₁ cg x).get (eval_comp_dom_aux hh))).get (e2u (eval_comp_dom hh).right), O₁ i = O₂ i)
    :=by
      intro xx
      intro hxx
      have hxx2 := le_trans hxx (use_mono_comp (e2u hh)).right

      exact hO xx hxx2

    have aux0 : (eval O₂ cg x).Dom := by
      have aux00 := eval_comp_dom_aux hh
      rwa [ih1] at aux00
    have aux1 : ((eval O₁ cg x).get (eval_comp_dom_aux hh)) = (eval O₂ cg x).get aux0 := by simp_all only [implies_true]
    have aux2 : (eval O₁ cf ((eval O₂ cg x).get aux0)).Dom := by
      have aux10 :=(eval_comp_dom hh).right
      rwa [aux1] at aux10
    have aux4 :(use O₁ cf ((eval O₁ cg x).get (eval_comp_dom_aux hh))).get (e2u (eval_comp_dom hh).right) = (use O₁ cf ((eval O₂ cg x).get aux0)).get (e2u aux2) := by
      simp_all only [implies_true]
    have h3:
    (∀ i ≤ (use O₁ cf ((eval O₂ cg x).get aux0)).get (e2u aux2), O₁ i = O₂ i)
    := by
      have aux := h2
      rwa [aux4] at aux

    have ih2 := hcf ((eval O₂ cg x).get aux0) aux2 h3

    simp
    [
      Part.bind_eq_bind,
      Part.bind,
      ih2,
    ]
  | hprec cf cg hcf hcg x ih =>
    rw [eval]
    rw [eval]
    -- simp only [prec_alt]
    -- rw [←eval]
    -- rw [←eval]
    rw [show x=Nat.pair x.l x.r from by simp] at hh ⊢ ih
    simp (config := { singlePass := true }) only [show x=Nat.pair x.l x.r from by simp] at hO

    cases hxr:x.r with
    | zero =>
      simp
      rw [hxr] at hh
      simp only [hxr] at hO
      have aux0 : (eval O₁ cf x.l).Dom := eval_prec_dom' hh
      have aux1 : (use O₁ cf x.l).Dom := e2u aux0
      have aux3 := use_mono_prec' (e2u hh)
      have aux2 : (∀ i ≤ (use O₁ cf x.l).get aux1, O₁ i = O₂ i) := by
        intro xx
        intro hxx
        have hxx2 := le_trans hxx (use_mono_prec' (e2u hh))
        exact hO xx hxx2
      simp [hcf x.l aux0 aux2]
    | succ xrM1 =>

      rw [hxr] at hh ih
      simp only [hxr] at hO
      simp
      have srw2 : (Nat.rec (eval O₂ cf x.l) (fun y IH ↦ IH.bind fun i ↦ eval O₂ cg (Nat.pair x.l (Nat.pair y i))) xrM1) = eval O₂ (prec cf cg) (Nat.pair x.l xrM1) := by
        rw (config:={occs:=.pos [1]}) [eval.eq_8]
        simp
      have srw1 : (Nat.rec (eval O₁ cf x.l) (fun y IH ↦ IH.bind fun i ↦ eval O₁ cg (Nat.pair x.l (Nat.pair y i))) xrM1) = eval O₁ (prec cf cg) (Nat.pair x.l xrM1) := by
        rw (config:={occs:=.pos [1]}) [eval.eq_8]
        simp
      rw [srw2]
      rw [srw1]

      have aux00 : (eval O₁ (cf.prec cg) (Nat.pair x.l xrM1)).Dom := by exact eval_prec_dom_aux hh

      -- have aux01 : (use O₁ (cf.prec cg) (Nat.pair x.l xrM1)).get (e2u aux00) ≤  := by sorry
      have aux02 : (∀ i ≤ (use O₁ (cf.prec cg) (Nat.pair x.l xrM1)).get (e2u aux00), O₁ i = O₂ i) := by
        intro xx
        intro hxx
        have hxx2 := le_trans hxx (use_mono_prec_1 (e2u hh))
        exact hO xx hxx2
      have aux03 := ih (Nat.pair x.l xrM1) (pair_lt_pair_right x.l (lt_add_one xrM1)) aux00 aux02
      have aux01 : (eval O₂ (cf.prec cg) (Nat.pair x.l xrM1)).Dom := by rwa [aux03] at aux00

      have aux11 := eval_prec_dom hh
      simp at aux11
      have aux10 := aux11.right
      have aux12 : (∀ i ≤ ((use O₁ cg (Nat.pair x.l (Nat.pair xrM1 ((eval O₁ (cf.prec cg) (Nat.pair x.l xrM1)).get (aux00)))))).get (e2u aux10), O₁ i = O₂ i) := by
        intro xx
        intro hxx
        have hxx2 := le_trans hxx (use_mono_prec (e2u hh)).right
        exact hO xx hxx2
      have aux13 := hcg (Nat.pair x.l (Nat.pair xrM1 ((eval O₁ (cf.prec cg) (Nat.pair x.l xrM1)).get (aux00)))) aux10 aux12

      rw [←aux03]

      have rw1 : ((eval O₁ (cf.prec cg) (Nat.pair x.l xrM1)).bind fun i ↦ eval O₁ cg (Nat.pair x.l (Nat.pair xrM1 i))) = eval O₁ cg (Nat.pair x.l (Nat.pair xrM1 ((eval O₁ (cf.prec cg) (Nat.pair x.l xrM1)).get (aux00)))) := by
        exact Part.Dom.bind aux00 fun i ↦ eval O₁ cg (Nat.pair x.l (Nat.pair xrM1 i))
      have rw2 : ((eval O₁ (cf.prec cg) (Nat.pair x.l xrM1)).bind fun i ↦ eval O₂ cg (Nat.pair x.l (Nat.pair xrM1 i))) = eval O₂ cg (Nat.pair x.l (Nat.pair xrM1 ((eval O₁ (cf.prec cg) (Nat.pair x.l xrM1)).get (aux00)))) := by
        exact Part.Dom.bind aux00 fun i ↦ eval O₂ cg (Nat.pair x.l (Nat.pair xrM1 i))
      rw [rw1, rw2]
      rw [aux13]
  | hrfind' cf  hcf x ih =>
    -- have hh2 := hh
    -- simp [eval] at hh2
    -- rcases hh2 with ⟨h1,h2,h3⟩
    have rop := rfind'_obtain_prop hh
    have rop1 := rop.left
    have rop1' := Part.eq_some_iff.mpr rop1
    have rop2 := rop.right.left
    have rop3 := rop.right.right
    let ro := rfind'_obtain hh
    have rwro : rfind'_obtain hh = ro := rfl
    simp [rwro] at rop rop1 rop2
    -- sorry
    -- have aux1 : (eval O₁ cf (Nat.pair x.l (ro + x.r))).Dom := by
    --   rw [rop1']
    --   exact trivial
    -- have aux2 : (∀ i ≤ (use O₁ cf (Nat.pair x.l (ro + x.r))).get (e2u aux1), O₁ i = O₂ i) := by
    --   intro xx
    --   intro hxx
    --   have := use_mono_rfind' (e2u hh) (show ro≤rfind'_obtain hh from by simp [ro])
    --   have hxx2 := le_trans hxx this
    --   exact hO xx hxx2
    -- have ih1 := hcf (Nat.pair x.l (ro + x.r)) aux1 aux2
    have ihAll : ∀ j ≤ ro, eval O₁ cf (Nat.pair x.l (j + x.r)) = eval O₂ cf (Nat.pair x.l (j + x.r)) := by
      intro j
      intro hjro
      have aux1 : (eval O₁ cf (Nat.pair x.l (j + x.r))).Dom := by
        exact rop2 j hjro
      have aux2 : (∀ i ≤ (use O₁ cf (Nat.pair x.l (j + x.r))).get (e2u aux1), O₁ i = O₂ i) := by
        intro xx
        intro hxx
        have := use_mono_rfind' (e2u hh) (show j≤rfind'_obtain hh from hjro)
        have hxx2 := le_trans hxx this
        exact hO xx hxx2
      exact hcf (Nat.pair x.l (j + x.r)) aux1 aux2


    -- rw [rop1'] at ih1
    have aux0 : (eval O₂ cf.rfind' x).Dom := by
      simp [eval]
      use ro
      constructor
      rw [←ihAll ro le_rfl]
      exact rop1
      intro j hjro
      have hjro : j≤ro := by exact le_of_succ_le hjro
      rw [←ihAll j hjro]
      exact rop2 j hjro

    suffices (eval O₁ cf.rfind' x).get hh ∈ eval O₂ cf.rfind' x from by
      have h0 : (eval O₂ cf.rfind' x).get aux0 ∈ eval O₂ cf.rfind' x := by exact Part.get_mem aux0
      have h2 := Part.mem_unique this h0
      rw [Part.dom_imp_some hh]
      rw [Part.dom_imp_some aux0]
      exact congrArg Part.some h2

    have geqlem := rfind'_geq_xr hh
    suffices (eval O₁ cf.rfind' x).get hh -x.r +x.r ∈ eval O₂ cf.rfind' x from by
      have h0 : (eval O₁ cf.rfind' x).get hh - x.r + x.r = (eval O₁ cf.rfind' x).get hh := by exact Nat.sub_add_cancel geqlem
      rwa [h0] at this

    have rwro2 : (eval O₁ cf.rfind' x).get hh - x.r = ro := rfl

    apply (rfind'_prop aux0).mpr
    rw [rwro2]
    constructor
    rw [←ihAll ro le_rfl]
    exact rop1
    -- simp [rwro]
    -- sorry
    constructor
    · intro j
      intro hjro
      rw [←ihAll j hjro]
      exact rop2 j hjro
    · intro j hjro
      rw [←ihAll j (le_of_succ_le hjro)]
      exact rop3 j hjro





/-
What does rfind' do?
rfind' cf (x,i) = the smallest (i+j) s.t. `[cf](x,i+j)=0`

So to calculate `rfind' cf x`, we will need to calculate
`[cf]` on all inputs from `x` to `(x.l, rfind' cf x)`

-/
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
