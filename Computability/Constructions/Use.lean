import Computability.Constructions.CovRec

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset






open Nat.RecursiveIn.Code
namespace Nat.RecursiveIn.Code


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
lemma rfind'_geq_xr (h:(eval O (rfind' cf) x).Dom) : (eval O cf.rfind' x).get h ≥ x.r := by simp [eval]
def rfind'_obtain (h:(eval O (rfind' cf) x).Dom) : ℕ := ((eval O (rfind' cf) x).get h)-x.r
theorem rfind'_obtain_prop
(h:(eval O (rfind' cf) x).Dom) :
0∈(eval O cf (Nat.pair x.l (rfind'_obtain h+x.r)))
∧ (∀ j ≤ rfind'_obtain h, (eval O cf (Nat.pair x.l (j+x.r))).Dom)
∧ (∀ j < rfind'_obtain h, ¬0∈(eval O cf (Nat.pair x.l (j+x.r))))
:= by
-- 0 ∈ eval O cf (Nat.pair x.l ((rfind'_obtain h) + x.r)) ∧ ∀ {m : ℕ}, m < (rfind'_obtain h) → (eval O cf (Nat.pair x.l (m + x.r))).Dom := by
  -- have h0 : ∃ m, m ∈ eval O (rfind' cf) x := by exact Part.dom_iff_mem.mp h
  -- simp [eval] at h
  -- simp [eval] at h0
  -- rcases h0 with ⟨m,a,⟨⟨hmal,asd⟩, hmar⟩⟩
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
    simp_all only [ge_iff_le, Nat.sub_add_cancel, rf_result]
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
    have := rfind'_geq_xr h
    have aux0 : (eval O cf.rfind' x).get h = y+x.r := by exact Part.get_eq_of_mem h1 h
    simp_all only [ge_iff_le, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right]
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
  do
    -- let ro := rfind'_obtain h

    let guard ← eval O (rfind' cf) x;
    let ro := guard - x.r
    -- eval O (rfind' cf) x;
    -- guard ((eval O (rfind' cf) x).Dom);

    -- let use_base ← use O cf x
    -- let eval_base ← eval O cf x
    -- if eval_base = 0 then use_base else

    -- let use_indt ← use O cf (Nat.pair x.l (x.r+1)) -- this is wrong :(
    -- let use_indt ← use O (rfind' cf) (Nat.pair x.l (x.r+1)) -- this is right but you have to show termination...

    let mut max := 0
    -- #check Std.Range|
    -- let l := List.reverse (List.range (ro+1))
    -- for i in List.reverse [0:ro+1] do
    for i in List.reverse (List.range (ro+1)) do
    -- for i in [ro+1:0:-1] do

      -- let use_i ← (use O cf (Nat.pair x.l ((ro-i)+x.r)))
      let use_i ← (use O cf (Nat.pair x.l (i+x.r)))
      -- let use_i := (use O cf (Nat.pair x.l ((ro-i)+x.r))).get this
      -- let use_i := (use O cf (Nat.pair x.l (i+x.r))).get this
      max := Nat.max max use_i
    max


/-- `usen; the use of [c:O]ₛ(x)` -/
def usen (O:ℕ→ℕ) (c:Code) (s:ℕ) : ℕ→ Option ℕ :=
match c,s with
| _,0              => fun x=> Option.none
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
    -- let asd ← evaln O s c x;
    -- Nat.max <$> (use O cf x) <*> (use O cg x)
| comp cf cg, s+1  => fun x=>
  do
    guard (x≤s);
    let usen_cg ← usen O cg (s+1) x
    let evaln_cg ← evaln O (s+1) cg x
    let usen_cf ← usen O cf (s+1) evaln_cg
    return Nat.max usen_cf usen_cg
    -- Nat.max <$> (use O cg x) <*> (eval O cg x >>= use O cf)
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
      -- let asd ← (eval O c x);
      -- let (xl, xr) := Nat.unpair x
      -- (Nat.rfind fun n => (fun x => x = 0) <$> eval O cf (Nat.pair xl (n + xr))).map (· + xr)

  -- if (eval O c x).Dom
  -- then
  -- else
    -- Part.none




theorem test (h:∀ (a : ℕ), ¬x = some a) : x=Option.none := by exact Option.eq_none_iff_forall_ne_some.mpr h
-- #check Nat.le_induction
-- #check induct

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
        have := hh a2 ha2 a ha

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
    simp only [unpaired, bind, Option.mem_def]
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
      simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
        Option.bind_eq_some_iff] at h ⊢

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
      simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
        Option.bind_eq_some_iff] at h7 ⊢
      rcases h7 with ⟨h8,h9,h10⟩
      refine ⟨h8,usen_mono hl' h9, h10⟩

theorem usen_sound : ∀ {c s n x}, x ∈ usen O c s n → x ∈ use O c n
| _, 0, n, x, h => by simp [usen] at h
| c, k + 1, n, x, h => by
  induction' c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n
  -- <;>
      -- simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
    -- obtain ⟨_, h⟩ := h
  -- iterate 5 simpa [pure, PFun.pure, eq_comm] using h
  · simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
    -- simpa [pure, PFun.pure, eq_comm] using h
  · simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
  · sorry
  · sorry
  · sorry
  · -- pair cf cg
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
    -- exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
  · --comp hf hg
    simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢
    -- obtain ⟨_, h⟩ := h
    -- rcases h with ⟨y, eg, ef⟩
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨h2,hg n h2 h3,
            h4,evaln_sound h5,
            h6,hf h4 h6 h7,
            ?_⟩
    subst h8
    exact Nat.max_comm h2 h6

  · -- prec cf cg
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
          have main := usen_sound h3
          simp [use] at main
          exact main
        · use h7
          constructor
          · exact hg (Nat.pair n.l (Nat.pair m h4)) h7 h8
          · exact h9

  · -- rfind' cf
    simp [use, usen, Option.bind_eq_some_iff, Seq.seq] at h ⊢
    obtain ⟨_, h⟩ := h


    rcases h with ⟨m, h₁, h₂⟩
    by_cases m0 : m = 0 <;> simp [m0] at h₂
    · exact
        ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
    · have := usen_sound h₂
      simp [eval] at this
      rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
      refine
        ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
          simp [add_comm, add_left_comm]⟩
      rcases i with - | i
      · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
      · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
        exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩
lemma evaln_sing (h1:a∈(evaln O s1 c x)) (h2:b∈(evaln O s2 c x)): a=b := by
  cases Classical.em (s1≤s2) with
  | inl h =>
    have := evaln_mono h h1
    simp_all only [Option.mem_def, Option.some.injEq]
  | inr h =>
    have := evaln_mono (Nat.le_of_not_ge h) h2
    simp_all only [Option.mem_def, Option.some.injEq]
theorem usen_complete {c n x} : x ∈ use O c n ↔ ∃ s, x ∈ usen O c s n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => usen_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ usen O  c (k + 1) n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [use, usen, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    -- constructor

    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
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
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ usen O (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [usen, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction' y with y IH generalizing m <;> simp [usen, Option.bind_eq_some_iff]
    · simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
      exact ⟨_, Nat.le_of_lt_succ <| usen_bound hk, _, hk, by simp⟩
    · rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| usen_bound hk₁
      use a
      use usen_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        usen_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩
theorem use_eq_rfindOpt (c n) : use O c n = Nat.rfindOpt fun s => usen O c s n :=
  Part.ext fun x => by
    refine usen_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply usen_mono hl

-- theorem Part.dom_imp_ex_some {x:Part ℕ} (h:x.Dom) : ∃ y, x=Part.some y := by
--   have h0 := Part.dom_iff_mem.mp h
--   rcases h0 with ⟨y,hy⟩
--   use y
--   exact Part.eq_some_iff.mpr hy
-- theorem Part.dom_imp_some {x:Part ℕ} (h:x.Dom) : x=Part.some (x.get h) := by
--   exact Part.get_eq_iff_eq_some.mp rfl


theorem use_dom_iff_eval_dom : (use O c x).Dom ↔ (eval O c x).Dom := by
  induction c generalizing x with
  | zero => exact Eq.to_iff rfl
  | succ => exact Eq.to_iff rfl
  | left => exact Eq.to_iff rfl
  | right => exact Eq.to_iff rfl
  | oracle => exact Eq.to_iff rfl
  | pair cf cg hcf hcg =>
    simp [use,eval]
    simp [Seq.seq]
    simp_all only []
  | comp cf cg hcf hcg =>
    simp [use,eval]
    simp [Seq.seq]
    simp_all only [and_exists_self]
  | prec cf cg hcf hcg =>
    sorry
  | rfind' _ _ => sorry

  sorry

#check use_dom_iff_eval_dom.mpr
abbrev e2u : (eval O c x).Dom → (use O c x).Dom := use_dom_iff_eval_dom.mpr
abbrev u2e : (use O c x).Dom → (eval O c x).Dom := use_dom_iff_eval_dom.mp



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


#check forIn
open List in
@[simp, grind =] theorem forIn'_cons [Monad m] {a : α} {as : List α}
    (f : (a' : α) → a' ∈ a :: as → β → m (ForInStep β)) (b : β) :
    forIn' (a::as) b f = f a mem_cons_self b >>=
      fun | ForInStep.done b => pure b | ForInStep.yield b => forIn' as b fun a' m b => f a' (mem_cons_of_mem a m) b := by
  simp only [forIn', List.forIn', forIn'.loop]
  congr 1
  funext s
  obtain b | b := s
  · rfl
  · apply forIn'_loop_congr
    intros
    rfl
open List in
@[simp] theorem forIn'_append [Monad m] {a : α} {as : List α}
    (f : (a' : α) → a' ∈ as++[a] → β → m (ForInStep β))
    (g : (a' : α) → a' ∈ as → β → m (ForInStep β))
    -- (hfg:)
    (b : β) :
    forIn' (as++[a]) b f
    =
    (forIn' (as) b g) >>=
      fun asd => f a (sorry) asd
      >>=
      fun
      | ForInStep.done b => pure b
      | ForInStep.yield b => pure b
      -- fun asd => f a (sorry) asd
    -- f a (False.elim mem_cons_of_mem) b >>=
    --   fun | ForInStep.done b => pure b | ForInStep.yield b => forIn' as b fun a' m b => f a' (mem_cons_of_mem a m) b
      := by
  induction as with
  | nil =>
    simp
    congr 1
    ·
    sorry
  | cons head tail ih =>
    simp
    sorry
  simp only [forIn', List.forIn', forIn'.loop]
  congr 1
  funext s
  obtain b | b := s
  · rfl
  · apply forIn'_loop_congr
    intros
    rfl
#check Finset
theorem clause_mono_1 {base1 base2 : ℕ} {f:ℕ→ℕ} {l:List ℕ}
-- {l:List ℕ}
-- {h:(forIn l (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
{h:∀ (l') (base:ℕ), (∃l'',l''++l'=l) → (forIn (l') (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
{h2:base1≤base2}
-- (hr:r≤ro)
:
(forIn l base1 fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).get (h l base1 (⟨[],rfl⟩))
≤
(forIn l base2 fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).get (h l base2 (⟨[],rfl⟩))
:= by
  induction l generalizing base1 base2 with
  | nil => simpa
  | cons head tail ih =>
    -- have : head :: tail = l := by exact?
    simp
    have ihmain :
    ∀ (l' : List ℕ) (base : ℕ),
      (∃ l'', l'' ++ l' = tail) → (forIn l' base fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom
      := by
      intro l' base h1
      rcases h1 with ⟨l'',hl''⟩
      have : (head::l'') ++ l' = head :: tail := by simp [hl'']
      exact h l' base  ⟨(head::l''),this⟩
    have ihmain2 : base1.max (f head) ≤ base2.max (f head) := by exact sup_le_sup_right h2 (f head)
    have := @ih (base1.max (f head)) (base2.max (f head)) ihmain ihmain2
    exact this

    -- #check @ih sorry
-- theorem clause_mono {base2:ℕ} {f:ℕ→ℕ} {r}
-- -- {l:List ℕ}
-- -- {h:(forIn l (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
-- {h:∀ r (base:ℕ), r≤ro → (forIn (((List.range r).reverse)) (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
-- {h2:base1≤base2}
-- (hr:r≤ro)
-- :
-- (forIn (((List.range r).reverse)) base1 fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).get (h r base1 hr)
-- ≤
-- (forIn (((List.range r).reverse)) base2 fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).get (h r base2 hr)
-- := by
--   induction l with
--   | nil => simpa
--   | cons head tail ih =>
--     simp
--     sorry
--   sorry


theorem clause_mono {base:ℕ} {f:ℕ→ℕ} {ro:ℕ}
-- {l:List ℕ}
-- {h:(forIn l (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
{h:∀r≤(ro+1), (forIn ((List.range r).reverse) (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
-- {h2:∀l1 l2 (base':ℕ),l1::l2=l→(forIn l2 (base') fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom}
:
  base ≤ (forIn l (base) fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).get h
  :=
  by
    -- induction l generalizing base with
    induction l generalizing base with
    | nil =>
      simp
    | cons head tail ih =>
      simp
      #check h2 head tail (base.max (f head)) rfl
      have := h2 head tail (base.max (f head)) rfl
      -- have doms : (forIn tail base fun a b ↦ Part.some (ForInStep.yield (b.max (f a)))).Dom := sorry
      have := @ih (base.max (f head)) (this)
      grind only [= List.forIn_cons, = Nat.max_def, cases Or]
      simp_all only [implies_true, ge_iff_le]

      sorry
      sorry

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

  have listrwgen (n): (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
    simp
    exact List.range_succ
  have listrw : (List.range (ro + 1)).reverse = ro :: (List.range ro).reverse := by
    simp
    exact List.range_succ
  simp [listrw]
  -- have : (List.range' 0 (ro + 1)) = (List.range' 0 (ro + 1))
  -- (List.range' k (ro + 1 - k))
  have basecase :
  (use O cf (Nat.pair x.l (j + x.r))).get (sorry) ≤
  (forIn' (List.range' j (ro + 1 - j)) 0 fun i h r ↦
        Part.some (ForInStep.yield (r.max ((use O cf (Nat.pair x.l (ro - i + x.r))).get (sorry))))).get
    (sorry)
    := by
    have : List.range' 0 (ro + 1) = 0 :: List.range' 1 (ro) := by
      simp_all [ro]
      rfl
    have : List.range' j (ro + 1 - j) = j :: List.range' (j+1) (ro-j) := by
      have : ro + 1 - j = ro-j+1 := by (expose_names; exact Nat.sub_add_comm hjro_1)
      rw [this]
      rfl
    simp [this]

    sorry

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
  have main2:
    (use O cf (Nat.pair x.l (j + x.r))).get auxdom5 ≤ (forIn' (List.range j).reverse ((use O cf (Nat.pair x.l (ro + x.r))).get domaux2) fun a' m b ↦ Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (a' + x.r))).get (domaux3 a' j m hjro))))).get auxdom6 := by
      -- wait this should be literally just an application of main1.
      sorry
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

          have main_aux : ∀ (l' : List ℕ) (base : ℕ),
      (∃ l'', l'' ++ l' = (List.range (ro - n - 1)).reverse) → (forIn l' base fun a b ↦ Part.some (ForInStep.yield (b.max ((fun a => ((use O cf (Nat.pair x.l (a + x.r))).get (⋯))) a)))).Dom := by sorry
          #check clause_mono_1

          sorry

        simp [ih]
        sorry
      sorry

  #check le_trans main2 main3
  apply le_trans main2 main3



-- (forIn' (List.range ro).reverse ((use O cf x).get (e2u aux3)) fun a h b ↦ Part.some (ForInStep.yield (b.max ((use O cf (Nat.pair x.l (ro - a + x.r))).get (by

--   done))))).Dom := by sorry


  induction j with
  | zero =>
    simp
    sorry
  | succ n ih =>
    simp
    sorry
  -- generalize ro=a at *
  -- revert ro
  -- generalize (eval O (rfind' cf) x).get (u2e hh) - x.r = ro2
  -- generalize x = ro2

  -- induction hro:ro generalizing j with
  cases hro:ro
  -- generalizing
  --   rwro
  --   rwro2
  --   rop
  --   hjro
  --   rop1
  --   rop2
  --   rop3
  --   rop4
  with
  | zero =>
    simp [hro] at hjro rop1
    simp only [hjro, zero_add, pair_lr]
    have : (eval O cf x).get aux3 = 0 := by exact Eq.symm ((fun {α} {o} {a} h ↦ (Part.eq_get_iff_mem h).mpr) aux3 rop1)
    simp [this]
  | succ n =>
    have aux4 := rop3 0 (Nat.lt_of_sub_eq_succ hro)

    -- simp [use]
    -- simp [Part.Dom.bind (u2e hh)]
    -- simp [Part.Dom.bind (e2u aux3)]
    -- simp [Part.Dom.bind (aux3)]
    have := rop3 0 (Nat.lt_of_sub_eq_succ hro)
    simp at this
    have : ¬ (eval O cf x).get aux3 = 0 := by
      contrapose this
      simp at this ⊢
      exact (Part.get_eq_iff_mem aux3).mp this
    simp [this] at ⊢
    have rwro2 : (eval O (rfind' cf) x).get (u2e hh) - x.r = ro := rfl
    simp [rwro2] at ⊢


    simp
    sorry

    -- have redundant : ro ≤ rfind'_obtain (u2e hh) := Nat.le_refl ro
    -- have ih1 := ih redundant (redundant) (rop2 ro le_rfl)
    -- -- simp [rwro] at ih1
    -- #check ih (le_rfl) (le_rfl)



    -- induction ro generalizing * with
    -- | zero => sorry
    -- | succ n _ => sorry

    cases lt_or_eq_of_le hjro with
    | inl hjro2 => sorry
    | inr hjro2 =>
      simp [hjro2]



      have : List.range' 0 (ro + 1) = 0 :: List.range' 1 (ro) := by
        aesop
      -- rw [this]
      simp [this]
      #check List.forIn_cons
      -- #check bind_assoc
      -- simp [←bind_assoc]

      simp [Part.Dom.bind (e2u $ rop2 ro le_rfl)]
      simp only [forIn_eq_forIn']

      have :
        (fun i h r ↦
        (use O cf (Nat.pair x.l (ro - i + x.r))).bind fun use_i
        ↦ Part.some (ForInStep.yield (r.max use_i))
        : (i : ℕ) → i ∈ List.range' 1 ro → ℕ → Part (ForInStep ℕ))
      = (fun i h r ↦
          Part.some (ForInStep.yield (r.max
          ((use O cf (Nat.pair x.l (ro - i + x.r))).get (e2u $ rop2 (ro-i) (sub_le ro i)))
          ))

        : (i : ℕ) → i ∈ List.range' 1 ro → ℕ → Part (ForInStep ℕ)) := by
          funext i h r
          simp [Part.Dom.bind (e2u $ rop2 (ro-i) (sub_le ro i))]
      simp [this]
      simp [hro]
      have : List.range' 1 (n + 1) = 1 :: List.range' 2 n := by
        aesop
      simp [this]
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have : List.range' 2 (n + 1) = 2 :: List.range' 3 n := by
          aesop
        simp [this]


      #check forIn
      #check rop2 ro le_rfl
      -- have : (eval O cf (Nat.pair x.l (ro + x.r))).Dom := by exact?


      -- rw (config:={occs:=.pos [1]}) [rwro2]
      -- #check forM_loop_eq_forM_range'
      have : List.range' 0 (ro + 1) = List.range (ro) ++ [ro] := by
        sorry
      simp [this]



    -- have aux6 := rop3 j
    -- simp [hro] at hjro rop1

    have main1 : (use O cf (Nat.pair x.l (j + x.r))).get (use_rfind'_dom hh j hjro) ≤ (use O cf.rfind' (Nat.pair x.l (j + x.r))).get (e2u $ rop4 j hjro) := by
      simp [use]
      simp [Part.bind, Part.assert]
      have basecasefail := rop3 j
      sorry

    simp only
    [
      use,
    ]

    -- simp only [hjro, zero_add, pair_lr]
    simp []
    -- simp only []
    simp [Part.bind, Part.assert]
    have := rop3 0 (Nat.lt_of_sub_eq_succ hro)
    simp at this
    have : ¬ (eval O cf x).get aux3 = 0 := by
      contrapose this
      simp at this ⊢
      exact (Part.get_eq_iff_mem aux3).mp this
    simp [this]
    -- #check rop3 0 (Nat.lt_of_sub_eq_succ hro)
    have rwro2 : (eval O (rfind' cf) x).get (u2e hh) - x.r = ro := rfl

    simp [rwro2]

    -- aesop
    -- unfold forIn
    -- simp only [Part.bind, Part.assert]
    -- simp [aux3]

    simp only [Part.bind]
    -- simp only [Part.coe_some, Part.bind_eq_bind, ge_iff_le]
    -- simp (config := { singlePass := true }) only [Part.dom_imp_some aux3]
    -- simp (config := { singlePass := true }) only [Part.dom_imp_some (u2e hh)]
    simp only [Part.assert]
    -- aesop? says
    --   subst hj
    --   simp_all [ro]
    --   split
    --   next h => simp_all only [le_refl]
    --   next h => simp_all only [le_sup_left]

  sorry
  cases lt_or_eq_of_le hj with
  | inl hhh =>
    have aux3 := rop2 0 (zero_le (rfind'_obtain (u2e hh)))
    simp at aux3
    have aux4 := rop3 0 (zero_lt_of_lt hhh)
    have aux5 := rop2 j hj
    have aux6 := rop3 j hhh
    simp only
    [
      use,
      -- Part.bind,
      -- Part.assert,
      -- Part.dom_imp_some aux3,
      -- aux4,
      -- aux5,
      -- aux6,
    ]
    #check Part.dom_imp_some aux3
    simp (config := { singlePass := true }) only [Part.dom_imp_some aux3]
    by_cases hhhh:((eval O cf x).get aux3=0)
    · simp only [hhhh]

    · simp only [hhhh]
    rw [Part.dom_imp_some aux3]
    simp [hhh]
  | inr h =>

    sorry
  -- cases (lt_or_eq_of_le hj)

  -- simp [aux0,aux1,aux2]
  -- induction j with
  -- | zero =>
  --   simp
  --   have aux0 := (rfind'_obtain_prop (u2e hh)).right.left
  --   have aux1 := (rfind'_obtain_prop (u2e hh)).right.right
  --   have aux2 := (rfind'_obtain_prop (u2e hh)).left
  --   -- simp [aux0,aux1,aux2]
  --   have h1 := Part.dom_imp_some ((use_comp_dom hh).left)
  -- | succ n _ => sorry
  -- sorry

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
