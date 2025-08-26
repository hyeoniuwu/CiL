import Computability.Constructions.CovRec

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset






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
  do
    let use_base ← use O cf x
    let eval_base ← eval O cf x
    if eval_base=0 then use_base else
    let use_indt ← use O cf (Nat.pair x.l (x.r+1))
    Nat.max use_base use_indt
    -- let asd ← (eval O c x);
    -- let (xl, xr) := Nat.unpair x
    -- (Nat.rfind fun n => (fun x => x = 0) <$> eval O cf (Nat.pair xl (n + xr))).map (· + xr)

-- /-- `usen; the use of [c:O]ₛ(x)` -/
-- def usen (O:ℕ→ℕ) (c:Code) (s:ℕ) (x:ℕ) : Option ℕ :=
-- match c,s with
-- | _,0              => Option.none
-- | zero      , s+1  => do guard (x≤s); return 0
-- | succ      , s+1  => do guard (x≤s); return 0
-- | left      , s+1  => do guard (x≤s); return 0
-- | right     , s+1  => do guard (x≤s); return 0
-- | oracle    , s+1  => do guard (x≤s); return x+1
-- | pair cf cg, s+1  =>
--   do
--     guard (x≤s);
--     let usen_cf ← usen O cf (s+1) x
--     let usen_cg ← usen O cg (s+1) x
--     return Nat.max usen_cf usen_cg
--     -- let asd ← evaln O s c x;
--     -- Nat.max <$> (use O cf x) <*> (use O cg x)
-- | comp cf cg, s+1  =>
--   do
--     guard (x≤s);
--     let usen_cg ← usen O cg (s+1) x
--     let evaln_cg ← evaln O (s+1) cg x
--     let usen_cf ← usen O cf (s+1) evaln_cg
--     return Nat.max usen_cf usen_cg
--     -- Nat.max <$> (use O cg x) <*> (eval O cg x >>= use O cf)
-- | prec cf cg, s+1 => do
--   guard (x≤s);
--   let (xl, i) := Nat.unpair x
--   (i.casesOn
--   (usen O cf (s+1) xl)
--   fun iM1 =>
--   do
--     let usen_prev  ← usen  O (prec cf cg) s (Nat.pair xl iM1)
--     let evaln_prev ← evaln O s (prec cf cg) (Nat.pair xl iM1)
--     let usen_indt  ← usen  O cg (s+1) (Nat.pair xl (Nat.pair iM1 evaln_prev))
--     return Nat.max usen_prev usen_indt)
-- | rfind' cf, s+1 =>
--   do
--     guard (x≤s);
--     let usen_base ← usen O cf (s+1) x
--     let evaln_base ← evaln O (s+1) cf x
--     let usen_indt ← usen O cf s (Nat.pair x.l (x.r+1))
--     if evaln_base=0 then usen_base else
--     Nat.max usen_base usen_indt
--       -- let asd ← (eval O c x);
--       -- let (xl, xr) := Nat.unpair x
--       -- (Nat.rfind fun n => (fun x => x = 0) <$> eval O cf (Nat.pair xl (n + xr))).map (· + xr)

--   -- if (eval O c x).Dom
--   -- then
--   -- else
--     -- Part.none



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
    simpa [Option.bind_eq_some] using Nat.lt_succ_of_le
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
    simp only [Option.mem_def, bind, Option.bind_eq_some, Option.guard_eq_some', exists_and_left,
      exists_const, and_imp]
    introv h h₁ h₂ h₃
    exact ⟨le_trans h₂ h, h₁ h₃⟩
  simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
  induction' c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n <;>
    rw [usen] at h ⊢;
    
    -- rw [usen] at h ⊢<;> refine this hl' (fun h => ?_) h
  iterate 5 exact this hl' (fun a ↦ a) h
  · -- pair cf cg
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h ⊢
    
    -- refine h.imp fun a => ?_
    refine h.imp fun a => And.imp (?_) <| ?_
    exact guard_imp hl'

    refine Exists.imp fun b => ?_
    rintro ⟨h1,h2,h3,h4⟩
    exact ⟨hf n b h1, h2, hg n h2 h3, h4⟩


    -- exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
  · -- comp cf cg
    simp only [bind, Option.pure_def, Option.bind_eq_some, Option.some.injEq] at h ⊢
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    refine ⟨h1,guard_imp hl' h2,
    h3,hg n h3 h4,
    h5,evaln_mono hl h6,
    h7,hf h5 h7 h8,
    h9⟩


  · -- prec cf cg    
    revert h
    simp only [unpaired, bind, Option.mem_def]
    induction n.unpair.2 <;> simp [Option.bind_eq_some]
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
    simp? [Bind.bind, Option.bind_eq_some] at h ⊢ says
      simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
        Option.bind_eq_some] at h ⊢

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
        Option.bind_eq_some] at h7 ⊢
      rcases h7 with ⟨h8,h9,h10⟩
      refine ⟨h8,usen_mono hl' h9, h10⟩
      

      
theorem usen_sound : ∀ {c s n x}, x ∈ usen O c s n → x ∈ use O c n
| _, 0, n, x, h => by simp [usen] at h
| c, k + 1, n, x, h => by
  induction' c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n
  -- <;>
      -- simp [use, usen, Option.bind_eq_some, Seq.seq] at h ⊢ <;>
    -- obtain ⟨_, h⟩ := h
  -- iterate 5 simpa [pure, PFun.pure, eq_comm] using h
  · simp [use, usen, Option.bind_eq_some, Seq.seq] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
    -- simpa [pure, PFun.pure, eq_comm] using h
  · simp [use, usen, Option.bind_eq_some, Seq.seq] at h ⊢
    obtain ⟨_, h⟩ := h
    exact (Part.get_eq_iff_mem trivial).mp h
  · sorry
  · sorry
  · sorry
  · -- pair cf cg
    simp [use, usen, Option.bind_eq_some, Seq.seq] at h ⊢
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
    simp [use, usen, Option.bind_eq_some, Seq.seq] at h ⊢
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
    simp [use, usen, Option.bind_eq_some, Seq.seq] at h ⊢
    -- obtain ⟨_, h⟩ := h
    revert h
    induction' n.r with m IH generalizing x
    -- <;> simp [Option.bind_eq_some]
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
      simp [Option.bind_eq_some] at hh
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
    simp [use, usen, Option.bind_eq_some, Seq.seq] at h ⊢
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
      simp [use, usen, pure, PFun.pure, Seq.seq, Option.bind_eq_some] at h ⊢
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
    -- induction' n₂ with m IH generalizing x n <;> simp [Option.bind_eq_some]
    induction' n₂ with m IH generalizing x n
    · 
      intro h
      -- simp [use] at h
      -- use n+1
      -- constructor
      -- exact le_add_right n 1
      -- simp at h
      -- simp [Option.bind_eq_some]
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

      
      
      sorry
      -- simp at hk₁
      constructor
      exact Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁
      sorry
      rcases IH hy with ⟨k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      refine
        ⟨(max k₁ k₂).succ,
          Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          usen_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
          usen_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [usen, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some,
        Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩

  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ usen O (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [usen, Option.bind_eq_some]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction' y with y IH generalizing m <;> simp [usen, Option.bind_eq_some]
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

theorem Part.dom_imp_ex_some {x:Part ℕ} (h:x.Dom) : ∃ y, x=Part.some y := by
  have h0 := Part.dom_iff_mem.mp h
  rcases h0 with ⟨y,hy⟩
  use y
  exact Part.eq_some_iff.mpr hy
theorem Part.dom_imp_some {x:Part ℕ} (h:x.Dom) : x=Part.some (x.get h) := by
  exact Part.get_eq_iff_eq_some.mp rfl


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
theorem auaua (h:x∨y∨z) : (x∨y)∨z := by exact or_assoc.mpr h

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
-- theorem eval_pair_dom (h:(eval O (pair cf cg) x).Dom) : (eval O cf x).Dom ∧ (eval O cg x).Dom := by
--   contrapose h
--   push_neg at h
--   simp [eval, Seq.seq]
--   by_cases hh:(eval O cf x).Dom
--   · exact fun a ↦ h hh
--   · simp [Part.eq_none_iff'.mpr hh]
  
theorem use_pair_dom (h:(use O (pair cf cg) x).Dom) : (use O cf x).Dom ∧ (use O cg x).Dom := by
  exact exists_prop.mp h
theorem use_comp_dom_aux (h:(use O (comp cf cg) x).Dom) : (eval O cg x).Dom := by
  simp [use] at h
  contrapose h
  simp [Seq.seq]
  exact fun a x_1 a ↦ h x_1
-- theorem use_comp_dom_aux_2 (h:(use O (comp cf cg) x).Dom) : (use O cg x).Dom := by
--   simp [use] at h
--   contrapose h
--   simp [Seq.seq]
--   exact fun a x_1 a_1 ↦ h a
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
  have aux1 : rf_result ≥ x.r := by
    unfold rf_result
    simp [eval]

  have aux2 : rfind'_obtain h = rf_result - x.r:= by exact rfl
  -- have aux3 : rf_result = m := by exact?
  have aux3 : rf_result ∈ eval O cf.rfind' x := by exact Part.get_mem h
  simp [eval] at aux3
  rcases aux3 with ⟨a,⟨⟨lll,rrr⟩,ha⟩⟩
  have aux4: rf_result - x.r = a := by exact (Nat.sub_eq_iff_eq_add aux1).mpr (_root_.id (Eq.symm ha))
  
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
    have h1 := Part.dom_imp_some ((use_pair_dom hh).left)
    simp only [use, Seq.seq, Part.bind]
    simp (config := { singlePass := true }) only [h1]
    simp [Part.assert]
theorem use_mono_comp (hh:(use O (comp cf cg) x).Dom):
  ((use O cg x).get ((use_comp_dom hh).left) ≤ (use O (comp cf cg) x).get hh)
  ∧
  ((use O cf ((eval O cg x).get (use_comp_dom_aux hh))).get ((use_comp_dom hh).right) ≤ (use O (comp cf cg) x).get hh)
  := by
    have h1 := Part.dom_imp_some ((use_comp_dom hh).left)
    have h2 := Part.dom_imp_some (use_comp_dom_aux hh)
    simp only [use, Seq.seq, Part.bind]
    simp (config := { singlePass := true }) only [h1]
    simp (config := { singlePass := true }) only [h2]
    simp only [Part.assert]
    simp [Part.bind]
    simp only [Part.assert]
    simp only [le_refl, or_true]

-- #check use_prec_dom'
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
      simp
      have h1 := Part.dom_imp_some ((use_prec_dom hh).left)
      have h2 := Part.dom_imp_some (use_prec_dom_aux hh)
      have := eval_prec_dom_aux (u2e hh)
      simp at this
      have h3 := Part.dom_imp_some this
      -- simp [use]
      simp only [use, Seq.seq, Part.bind]
      
      -- simp
      simp (config := { singlePass := true }) only [h1]
      simp (config := { singlePass := true }) only [h3]
      -- simp (config := { singlePass := true }) only [h2]
      simp only [Part.assert]
      simp [Part.bind]
      simp only [Part.assert]
      simp only [le_sup_left, le_sup_right, and_self]
    | succ n ih =>
      simp
      have h1 := Part.dom_imp_some ((use_prec_dom hh).left)
      have h2 := Part.dom_imp_some (use_prec_dom_aux hh)
      have h3' := eval_prec_dom_aux (u2e hh)
      simp at h3'
      have h3 := Part.dom_imp_some h3'
      have h5' := eval_prec_dom_aux h3'
      have h5 := Part.dom_imp_some h5'
      -- have h4' := (eval_prec_dom (u2e hh)).right
      have h4' := (eval_prec_dom h3').right
      simp at h4'
      have h4 := e2u h4'

      -- sorry
      -- simp [use]
      -- simp only [use]
      simp only [use, Seq.seq, Part.bind,unpair_pair]
      -- simp only [h3',h5']
      -- simp
      -- simp only []
      -- simp
      simp (config := { singlePass := true }) only [h2]
      simp (config := { singlePass := true }) only [h5]
      -- simp (config := { singlePass := true }) only [h1]
      -- simp (config := { singlePass := true }) only [h3]
      -- have : (use O (cf.prec cg) (Nat.pair x (n + 1))).Dom := by exact (e2u h3')
      -- have : (use O (cf.prec cg) (Nat.pair x (n + 1))).Dom := by exact?
      -- have ihsimp := ih (e2u h3')
      
      -- #check @ih (e2u h3') 
      -- have ihsimp := @ih (e2u h3') (e2u h3')
      have ihsimp := @ih (e2u h3')
      
      -- simp only [unpair]
      -- simp [ihsimp]
      -- stop
      simp only [Part.assert]
      simp [Part.bind]
      -- aesop
      simp only [Part.assert]
      -- simp only [Part.assert]
      -- #check le_sup_left
      simp
      -- apply Or.inr
      -- apply Or.inl
      have ihsimp := ihsimp.left
      simp only [use, Seq.seq, Part.bind] at ihsimp
      simp only [unpair_pair] at ihsimp
      simp (config := { singlePass := true }) only [h5] at ihsimp
      -- simp (config := { singlePass := true }) only [h1] at ihsimp
      -- simp (config := { singlePass := true }) only [h2] at ihsimp
      simp only [Part.assert] at ihsimp
      simp [Part.bind] at ihsimp
      -- aesop
      simp only [Part.assert] at ihsimp
      apply or_assoc.mp
      apply Or.inl
      
      -- have aux0 : (eval O (cf.prec cg) (Nat.pair x n)).Dom := by exact h5'
      let v2 := (use O cg (Nat.pair x (Nat.pair n ((eval O (cf.prec cg) (Nat.pair x n)).get ?_)))).get ?_
      exact le_sup_iff.mp ihsimp
      exact h5'
      exact h4
      
      
theorem use_mono_rfind'
(hh:(use O (rfind' cf) x).Dom):
∀ hj:j ≤ rfind'_obtain (u2e hh),
  (use O cf (Nat.pair x.l (j+x.r))).get (use_rfind'_dom hh j hj) ≤ (use O (rfind' cf) x).get hh
  := by
  -- induction s with
  -- simp
  -- [
  --   use,
  --   -- eval,
  --   Part.bind,
  --   Part.assert,
  -- ]
  intro hj
  have aux0 := (rfind'_obtain_prop (u2e hh)).right.left
  have aux1 := (rfind'_obtain_prop (u2e hh)).right.right
  have aux2 := (rfind'_obtain_prop (u2e hh)).left
  cases lt_or_eq_of_le hj with
  | inl hhh =>
    have aux3 := aux0 0 (zero_le (rfind'_obtain (u2e hh)))
    simp at aux3
    have aux4 := aux1 0 (zero_lt_of_lt hhh)
    have aux5 := aux0 j hj
    have aux6 := aux1 j hhh
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
  | inr h => sorry
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
    sorry
  
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
