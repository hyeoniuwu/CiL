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
  do
    let use_base ← use O cf x
    let eval_base ← eval O cf x
    if eval_base=0 then use_base else
    let use_indt ← use O cf (Nat.pair x.l (x.r+1))
    Nat.max use_base use_indt
    -- let asd ← (eval O c x);
    -- let (xl, xr) := Nat.unpair x
    -- (Nat.rfind fun n => (fun x => x = 0) <$> eval O cf (Nat.pair xl (n + xr))).map (· + xr)

/-- `usen; the use of [c:O]ₛ(x)` -/
def usen (O:ℕ→ℕ) (c:Code) (s:ℕ) (x:ℕ) : Option ℕ :=
match c,s with
| _,0              => Option.none
| zero      , s+1  => do guard (x≤s); return 0
| succ      , s+1  => do guard (x≤s); return 0
| left      , s+1  => do guard (x≤s); return 0
| right     , s+1  => do guard (x≤s); return 0
| oracle    , s+1  => do guard (x≤s); return x+1
| pair cf cg, s+1  =>
  do
    let usen_cf ← usen O cf (s+1) x
    let usen_cg ← usen O cg (s+1) x
    return Nat.max usen_cf usen_cg
    -- let asd ← evaln O s c x;
    -- Nat.max <$> (use O cf x) <*> (use O cg x)
| comp cf cg, s+1  =>
  do
    let usen_cg ← usen O cg (s+1) x
    let evaln_cg ← evaln O (s+1) cg x
    let usen_cf ← usen O cf (s+1) evaln_cg
    return Nat.max usen_cf usen_cg
    -- Nat.max <$> (use O cg x) <*> (eval O cg x >>= use O cf)
| prec cf cg, s+1 =>
  
  let (xl, i) := Nat.unpair x
  i.casesOn
  (usen O cf (s+1) xl)
  fun iM1 =>
  do
    let usen_prev  ← usen  O (prec cf cg) s (Nat.pair xl iM1)
    let evaln_prev ← evaln O s (prec cf cg) (Nat.pair xl iM1)
    let usen_indt  ← usen  O cg (s+1) (Nat.pair xl (Nat.pair iM1 evaln_prev))
    return Nat.max usen_prev usen_indt
| rfind' cf, s+1 =>
  do
    let usen_base ← usen O cf (s+1) x
    let evaln_base ← evaln O (s+1) cf x
    let usen_indt ← usen O cf s (Nat.pair x.l (x.r+1))
    if evaln_base=0 then usen_base else
    Nat.max usen_base usen_indt
      -- let asd ← (eval O c x);
      -- let (xl, xr) := Nat.unpair x
      -- (Nat.rfind fun n => (fun x => x = 0) <$> eval O cf (Nat.pair xl (n + xr))).map (· + xr)

  -- if (eval O c x).Dom
  -- then
  -- else
    -- Part.none
-- actually, maybe we dont have to define it like the above.
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
    exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
  · -- comp cf cg
    simp only [bind, Option.pure_def, Option.bind_eq_some, Option.some.injEq] at h ⊢
    -- have loc := evaln_mono
    -- simp? [Bind.bind, Option.bind_eq_some] at h ⊢ says
    --   simp only [bind, Option.mem_def, Option.bind_eq_some] at h ⊢
    -- apply h.imp fun a => And.imp (hg _ _)
    -- exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    -- exact h.imp fun a => And.imp (hg _ _) (evaln_mono hl _ _)
    -- #check h.imp
    rcases h with ⟨a,⟨ha1,⟨b,⟨hb1,⟨hb2,⟨hb3,hb4⟩⟩⟩⟩⟩⟩
    use a
    constructor
    exact hg n a ha1
    use b
    constructor
    exact evaln_mono hl hb1
    use hb2
    constructor
    exact hf b hb2 hb3
    exact hb4
-- TODO: golf proof above?

    
  · -- prec cf cg
    revert h
    simp only [unpaired, bind, Option.mem_def]
    induction n.unpair.2 <;> simp [Option.bind_eq_some]
    · apply hf
    · 
      expose_names
      intro x1
      intro hx1
      intro x2
      intro hx2
      intro x3
      intro hx3
      intro hmax
      use x1
      constructor
      · 
        sorry
      · use x2
        constructor
        · 
          sorry
        · use x3
          sorry
        sorry
      
      
      exact fun y h₁ h₂ => ⟨y, usen_mono hl' h₁, hg _ _ h₂⟩
  · -- rfind' cf
    simp? [Bind.bind, Option.bind_eq_some] at h ⊢ says
      simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
        Option.bind_eq_some] at h ⊢
    refine h.imp fun x => And.imp (hf _ _) ?_
    by_cases x0 : x = 0 <;> simp [x0]
    sorry
    exact usen_mono hl'
theorem usen_sound : ∀ {c s n x}, x ∈ usen O c s n → x ∈ use O c n := by sorry
theorem usen_complete {c n x} : x ∈ use O c n ↔ ∃ s, x ∈ usen O c s n := by sorry
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
  | prec cf cg hcf hcg => sorry
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
  aesop

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


-- #check Partrec.rfind'_dom
theorem up_to_use (hh:(eval O₁ c x).Dom) (hO: ∀ i≤(use O₁ c x).get (e2u hh), O₁ i = O₂ i) : eval O₁ c x = eval O₂ c x := by
  -- have h:x≤use O₁ c x
  induction c generalizing x with
  | zero => simp [eval]
  | succ => simp [eval]
  | left => simp [eval]
  | right => simp [eval]
  | oracle =>
    have h1:x≤(use O₁ oracle x).get (e2u hh) := by simp [use]
    simp [eval]
    exact hO x h1
  | pair cf cg hcf hcg =>
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
    rw [hcf (eval_pair_dom hh).left h1]
    rw [hcg (eval_pair_dom hh).right h2]
  | comp cf cg hcf hcg =>
    simp only [eval]
    have h1:
    (∀ i ≤ (use O₁ cg x).get (e2u (eval_comp_dom hh).left), O₁ i = O₂ i)
    :=by
      intro xx
      intro hxx
      have hxx2 := le_trans hxx (use_mono_comp (e2u hh)).left
      exact hO xx hxx2
    have ih1 := hcg (eval_comp_dom hh).left h1
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

    have ih2 := hcf aux2 h3
    
    simp
    [
      Part.bind_eq_bind,
      Part.bind,
      ih2,
    ]
  | prec cf cg hcf hcg =>
    sorry
  | rfind' cf hcf =>
    simp [eval]
    simp [Part.map]
    #check hcf
    constructor
    · constructor
      · intro h2
        rcases h2 with ⟨h2,hh2⟩
        use h2
        rcases hh2.left with ⟨hh2l,hhh2l⟩
        constructor
        · use hh2l
          -- sorry
        · have hh2r := hh2.right
          #check 1
      · sorry
      sorry
    · sorry

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
