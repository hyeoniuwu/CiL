import Mathlib.Data.Nat.Pairing
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Find
-- import Mathlib.Computability.Partrec



open Part

namespace Nat


section Rfind

variable (p : ℕ →. Bool)

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, false ∈ p k

private def wf_lbp (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom) : WellFounded (lbp p) :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction m generalizing k with (refine ⟨_, fun y r => ?_⟩; rcases r with ⟨rfl, a⟩)
    | zero => injection mem_unique pn.1 (a _ kn)
    | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)⟩

variable (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom)

/-- Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined as false.
Returns a subtype. -/
def rfindX : { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } :=
  suffices ∀ k, (∀ n < k, false ∈ p n) → { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rcases lt_trichotomy m n with (h₃ | h₃ | h₃)
        · exact h₂ _ h₃
        · rw [h₃]
          exact h₁.fst
        · injection mem_unique h₁ (al _ h₃)
      cases e : (p m).get pm
      · suffices ∀ᵉ k ≤ m, false ∈ p k from IH _ ⟨rfl, this⟩ fun n h => this _ (le_of_lt_succ h)
        intro n h
        rcases h.lt_or_eq_dec with h | h
        · exact al _ h
        · rw [h]
          exact ⟨_, e⟩
      · exact ⟨m, ⟨_, e⟩, al⟩)

end Rfind

/-- Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined as false.
Returns a `Part`. -/
def rfind (p : ℕ →. Bool) : Part ℕ :=
  ⟨_, fun h => (rfindX p h).1⟩

theorem rfind_spec {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : true ∈ p n :=
  h.snd ▸ (rfindX p h.fst).2.1

theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : ∀ {m : ℕ}, m < n → false ∈ p m :=
  @(h.snd ▸ @((rfindX p h.fst).2.2))

@[simp]
theorem rfind_dom {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).Dom :=
  Iff.rfl

theorem rfind_dom' {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).Dom :=
  exists_congr fun _ =>
    and_congr_right fun pn =>
      ⟨fun H _ h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H _ h =>
        H (le_of_lt h)⟩

@[simp]
theorem mem_rfind {p : ℕ →. Bool} {n : ℕ} :
    n ∈ rfind p ↔ true ∈ p n ∧ ∀ {m : ℕ}, m < n → false ∈ p m :=
  ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ => by
    let ⟨m, hm⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨_, h₁, fun {m} mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm h)⟩

theorem rfind_min' {p : ℕ → Bool} {m : ℕ} (pm : p m) : ∃ n ∈ rfind p, n ≤ m :=
  have : true ∈ (p : ℕ →. Bool) m := ⟨trivial, pm⟩
  let ⟨n, hn⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨m, this, fun {_} _ => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩

theorem rfind_zero_none (p : ℕ →. Bool) (p0 : p 0 = Part.none) : rfind p = Part.none :=
  eq_none_iff.2 fun _ h =>
    let ⟨_, _, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)

/-- Find the smallest `n` satisfying `f n`, where all `f k` for `k < n` are defined as false.
Returns a `Part`. -/
def rfindOpt {α} (f : ℕ → Option α) : Part α :=
  (rfind fun n => (f n).isSome).bind fun n => f n

theorem rfindOpt_spec {α} {f : ℕ → Option α} {a} (h : a ∈ rfindOpt f) : ∃ n, a ∈ f n :=
  let ⟨n, _, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩

theorem rfindOpt_dom {α} {f : ℕ → Option α} : (rfindOpt f).Dom ↔ ∃ n a, a ∈ f n :=
  ⟨fun h => (rfindOpt_spec ⟨h, rfl⟩).imp fun _ h => ⟨_, h⟩, fun h => by
    have h' : ∃ n, (f n).isSome := h.imp fun n => Option.isSome_iff_exists.2
    have s := Nat.find_spec h'
    have fd : (rfind fun n => (f n).isSome).Dom :=
      ⟨Nat.find h', by simpa using s.symm, fun _ _ => trivial⟩
    refine ⟨fd, ?_⟩
    have := rfind_spec (get_mem fd)
    simpa using this⟩

theorem rfindOpt_mono {α} {f : ℕ → Option α} (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n) {a} :
    a ∈ rfindOpt f ↔ ∃ n, a ∈ f n :=
  ⟨rfindOpt_spec, fun ⟨n, h⟩ => by
    have h' := rfindOpt_dom.2 ⟨_, _, h⟩
    obtain ⟨k, hk⟩ := rfindOpt_spec ⟨h', rfl⟩
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩


/-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
@[simp, reducible]
def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2

-- inductive RecursiveIn (O : ℕ → ℕ) : (ℕ →. ℕ) → Prop
--   | zero : RecursiveIn O fun _ => 0
--   | succ : RecursiveIn O Nat.succ
--   | left : RecursiveIn O fun n => (Nat.unpair n).1
--   | right : RecursiveIn O fun n => (Nat.unpair n).2
--   | oracle : RecursiveIn O O
--   | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
--       RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
--   | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
--       RecursiveIn O fun n => h n >>= f
--   | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
--       RecursiveIn O fun p =>
--         let (a, n) := Nat.unpair p
--         n.rec (f a) fun y IH => do
--           let i ← IH
--           h (Nat.pair a (Nat.pair y i))
--   | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
--       RecursiveIn O fun a =>
--         Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)
inductive RecursiveIn (O : ℕ → ℕ) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : RecursiveIn O O
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O
        -- fun a =>
        $ Nat.unpaired fun a m =>
          (Nat.rfind fun n => (fun x => x = 0) <$> f (Nat.pair a (n + m))).map (· + m)

/-- The primitive recursive functions `ℕ → ℕ`. -/
protected inductive PrimrecIn (O:ℕ→ℕ) : (ℕ → ℕ) → Prop
  | zero : Nat.PrimrecIn O fun _ => 0
  | protected succ : Nat.PrimrecIn O succ
  | left : Nat.PrimrecIn O fun n => n.unpair.1
  | right : Nat.PrimrecIn O fun n => n.unpair.2
  | oracle : Nat.PrimrecIn O O
  | pair {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => pair (f n) (g n)
  | comp {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => f (g n)
  | prec {f g} :
      Nat.PrimrecIn O f →
        Nat.PrimrecIn O g →
          Nat.PrimrecIn O (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

end Nat
