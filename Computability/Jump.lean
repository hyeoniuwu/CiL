import Computability.Constructions.Basic
import Computability.Constructions.Primitive
import Computability.Basic

open Computability
open Classical
open Nat.RecursiveIn.Code

@[simp] noncomputable def jump (O : ℕ → ℕ) : ℕ → ℕ := λ n =>
  let part := eval O (decodeCode (Nat.unpair n).1) (Nat.unpair n).2
  dite part.Dom (λ proof => Nat.succ $ part.get proof) (λ _ => 0)
noncomputable abbrev K0 (O:ℕ→ℕ) := jump O

notation:10000 f"⌜" => jump f

namespace Nat.RecursiveIn.Code

def c_jump_decode (c) := c_ite c c_diverge (c_pred.comp c)
@[simp] theorem c_jump_decode_ev (hc:code_total O c): eval O (c_jump_decode c) x = if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  simp [c_jump_decode]
  simp [c_ite_ev hc]
  congr
  simp [eval]
  if h:(eval O c x).Dom then
    rw [Part.dom_imp_some h]
    simp [-Part.some_get]
  else
    simp [Part.eq_none_iff'.mpr h]
theorem c_jump_decode_ev' (hc:code_total O c): eval O (c_jump_decode c) = fun x => if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  funext xs
  exact c_jump_decode_ev hc

-- theorem Nat.RecursiveIn.jumpDecodeIte {O} {compute:ℕ→ℕ} (compute_recIn_fJump: compute ≤ᵀᶠ O): Nat.RecursiveIn O fun x ↦ if compute x = 0 then Part.none else ↑(some ((Nat.pred ∘ compute) x)) := by
--   apply Nat.RecursiveIn.ite
--   · exact compute_recIn_fJump
--   · exact Nat.RecursiveIn.none
--   · apply Nat.RecursiveIn.totalComp
--     · exact Nat.RecursiveIn.of_primrec Nat.Primrec.pred
--     · exact compute_recIn_fJump
theorem jump_recIn (f:ℕ→ℕ) : f ≤ᵀᶠ f⌜ := by
  apply exists_code.mpr
  let compute := oracle.comp (pair (c_const oracle) c_id)
  let c := c_jump_decode compute
  use c

  have compute_total : code_total f⌜ compute := by
    apply prim_total
    repeat (first|assumption|simp|constructor)

  simp [c]
  simp [c_jump_decode_ev' compute_total]
  rw [←eval_total_eq_eval compute_total]
  unfold compute
  simp [eval_total, eval, Seq.seq]
  exact rfl

@[simp] noncomputable def K (O:ℕ→ℕ) : ℕ → ℕ := λ n =>
  let part := eval O n n
  dite part.Dom (λ proof => Nat.succ $ part.get proof) (λ _ => 0)

theorem K_leq_K0 (O:ℕ→ℕ) : Nat.RecursiveIn (K0 O) (K O) := by
  apply exists_code.mpr
  use oracle.comp $ pair c_id c_id

  simp [eval,Seq.seq]
  exact rfl
theorem K0_leq_K (O:ℕ→ℕ) : Nat.RecursiveIn (K O) (K0 O) := by
  apply exists_code.mpr
  let compute := oracle.comp c_ev_const
  use compute

  have compute_total : code_total (K O) compute := by
    apply prim_total
    repeat (first|assumption|simp|constructor)

  unfold compute
  funext x
  rw [eval_total_comp compute_total]
  simp [eval, c_ev_const_ev']


theorem K0_eq_K {O} : (K O) ≡ᵀᶠ (K0 O) := ⟨K_leq_K0 O,K0_leq_K O⟩
theorem O_le_K0 (O:ℕ→ℕ) :  O ≤ᵀᶠ (K0 O) := by exact jump_recIn O
theorem O_le_K (O:ℕ→ℕ) : O ≤ᵀᶠ (K O) := TuringReducible.trans (O_le_K0 O) (K0_leq_K O)
  
theorem jump_not_leq_f (f:ℕ→ℕ) : ¬(f⌜ ≤ᵀᶠ f) := by
  intro h
  rcases exists_code.mp h with ⟨c_jf,hc_jh⟩
  let g := c_ite (c_jf.comp (pair c_id c_id)) (zero) c_diverge
  -- have g_total : code_total f g := by
  --   sorry
  --   -- apply prim_total
  --   -- repeat (first|assumption|simp|constructor)
  have fg : eval f g =  fun (x:ℕ) => if (f⌜) (Nat.pair x x) = 0 then Part.some 0 else Part.none := by
    unfold g
    simp
    funext x
    have : code_total f (c_jf.comp (pair c_id c_id)) := by
      intro x
      simp [eval,hc_jh,Seq.seq]
    simp [c_ite_ev this]
    simp [eval,hc_jh]
    simp [Seq.seq]
    rfl
  stop
  -- why does this blow up lean?
  cases Classical.em (eval f g g).Dom with
  | inl hh =>
    have hh2 := hh
    rw [fg] at hh2
    simp at hh2
    simp only [hh] at hh2
    simp only [↓reduceIte] at hh2
    simp only [Part.not_none_dom] at hh2
    -- exact hh2
    -- simp at hh2

    -- simp only [jump, unpair_pair, decodeCode_encodeCode, hh, ↓reduceDIte, succ_eq_add_one, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Part.not_none_dom] at hh2
  | inr hh =>
    have hh2 := hh
    -- rw [fg] at hh2
    -- simp [hh] at hh2  

    -- simp [eval]
    -- simp [Seq.seq]
  

theorem jump_not_leq_f' (f:ℕ→ℕ) : ¬(f⌜ ≤ᵀᶠ f) := by
  intro jump_reducible
  let g : (ℕ→.ℕ) := fun (x:ℕ) => if (f⌜) (Nat.pair x x) = 0 then 0 else Part.none

  have g_recIn_f : Nat.RecursiveIn f g := by
    simp only [g]
    apply Nat.RecursiveIn.ite
    · apply Nat.RecursiveIn.totalComp' jump_reducible
      exact Nat.RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id)
    · exact Nat.RecursiveIn.zero
    · exact Nat.RecursiveIn.none

  have exists_index_for_g : ∃ c : ℕ, eval f c = g := by exact exists_code_nat.mp g_recIn_f
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  cases Classical.em (g index_g).Dom with
  | inl h =>
    have contra : g index_g = Part.none := by
      simp [g]
      rw [index_g_is_g]
      exact fun a ↦ False.elim (a h)
    rw [contra] at h
    exact h
  | inr h =>
    have contra : g index_g = 0 := by
      simp [g]
      rw [index_g_is_g]
      exact fun a ↦ False.elim (h a)
    rw [contra] at h
    exact h trivial

theorem K_not_leq_f (O:ℕ→ℕ) : ¬(K O ≤ᵀᶠ O) := by
  intro h
  apply jump_not_leq_f
  exact TuringReducible.trans (K0_leq_K O) h

theorem O_lt_K0 {O:ℕ→ℕ} : O <ᵀᶠ (K0 O) := ⟨jump_recIn O,jump_not_leq_f O⟩


-- theorem re_iff_one_one_jump  (A : Set ℕ) (f : ℕ →. ℕ) :
-- recursively_enumerable_in₂ f A ↔ OneOneReducible A (f⌜).Dom := by sorry

-- theorem re_in_trans (A : Set ℕ) (f h : ℕ →. ℕ) :
--   recursively_enumerable_in₂ f A →
--   f ≤ᵀᶠ h →
--   recursively_enumerable_in₂ h A := by
--   intro freInA fh
--   simp [recursively_enumerable_in₂] at *
--   obtain ⟨g, hg, hA⟩ := freInA
--   use g
--   constructor
--   have tred : g ≤ᵀᶠ f := by
--     simp [TuringReducible]
--     assumption
--   exact TuringReducible.trans tred fh
--   exact hA
