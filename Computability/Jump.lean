import Computability.Constructions.Basic
import Computability.Constructions.Primitive
import Computability.Basic

open Computability
open Classical
open Computability.Code

@[simp] noncomputable def K0 (O : ℕ → ℕ) : ℕ → ℕ := λ n =>
  let part := eval O n.l n.r
  if h:part.Dom then part.get h+1 else 0
@[simp] noncomputable def K (O:ℕ→ℕ) : ℕ → ℕ := λ n =>
  let part := eval O n n
  if h:part.Dom then part.get h + 1 else 0
noncomputable abbrev jump (O:ℕ→ℕ) : ℕ → ℕ := K0 O

notation:10000 f"⌜" => jump f

namespace Computability.Code

def c_jump_decode (c:Code) := c_ite c c_diverge (c_pred.comp c)
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
-- theorem jump_recIn (f:ℕ→ℕ) : f ≤ᵀᶠ f⌜ := by
theorem O_le_K0 (O:ℕ→ℕ) :  O ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr  -- change goal to: ∃ c, eval (K0 O) c = O
  let q := oracle.comp (pair (c_const oracle) c_id)
  use c_jump_decode q

  have compute_total : code_total (K0 O) q := by
    apply prim_total
    apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

  simp only [c_jump_decode_ev' compute_total]
  simp only [q]
  simp [eval, Seq.seq]
  exact rfl
theorem O_le_J (O:ℕ→ℕ) : O ≤ᵀᶠ O⌜ :=  O_le_K0 O

theorem K_leq_K0 (O:ℕ→ℕ) : (K O)  ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr
  use oracle.comp $ pair c_id c_id

  simp [eval,Seq.seq]
  exact rfl
theorem K0_leq_K (O:ℕ→ℕ) : (K0 O) ≤ᵀᶠ (K O)  := by
  apply exists_code.mpr
  let compute := oracle.comp c_ev_const
  use compute

  have compute_total : code_total (K O) compute := by
    apply prim_total
    apply_rules (config := {maxDepth:=60, symm:=false, exfalso:=false, transparency:=.reducible}) only [*] using cp

  unfold compute
  funext x
  rw [eval_total_comp compute_total]
  simp [eval, c_ev_const_ev']
theorem K_eq_K0 {O} : (K O)  ≡ᵀᶠ (K0 O) := ⟨K_leq_K0 O,K0_leq_K O⟩
theorem K0_eq_K {O} : (K0 O) ≡ᵀᶠ (K O)  := K_eq_K0.symm
theorem O_le_K (O:ℕ→ℕ) : O ≤ᵀᶠ (K O) := TuringReducible.trans (O_le_K0 O) (K0_leq_K O)

theorem jump_not_leq_f (f:ℕ→ℕ) : ¬(f⌜ ≤ᵀᶠ f) := by
  intro h
  rcases exists_code.mp h with ⟨c_jf,hc_jh⟩
  let g := c_ite (c_jf.comp (pair c_id c_id)) (zero) c_diverge
  have fg : eval f g =  fun (x:ℕ) => if (f⌜) (Nat.pair x x) = 0 then Part.some 0 else Part.none := by
    unfold g
    funext x
    have : code_total f (c_jf.comp (pair c_id c_id)) := by intro x; simp [eval,hc_jh,Seq.seq]
    simp [c_ite_ev this, eval, hc_jh, Seq.seq]
  -- why does this blow up lean?
  -- nvm, fixed [25-09-24 00:10:28]
  cases Classical.em (eval f g g).Dom with
  | inl hh =>
    have hh2 := hh
    rw [fg] at hh2
    simp [hh] at hh2
  | inr hh =>
    have hh2 := hh
    rw [fg] at hh2
    simp [hh] at hh2

-- theorem jump_not_leq_f' (O:ℕ→ℕ) : ¬(O⌜ ≤ᵀᶠ O) := by
theorem K0_nle_O (O:ℕ→ℕ) : ¬(K0 O ≤ᵀᶠ O) := by
  intro jump_reducible
  let g : (ℕ→.ℕ) := fun (x:ℕ) => if (O⌜) (Nat.pair x x) = 0 then 0 else Part.none

  have g_recIn_f : Nat.RecursiveIn O g := by
    simp only [g]
    apply Nat.RecursiveIn.ite
    · apply Nat.RecursiveIn.totalComp' jump_reducible
      exact Nat.RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id)
    · exact Nat.RecursiveIn.zero
    · exact Nat.RecursiveIn.none

  have exists_index_for_g : ∃ c : ℕ, eval O c = g := by exact exists_code_nat.mp g_recIn_f
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

theorem K_nle_O (O:ℕ→ℕ) : ¬(K O ≤ᵀᶠ O) := by
  intro h
  apply jump_not_leq_f
  exact TuringReducible.trans (K0_leq_K O) h

theorem O_lt_K0 {O:ℕ→ℕ} : O <ᵀᶠ (K0 O) := ⟨O_le_J O,jump_not_leq_f O⟩


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
