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

/- Partially recursive partial functions `α → σ` between `Primcodable` types -/
-- def PartrecIn2 {β τ α σ} [Primcodable β] [Primcodable τ] [Primcodable α] [Primcodable σ] (g : β →. τ) (f : α →. σ) :=
--   Nat.RecursiveIn (fun n => Part.bind (Encodable.decode (β := β) n) fun a => (g a).map Encodable.encode) fun n => Part.bind (Encodable.decode (α := α) n) fun a => (f a).map Encodable.encode
-- def PartrecIn1 {α σ} [Primcodable α] [Primcodable σ] (g : ℕ→.ℕ) (f : α →. σ) :=
--   Nat.RecursiveIn g fun n => Part.bind (Encodable.decode (α := α) n) fun a => (f a).map Encodable.encode

-- instance : OfNat (Part ℕ) m where ofNat := Part.some (m)
namespace Nat.RecursiveIn.Code

def c_jump_decode (c) := c_ite c c_diverge (c_pred.comp c)
@[simp] theorem c_jump_decode_ev (hc:code_total O c): eval O (c_jump_decode c) x = if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  simp [c_jump_decode]
  simp [c_ite_ev hc]
  simp [c_diverge_ev]
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

theorem OracleNat.RecursiveInK (O:ℕ→ℕ) : Nat.RecursiveIn (K O) O := by
  apply exists_code.mpr
  let compute := (K O) ∘ c_evconst ∘ Nat.pair (encodeCode oracle)
  -- let h:ℕ→.ℕ := (fun x => if compute x=0 then Part.none else (Nat.pred ∘ compute) x)
  -- let compute := oracle.comp (pair (c_const oracle) c_id)
  let c := c_jump_decode compute
  use c
  -- use h

  sorry
  let compute := (K O) ∘ c_evconst ∘ Nat.pair (encodeCode oracle)
  let h:ℕ→.ℕ := (fun x => if compute x=0 then Part.none else (Nat.pred ∘ compute) x)

  have main : O = h := by

    simp only [h]
    funext xs
    cases Classical.em (compute xs = 0) with
    | inl h =>
        simp only [h]
        simp? [compute] at h says simp only [Function.comp_apply, K, c_evconst_ev, decodeCode_encodeCode, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, compute] at h
        exact Part.eq_none_iff'.mpr h
      | inr h =>
        simp only [compute]
        simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, Nat.pred_eq_sub_one, Part.coe_some, ite_not]
        simp only [compute] at h
        simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, Decidable.not_not] at h

        simp only [h]
        simp only [c_evconst_ev]
        simp? says simp only [↓reduceIte, ↓reduceDIte, decodeCode_encodeCode, add_tsub_cancel_right, Part.some_get]
        exact rfl

  have compute_recIn_KO : compute ≤ᵀᶠ (K O) := by
    simp only [compute, TuringReducible]

    apply Nat.RecursiveIn.totalComp
    · exact Nat.RecursiveIn.oracle
    · apply Nat.RecursiveIn.totalComp
      · exact Nat.RecursiveIn.of_primrecIn c_evconst_pr
      · rw [Nat.RecursiveIn.pair']
        apply Nat.RecursiveIn.pair
        · simp only [encodeCode]
          exact Nat.RecursiveIn.of_primrec (Nat.Primrec.const 4)
        · exact Nat.RecursiveIn.id

  rw (config := {occs := .pos [1]}) [main]
  simp only [h]
  exact Nat.RecursiveIn.jumpDecodeIte compute_recIn_KO

theorem K_leq_K0 (O:ℕ→ℕ) : Nat.RecursiveIn (K0 O) (K O) := by
  apply exists_code.mpr
  use oracle.comp $ pair c_id c_id

  simp [eval,Seq.seq]
  exact rfl

theorem K0_leq_K (O:ℕ→ℕ) : Nat.RecursiveIn (K O) (K0 O) := by
  let compute := (K O) ∘ c_evconst
  let h:ℕ→.ℕ := (compute)

  have main : O⌜ = h := by
    simp only [h]
    funext xs
    cases Classical.em (compute xs = 0) with
    | inl h =>
        simp only [PFun.coe_val, jump, Nat.succ_eq_add_one, Part.some_inj]
        simp only [h]
        simp only [dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false]
        simp only [compute] at h
        simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false] at h
        rw [show xs = Nat.pair (xs.unpair.1) (xs.unpair.2) from Eq.symm (Nat.pair_unpair xs)] at h
        simp only [c_evconst_ev] at h
        exact h
    | inr h =>
      simp only [PFun.coe_val, jump, Nat.succ_eq_add_one, Part.some_inj]
      simp only [compute]
      simp only [compute] at h
      simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, Decidable.not_not] at h
      simp only [Function.comp_apply, K, Nat.succ_eq_add_one]
      simp only [h]
      rw [show xs = Nat.pair (xs.unpair.1) (xs.unpair.2) from Eq.symm (Nat.pair_unpair xs)] at h
      simp only [c_evconst_ev] at h
      simp only [h]
      have temp : c_evconst xs = c_evconst (Nat.pair (xs.unpair.1) (xs.unpair.2)) := by simp only [Nat.pair_unpair]
      simp only [temp]
      simp only [c_evconst_ev]

  have compute_recIn_KO : compute ≤ᵀᶠ (K O) := by
    simp only [compute, TuringReducible]

    apply Nat.RecursiveIn.totalComp
    · exact Nat.RecursiveIn.oracle
    · exact Nat.RecursiveIn.of_primrecIn c_evconst_pr

  rw [main]
  simp only [h]
  exact compute_recIn_KO

theorem K0_eq_K {O} : (K O) ≡ᵀᶠ (K0 O) := ⟨K_leq_K0 O,K0_leq_K O⟩


theorem jump_not_leq_f (f:ℕ→ℕ) : ¬(f⌜ ≤ᵀᶠ f) := by
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
      simp only [g]
      simp only [jump, Nat.unpair_pair, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero,one_ne_zero, and_false, imp_false, ite_not, ite_eq_left_iff]
      simp only [index_g_is_g]
      exact fun a ↦ False.elim (a h)
    rw [contra] at h
    exact h
  | inr h =>
    have contra : g index_g = 0 := by
      simp only [g]
      simp only [jump, Nat.unpair_pair, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero,one_ne_zero, and_false, imp_false, ite_not]
      simp only [index_g_is_g]
      exact if_neg h
    rw [contra] at h
    exact h trivial

theorem K_not_leq_f (f:ℕ→ℕ) : ¬(K f ≤ᵀᶠ f) := by
  intro h
  have h2 : f⌜ ≤ᵀᶠ f := by
    apply TuringReducible.trans
    · apply K0_leq_K
    · exact h
  apply jump_not_leq_f
  exact h2

theorem id_lt_K0 {O:ℕ→ℕ} : O <ᵀᶠ (K0 O) := by
  constructor
  exact jump_recIn O
  exact jump_not_leq_f O

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
