import Computability.Constructions.Primitive

open Nat.RecursiveIn.Code

namespace Nat.RecursiveIn.Code

def c_diverge := rfind' (c_const 1)
theorem c_diverge_ev : eval O c_diverge x = Part.none := by
  simp [c_diverge,eval]
  apply Part.eq_none_iff.mpr
  simp





def c_ifz1 (c) (a b:ℕ) := c_add.comp₂ (c_mul.comp₂ (c_const b) (c_sg.comp c)) (c_mul.comp₂ (c_const a) (c_sg'.comp c))
open Classical in
theorem c_ifz1_ev (hc:code_total O c) : eval O (c_ifz1 c a b) x = if (eval O c x=Part.some 0) then Part.some a else Part.some b := by
  simp [c_ifz1]
  simp [eval]
  simp [Seq.seq]
  have : (eval O c x).Dom := by exact hc x
  simp [Part.Dom.bind (hc x)]
  split
  next h => simp [Part.get_eq_iff_eq_some.mp h]
  next h => simp [Part.ne_of_get_ne' h]


-- /-- Given a total choice function `c`, returns `a` or `b` conditioning on whether `c x=0`. -/
-- theorem Nat.RecursiveIn.ifz1 {O:ℕ→ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c): Nat.RecursiveIn O (fun x => if (c x=0) then (a:ℕ) else (b:ℕ):ℕ→ℕ) := by
--   apply exists_code.mpr
--   rcases exists_code.mp hc with ⟨cc,hcc⟩
--   use (c_ifz1 cc a b)
--   have := c_ifz1_ev hc
--   simp [c_ifz1_ev hc]

--   let construction := fun x =>
--     Nat.add
--     (Nat.mul b (Nat.sg (c x)))
--     (Nat.mul a (Nat.sg' (c x)))
--   have consRecin:Nat.RecursiveIn O construction := by
--     simp only [construction]
--     apply Nat.RecursiveIn.totalComp₂
--     · apply of_primrec Nat.Primrec.add
--     · apply Nat.RecursiveIn.totalComp₂
--       · apply of_primrec Nat.Primrec.mul
--       · apply of_primrec (Nat.Primrec.const b)
--       · apply Nat.RecursiveIn.totalComp'
--         · exact of_primrec Nat.Primrec.sg
--         · exact hc
--     · apply Nat.RecursiveIn.totalComp₂
--       · apply of_primrec Nat.Primrec.mul
--       · apply of_primrec (Nat.Primrec.const a)
--       · apply Nat.RecursiveIn.totalComp'
--         · exact of_primrec Nat.Primrec.sg'
--         · exact hc
--   have consEq: (fun x => if (c x=0) then (a:ℕ) else (b:ℕ):ℕ→ℕ) = construction := by
--     simp [construction]
--     funext xs
--     cases Classical.em (c xs = 0) with -- do i really need classical.em here?
--     | inl h => simp [h]
--     | inr h => simp [h]

--   rw [consEq]
--   exact consRecin

def c_ite (c a b:Nat.RecursiveIn.Code) := c_eval.comp
open Classical in
theorem c_ite_ev (hc:code_total O c) : eval O (c_ite c a b) x = if (eval O c x=Part.some 0) then (eval O a x) else (eval O b x) := by

  sorry

theorem Nat.RecursiveIn.ite {O:ℕ→ℕ} {f g:ℕ→.ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c) (hf:Nat.RecursiveIn O f) (hg:Nat.RecursiveIn O g):Nat.RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
    have exists_index_for_f:∃ c:ℕ, eval O c = f := by exact exists_code_nat.mp hf
    have exists_index_for_g:∃ c:ℕ, eval O c = g := by exact exists_code_nat.mp hg
    rcases exists_index_for_f with ⟨index_f,index_f_is_f⟩
    rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

    have main2:(fun a => if (c a=0) then (f a) else (g a)) = fun a => Nat.pair (if c a=0 then (index_f) else (index_g)) a >>= eval₁ O := by
      funext xs
      cases Classical.em (c xs = 0) with
      | inl h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval₁, Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_f_is_f)) xs
      | inr h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval₁, Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_g_is_g)) xs
    rw [main2]


    apply Nat.RecursiveIn.evalRecInO'
    apply Nat.RecursiveIn.someTotal

    rw [Nat.RecursiveIn.pair']

    apply Nat.RecursiveIn.pair
    · simp only [Part.coe_some]
      apply Nat.RecursiveIn.ifz1
      exact hc
    exact id





end Nat.RecursiveIn.Code
