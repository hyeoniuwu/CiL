-- import Computability.Basic
import Computability.Constructions.Eval

open Nat Part

namespace Computability.Code

/--
Given a code `c`, `dovetail c` gives the code to the function which, on input n,
returns `y` s.t. `[c](n,y)=0`.
-/

def dovetailn (c:Code) : Code :=
  c_rfind $
  c_if_eq'.comp₂
  (c_evaln.comp₃ (pair left (left.comp right)) (c_const c) (right.comp right))
  (c_const 1)

theorem dovetailn_ev_0 (h:(eval O (dovetailn c) x).Dom) :
let dvt := (eval O (dovetailn c) x).get h
evaln O dvt.r c (Nat.pair x (dvt.l))=Option.some 0 := by
  extract_lets; expose_names
  have dvtrw : (eval O (dovetailn c) x).get h = dvt := rfl

  unfold dovetailn at h dvtrw

  have := Part.get_mem h
  rw [dvtrw] at this
  simp [c_rfind_prop] at this
  simp [eval] at this

  rcases this with ⟨⟨h2,h3,h4⟩,h5⟩; clear h5
  simp [Seq.seq] at h3
  rw [h3] at h4; clear h3; simp at h4
  have := Part.eq_some_iff.mpr h4; clear h4
  simp [o2n] at this
  exact Encodable.encode_inj.mp this
theorem dovetailn_ev_0' (h:(eval O (dovetailn c) x).Dom) :
let dvt := (eval O (dovetailn c) x).get h
eval O c (Nat.pair x (dvt.l))=Part.some 0 := by
  have := dovetailn_ev_0 h
  extract_lets
  expose_names
  extract_lets at this
  exact Part.eq_some_iff.mpr (evaln_sound this)

theorem dovetailn_ev_1' : eval O (dovetailn c) x=Part.none ↔ ∀ s y, evaln O s c (Nat.pair x y)≠Option.some 0 := by
  constructor
  ·
    contrapose
    simp
    intro s y
    intro h
    apply Part.not_none_iff_dom.mpr

    unfold dovetailn
    simp only [c_rfind_prop]
    simp only [comp₂, comp₃] -- without this theres a recursion depth error. why?
    simp []

    use Nat.pair y s
    simp [eval]
    simp [Seq.seq]
    constructor
    ·
      aesop? says
        simp_all only [Encodable.encode_some, Encodable.encode_nat, succ_eq_add_one, zero_add, ↓reduceIte,
        Part.mem_some_iff]
    aesop? says
      intro m a
      split
      next h_1 => simp_all only [Part.some_dom]
      next h_1 => simp_all only [Part.some_dom]

  ·
    contrapose
    intro h
    simp
    have hh := Part.not_none_iff_dom.mp h
    have := dovetailn_ev_0 hh

    aesop? says
      apply Exists.intro
      apply Exists.intro
      exact this

theorem dovetailn_ev_1_aux : (∀ s y, evaln O s c (Nat.pair x y)≠Option.some 0) ↔ ∀ y, eval O c (Nat.pair x y)≠Part.some 0 := by

  constructor
  contrapose
  simp
  intro y
  intro h
  have := evaln_complete.mp (Part.eq_some_iff.mp h)
  aesop

  contrapose
  simp
  intro s y
  intro h
  use y
  exact Part.eq_some_iff.mpr (evaln_sound h)

theorem dovetailn_ev_1 : eval O (dovetailn c) x=Part.none ↔ ∀ y, eval O c (Nat.pair x y)≠Part.some 0 := by
  exact Iff.trans dovetailn_ev_1' dovetailn_ev_1_aux
theorem dovetailn_ev_2 : (eval O (dovetailn c) x).Dom ↔ ∃ y, eval O c (Nat.pair x y)=Part.some 0 := by
  have := (@dovetailn_ev_1 O c x).not
  simp at this
  exact Iff.trans (Iff.symm Part.not_none_iff_dom) this





def dovetail (c:Code) : Code := left.comp (dovetailn c)

theorem dovetail_dom_iff_dovetailn_dom : (eval O (dovetail c) x).Dom ↔ (eval O (dovetailn c) x).Dom := by
  simp [dovetail,eval]
theorem dovetail_none_iff_dovetailn_none : (eval O (dovetail c) x) = Part.none ↔ (eval O (dovetailn c) x) = Part.none := by
  apply not_iff_not.mp
  simp [not_none_iff_dom]
  exact dovetail_dom_iff_dovetailn_dom
theorem dovetail_ev_0 (h:(eval O (dovetail c) x).Dom) :
let dvt := (eval O (dovetail c) x).get h
eval O c (Nat.pair x (dvt))=Part.some 0 := by
  -- sorry
  have : (eval O (dovetailn c) x).Dom := by
    exact dovetail_dom_iff_dovetailn_dom.mp h
  have main := dovetailn_ev_0' this
  extract_lets
  extract_lets at main
  expose_names

  have : dvt = dvt_1.l := by simp [dvt_1,dvt,dovetail, eval, Part.Dom.bind this]
  rw [this]
  exact main

theorem dovetail_ev_1' : eval O (dovetail c) x=Part.none ↔ ∀ s y, evaln O s c (Nat.pair x y)≠Option.some 0 := by
  simp [dovetail_none_iff_dovetailn_none]
  exact dovetailn_ev_1'
theorem dovetail_ev_1 : eval O (dovetail c) x=Part.none ↔ ∀ y, eval O c (Nat.pair x y)≠Part.some 0 := by
  exact Iff.trans dovetail_ev_1' dovetailn_ev_1_aux
theorem dovetail_ev_2 : (eval O (dovetail c) x).Dom ↔ ∃ y, eval O c (Nat.pair x y)=Part.some 0 := by
  have := (@dovetail_ev_1 O c x).not
  simp at this
  exact Iff.trans (Iff.symm Part.not_none_iff_dom) this
end Computability.Code
