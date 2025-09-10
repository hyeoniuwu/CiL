import Computability.Basic
import Computability.Constructions.Eval

open Part
namespace Nat.RecursiveIn.Code



theorem rfind'_eqv_rfind : ((Nat.unpaired fun a m => (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) (Nat.pair x 0)) = (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair x n)) := by
-- theorem rfind'_eqv_rfind : ((Nat.unpaired fun a m => (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) ∘ (Nat.pair <$> (fun (n:ℕ)=>n) <*> Part.some 0)) x = (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair x n)) := by
  simp only [Nat.unpaired]
  simp only [Nat.unpair_pair, add_zero, Part.map_eq_map]
  exact rfl


/--`[code_rfind c](x)=smallest n s.t. [c](x,n)=0.`-/
-- def c_rfind : ℕ→ℕ := fun c => comp (rfind' c) (pair Nat.RecursiveIn.Code.id zero)
def c_rfind : Nat.RecursiveIn.Code→Nat.RecursiveIn.Code := fun c => comp (rfind' c) (pair Nat.RecursiveIn.Code.id zero)


/-- Given a code `c` -/
abbrev rfind (O:ℕ→ℕ) : ℕ→ℕ→.ℕ := fun c => fun a=> Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a n)
theorem c_rfind_prop : eval O (c_rfind c) a = (rfind O c a) := by
  unfold c_rfind
  unfold rfind
  rw [←rfind'_eqv_rfind]
  simp? says simp only [decodeCode_encodeCode, Nat.unpaired, Nat.unpair_pair, add_zero, Part.map_eq_map]
  simp only [eval]
  simp only [eval_id]
  simp only [pure]
  simp only [PFun.pure]
  simp only [Seq.seq]
  simp










/--
Given a code `c`, `dovetail c` gives the code to the function which, on input n,
returns `y` s.t. `[c](n,y)=0`.
-/
-- noncomputable def dovetail_aux (c:Code) : Code := c_evaln.comp₃ (left) c right
-- noncomputable def dovetail (c:Code) : Code := (c_rfind (c_evaln.comp₃ (pair left (left.comp right)) (c_const c) (right.comp right)))
noncomputable def dovetail (c:Code) : Code :=
  c_rfind $
  c_if_eq'.comp₂
  (c_evaln.comp₃ (pair left (left.comp right)) (c_const c) (right.comp right))
  (c_const 1)
-- noncomputable def dovetail (c:Code) : Code := (rfind' (c_evaln.comp₃ (pair left (right.comp left)) (c_const c) (right.comp right))).comp₂ c_id zero
-- theorem dovetail_evp_0 (hc:code_prim c) : y∈eval O (dovetail c) x → eval O c (Nat.pair x y)=0 := by sorry
-- theorem dovetail_evp_0' (hc:code_prim c) (h:(eval O (dovetail c) x).Dom) : eval_prim O c (Nat.pair x ((eval O (dovetail c) x).get h))=0 := by sorry
-- theorem dovetail_evp_1 (hc:code_prim c) : eval O (dovetail c) x=Part.none ↔ ∀ y, eval_prim O c (Nat.pair x y)=0 := by sorry
-- theorem dovetail_ev_0 : y∈eval O (dovetail c) x → eval O c (Nat.pair x y)=0 := by sorry
theorem dovetail_ev_0 (h:(eval O (dovetail c) x).Dom) :
let dvt := (eval O (dovetail c) x).get h
evaln O dvt.r c (Nat.pair x (dvt.l))=Option.some 0 := by
  extract_lets
  expose_names

  unfold dovetail at h
  simp [] at h

  have dvtrw : (eval O
    (c_rfind
      (c_if_eq'.comp
        ((c_evaln.comp ((left.pair (left.comp right)).pair ((c_const c.encodeCode).pair (right.comp right)))).pair
          (c_const 1))))
    x) = (eval O c.dovetail x) := by rfl
  let temprw := (eval O
    (c_rfind
      (c_if_eq'.comp
        ((c_evaln.comp ((left.pair (left.comp right)).pair ((c_const c.encodeCode).pair (right.comp right)))).pair
          (c_const 1))))
    x).get
    h
  have temprwrw : (eval O
    (c_rfind
      (c_if_eq'.comp
        ((c_evaln.comp ((left.pair (left.comp right)).pair ((c_const c.encodeCode).pair (right.comp right)))).pair
          (c_const 1))))
    x).get
    h = temprw := rfl

  have := Part.get_mem h
  rw [temprwrw] at this
  simp [c_rfind_prop] at this
  simp [eval] at this

  rcases this with ⟨⟨h2,h3,h4⟩,h5⟩; clear h5
  simp [Seq.seq] at h3
  rw [h3] at h4; clear h3
  simp at h4
  have temprw_eq_dvt : temprw = dvt := by exact temprwrw
  rw [temprw_eq_dvt] at h4
  have := Part.eq_some_iff.mpr h4; clear h4
  simp at this
  simp [o2n] at this
  apply Encodable.encode_inj.mp
  exact this
theorem dovetail_ev_0' (h:(eval O (dovetail c) x).Dom) :
let dvt := (eval O (dovetail c) x).get h
eval O c (Nat.pair x (dvt.l))=Part.some 0 := by
  have := dovetail_ev_0 h
  extract_lets
  expose_names
  extract_lets at this
  exact Part.eq_some_iff.mpr (evaln_sound this)
-- theorem dovetail_ev_0'' (h:(eval O (dovetail c) x).Dom) : ∃ y, eval O c (Nat.pair x y)=Part.some 0 := by sorry
-- let dvt := (eval O (dovetail c) x).get h
-- evaln O dvt.r c (Nat.pair x (dvt.l))=Option.some 0
theorem dovetail_ev_1' : eval O (dovetail c) x=Part.none ↔ ∀ s y, evaln O s c (Nat.pair x y)≠Option.some 0 := by
  constructor
  · 
    contrapose
    simp
    intro s y
    intro h
    apply Part.not_none_iff_dom.mpr

    unfold dovetail
    simp []
    simp only [c_rfind_prop]
    simp
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
    have := dovetail_ev_0 hh

    aesop? says
      apply Exists.intro
      apply Exists.intro
      exact this

theorem dovetail_ev_1_aux : (∀ s y, evaln O s c (Nat.pair x y)≠Option.some 0) ↔ ∀ y, eval O c (Nat.pair x y)≠Part.some 0 := by
  
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
  
theorem dovetail_ev_1 : eval O (dovetail c) x=Part.none ↔ ∀ y, eval O c (Nat.pair x y)≠Part.some 0 := by
  exact Iff.trans dovetail_ev_1' dovetail_ev_1_aux
theorem dovetail_ev_2 : (eval O (dovetail c) x).Dom ↔ ∃ y, eval O c (Nat.pair x y)=Part.some 0 := by
  have := (@dovetail_ev_1 O c x).not
  simp at this
  exact Iff.trans (Iff.symm Part.not_none_iff_dom) this


end Nat.RecursiveIn.Code
