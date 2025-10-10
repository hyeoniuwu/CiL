import Computability.Constructions.Option

open Nat
open Denumerable
open Encodable
open List


section rfindOpt
namespace Computability.Code

theorem rfind'_eqv_rfind : ((Nat.unpaired fun a m => (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) (Nat.pair x 0)) = (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair x n)) := by
-- theorem rfind'_eqv_rfind : ((Nat.unpaired fun a m => (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a (n + m))).map (· + m)) ∘ (Nat.pair <$> (fun (n:ℕ)=>n) <*> Part.some 0)) x = (Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair x n)) := by
  simp only [Nat.unpaired]
  simp only [Nat.unpair_pair, add_zero, Part.map_eq_map]
  exact rfl

/--`[code_rfind c](x)=smallest n s.t. [c](x,n)=0.`-/
-- def c_rfind : ℕ→ℕ := fun c => comp (rfind' c) (pair Computability.Code.id zero)
def c_rfind : Computability.Code→Computability.Code := fun c => (rfind' c).comp (pair c_id zero)

/-- Given a code `c` -/
abbrev rfind (O:ℕ→ℕ) : Code→ℕ→.ℕ := fun c => fun a=> Nat.rfind fun n => (fun m => m = 0) <$> eval O c (Nat.pair a n)
theorem c_rfind_prop : eval O (c_rfind c) a = (rfind O c a) := by
  unfold c_rfind
  unfold rfind
  rw [←rfind'_eqv_rfind]
  simp [eval,Seq.seq]

theorem c_rfind_prop2 : eval O (c_rfind c) a = (Nat.rfind (fun x => n2b' <$> eval O c (Nat.pair a x))) := by
  simp [c_rfind_prop]
  simp [rfind]
  unfold n2b'
  simp

def c_ppred := c_rfind (c_if_eq'.comp₂ left (succ.comp right))
@[simp] theorem c_ppred_ev : eval O c_ppred y = Nat.ppred y := by
  unfold c_ppred
  simp [c_rfind_prop2]
  simp [eval]
  simp [Seq.seq]
  cases y with
  | zero =>
    simp
    have : ¬ ((Nat.rfind fun x ↦ Part.some (n2b' 1))).Dom := by
      simp
      simp [n2b']


    exact Part.eq_none_iff'.mpr this
  | succ n =>
    simp
    unfold n2b'
    simp
    aesop


def c_ofOption (c:Code) := c_ppred.comp c
theorem c_ofOption_ev (hc1:code_total O c) : eval O (c_ofOption c) x = ↑(n2o ((eval O c x).get (hc1 x))) := by
  unfold c_ofOption
  simp [eval]
  simp [Part.Dom.bind (hc1 x)]
  cases (eval O c x).get (hc1 x) with
  | zero => simp;
  | succ n => simp;

-- def c_rfindOpt (c:Code) := (c_ofOption c).comp (c_rfind (c_isSome.comp (c.comp right)))
def c_rfindOpt (c:Code) := (c_ofOption c).comp₂ c_id (c_rfind (c_isSome.comp (c)))
@[simp] theorem c_rfindOpt_ev (hc1:code_total O c) : eval O (c_rfindOpt c) x =  Nat.rfindOpt (fun y => n2o $ (eval O c (Nat.pair x y)).get (hc1 (Nat.pair x y))) := by
  unfold c_rfindOpt
  simp [c_rfind_prop2]
  unfold rfindOpt
  simp [eval]
  simp [n2b']
  simp [b'2n]

  have : ((fun x_1 ↦ (eval O c (Nat.pair x x_1)).bind fun y ↦ Part.some !decide (n2o y = Option.none))) = ((fun n ↦ Part.some (n2o ((eval O c (Nat.pair x n)).get (hc1 (Nat.pair x n)))).isSome)) := by

    funext n
    simp [Part.Dom.bind (hc1 (Nat.pair x n))]
    cases n2o ((eval O c (Nat.pair x n)).get (hc1 (Nat.pair x n))) with
    | none => simp
    | some val => simp

  rw [this]
  if hh: (Nat.rfind fun n ↦ Part.some (n2o ((eval O c (Nat.pair x n)).get (hc1 (Nat.pair x n)))).isSome).Dom then
  simp [Part.Dom.bind hh]
  simp [Seq.seq]
  simp [c_ofOption_ev hc1]
  simp [Part.Dom.bind hh]
  -- have : ((eval O c ((Nat.rfind fun n ↦ Part.some (n2o ((eval O c (Nat.pair x n)).get (hc1 (Nat.pair x n)))).isSome).get hh))).Dom := by exact hc1 ((Nat.rfind fun n ↦ Part.some (n2o ((eval O c (Nat.pair x n)).get (hc1 (Nat.pair x n)))).isSome).get hh)
  -- congr


  else
  simp [Part.eq_none_iff'.mpr hh]
  simp [Seq.seq]
end Computability.Code
-- -- theorem Nat.PrimrecIn.rfindOpt:Nat.PrimrecIn O Nat.rfindOpt := by ...
-- -- theorem Nat.Primrec.rfindOpt:Nat.Primrec Nat.rfindOpt := by ...
end rfindOpt
