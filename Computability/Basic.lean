/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Label
import Computability.Encoding
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.BitIndices

/-!
# Notations, helper functions

In this file we define helper functions which will be used in later computability arguments.
-/

open Nat Classical Computability.Code

-- general helper functions
section pair
notation "⟪" x "," y "⟫" => Nat.pair x y
notation "⟪" x "," y "⟫" => Nat.pair <$> x <*> y
notation "⟪" x "," y "," z "⟫" => Nat.pair x (Nat.pair y z)
notation "⟪" x "," y "," z "⟫" => Nat.pair <$> x <*> (Nat.pair <$> y <*> z)
notation "⟪" x "," y "," z "," w "⟫" => Nat.pair (Nat.pair x y) (Nat.pair z w)
notation "⟪" x "," y "," z "," w "⟫" => Nat.pair <$> (Nat.pair <$> x <*> y) <*> (Nat.pair <$> z <*> w)
def Nat.l (n : ℕ) := n.unpair.1
def Nat.r (n : ℕ) := n.unpair.2
@[simp] theorem pair_l {x y} : (Nat.pair x y).l = x := by simp [Nat.l]
@[simp] theorem pair_r {x y} : (Nat.pair x y).r = y := by simp [Nat.r]
@[simp] theorem pair_lr {x} : (Nat.pair x.l x.r) = x := by simp [Nat.r, Nat.l]
@[simp] theorem unpair1_to_l {n : ℕ} : (n.unpair.1) = n.l := by simp [Nat.l]
@[simp] theorem unpair2_to_r {n : ℕ} : (n.unpair.2) = n.r := by simp [Nat.r]
@[simp, reducible] def Nat.unpaired2 {α} (f : ℕ → ℕ → α) (n : ℕ) : α := f n.l n.r
theorem pair_nonzero_right_pos_aux {x s : ℕ} : ¬ ⟪x, s+1⟫ = 0 := by
  rw [show 0=Nat.pair 0 0 from rfl]
  rw [pair_eq_pair]
  intro h
  have hr := h.right
  contradiction
@[simp] theorem pair_nonzero_right_pos {x s : ℕ} : ⟪x, s+1⟫ > 0 :=
  zero_lt_of_ne_zero pair_nonzero_right_pos_aux
theorem pair_nonzero_left_pos_aux {x s : ℕ} : ¬ (⟪s+1, x⟫ = 0) := by
  rw [show 0=Nat.pair 0 0 from rfl]
  rw [pair_eq_pair]
  intro h
  have hr := h.left
  contradiction
@[simp] theorem pair_nonzero_left_pos {x s : ℕ} : ⟪s+1, x⟫ > 0 :=
  zero_lt_of_ne_zero pair_nonzero_left_pos_aux
theorem pair_r_gt0 {x} : x>0→(Nat.pair y x)>0 := by
  contrapose
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
  intro h
  rw [show x=(Nat.pair y x).unpair.2 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
theorem pair_l_gt0 {x} : x>0→(Nat.pair x y)>0 := by
  contrapose
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
  intro h
  rw [show x=(Nat.pair x y).unpair.1 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
theorem pair_r_ne_0 {x} : x≠0→(Nat.pair y x)≠0 := by
  contrapose
  intro h
  rw [show x=(Nat.pair y x).unpair.2 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
theorem pair_l_ne_0 {x} : x≠0→(Nat.pair x y)≠0 := by
  contrapose
  intro h
  rw [show x=(Nat.pair x y).unpair.1 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
end pair


def n2b (n : ℕ) : Bool := if n = 0 then false else true
def b2n (b : Bool) : ℕ := if b then 1 else 0
def n2b' (n : ℕ) : Bool := if n=0 then true else false
def b'2n (b : Bool) : ℕ := if b then 0 else 1
theorem b2n_a0 {x} : b2n x = 0 ↔ x = false := by simp [b2n]

open Denumerable Encodable
abbrev n2o := @ofNat (Option ℕ) _
abbrev o2n := @encode (Option ℕ) _

section fs
/-
We define functions to treat naturals as finite sets.
-/
abbrev fs_in := Nat.testBit
/-
Examples:
fs_in 0b0010 0 = false
fs_in 0b0010 1 = true
fs_in 0b0010 2 = false
fs_in 0b0010 3 = false
-/

/-- `fs_add a x` gives the natural representing the set with `x` added to `a` interpreted as a finite set. -/
abbrev fs_add : ℕ→ℕ→ℕ := λ a x ↦ a ||| (2^x)

/-- `fs_add a` gives the the size of `a` interepreted as a finite set. -/
def fs_size := List.length.comp Nat.bitIndices
/-
Examples:
fs_size 0b010 = 1
fs_size 0b111 = 3
fs_size 0b011000111 = 5
-/

theorem fs_in_singleton {x y}: fs_in (2^y) x ↔ x=y := by grind
theorem fs_in_singleton': Nat.testBit (2^y) x = false ↔ y≠x := by grind
end fs

namespace Computability.Code.nc_to_nn
@[coe] protected def lift (f:ℕ→Code) : ℕ→ℕ := fun x => c2n (f x)
instance : Coe (ℕ→Code) (ℕ→ℕ) := ⟨Computability.Code.nc_to_nn.lift⟩
end Computability.Code.nc_to_nn
namespace Computability.Code.cc_to_nn
@[coe] protected def lift (f:Code→Code) : ℕ→ℕ := c2n ∘ f ∘ n2c
instance : Coe (Code→Code) (ℕ→ℕ) := ⟨Computability.Code.cc_to_nn.lift⟩
end Computability.Code.cc_to_nn

section primrec
-- templates for primrec constructions as codes
namespace Computability.Code
@[aesop safe, cp] inductive code_prim : Code → Prop
| zero:code_prim zero
| succ:code_prim succ
| left:code_prim left
| right:code_prim right
| oracle:code_prim oracle
| pair {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (pair a b)
| comp {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (comp a b)
| prec {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (prec a b)
@[cp] theorem zero_prim : code_prim zero := code_prim.zero
@[cp] theorem succ_prim : code_prim succ := code_prim.succ
@[cp] theorem left_prim : code_prim left := code_prim.left
@[cp] theorem right_prim : code_prim right := code_prim.right
@[cp] theorem oracle_prim : code_prim oracle := code_prim.oracle
@[cp] theorem pair_prim (ha:code_prim a) (hb:code_prim b) : code_prim (pair a b) := code_prim.pair ha hb
@[cp] theorem comp_prim (ha:code_prim a) (hb:code_prim b) : code_prim (comp a b) := code_prim.comp ha hb
@[cp] theorem prec_prim (ha:code_prim a) (hb:code_prim b) : code_prim (prec a b) := code_prim.prec ha hb
def code_total (O) (c:Code) := ∀x, (eval O c x).Dom
@[simp] theorem zero_total {O} : code_total O zero := λ _ ↦ trivial
@[simp] theorem left_total {O} : code_total O left := λ _ ↦ trivial
@[simp] theorem right_total {O} : code_total O right := λ _ ↦ trivial
@[simp] theorem succ_total {O} : code_total O succ := λ _ ↦ trivial
@[simp] theorem oracle_total {O} : code_total O oracle := λ _ ↦ trivial
theorem prim_total (h:code_prim c): code_total O c := by
  unfold code_total
  induction h with
  | zero                   => simp [eval];
  | succ                   => simp [eval];
  | left                   => simp [eval];
  | right                  => simp [eval];
  | oracle                 => simp [eval];
  | pair ha hb ha_ih hb_ih => simp [eval, Seq.seq]; exact fun x ↦ ⟨ha_ih x, hb_ih x⟩
  | comp ha hb ha_ih hb_ih =>
    simp [eval]
    intro x
    use hb_ih x
    (expose_names; exact ha_ih ((eval O b x).get (hb_ih x)))
  | prec ha hb ha_ih hb_ih =>
    expose_names
    simp [eval]
    intro x
    induction x.r with
    | zero => exact ha_ih x.l
    | succ y' IH' => use IH'; apply hb_ih
@[simp] def evalp (O:ℕ→ℕ):Code→ℕ→ℕ
| zero       => λ _ ↦ 0
| succ       => Nat.succ
| left       => Nat.l
| right      => Nat.r
| oracle     => O
| pair cf cg => λ x ↦ Nat.pair (evalp O cf x) (evalp O cg x)
| comp cf cg => λ x ↦ evalp O cf (evalp O cg x)
| prec cf cg => unpaired fun z n => n.rec (evalp O cf z) fun y IH => (evalp O cg) (z.pair (y.pair IH))
| rfind' _   => λ _ ↦ 0
theorem evalp_eq_eval (h:code_prim c):evalp O c = eval O c := by
  induction h with
  | zero => exact rfl
  | succ => exact rfl
  | left => exact rfl
  | right => exact rfl
  | oracle => exact rfl
  | pair ha hb ha_ih hb_ih =>
    unfold evalp
    simp [eval]
    funext xs
    simp [Seq.seq]
    expose_names
    simp only [show eval O a xs = Part.some (evalp O a xs) from by exact congrFun (_root_.id (Eq.symm ha_ih)) xs]
    simp only [show eval O b xs = Part.some (evalp O b xs) from by exact congrFun (_root_.id (Eq.symm hb_ih)) xs]
    simp
  | comp ha hb ha_ih hb_ih =>
    unfold evalp
    simp [eval]
    funext xs
    simp
    expose_names
    simp only [show eval O b xs = Part.some (evalp O b xs) from by exact congrFun (_root_.id (Eq.symm hb_ih)) xs]
    simp
    simp only [show eval O a (evalp O b xs) = Part.some (evalp O a (evalp O b xs)) from by exact congrFun (_root_.id (Eq.symm ha_ih)) (evalp O b xs)]
  | prec ha hb ha_ih hb_ih =>
    unfold evalp
    simp [eval]
    funext xs
    simp
    expose_names
    induction xs.r with
    | zero =>
      simp
      simp only [show eval O a xs.l = Part.some (evalp O a xs.l) from by exact congrFun (_root_.id (Eq.symm ha_ih)) xs.l]
    | succ y' IH' =>
      have h0:@Nat.rec (fun x ↦ Part ℕ) (eval O a xs.l) (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair xs.l (Nat.pair y i))) (y'+1) = ((@Nat.rec (fun x ↦ Part ℕ) (eval O a xs.l)
  (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair xs.l (Nat.pair y i))) y').bind fun i ↦ eval O b (Nat.pair xs.l (Nat.pair y' i))) := by
        exact rfl
      rw [h0]
      rw [←IH']
      rw [Part.bind_some]
      simp
      rw [show eval O b ((Nat.pair xs.l (Nat.pair y' (Nat.rec (evalp O a xs.l) (fun y IH ↦ evalp O b (Nat.pair xs.l (Nat.pair y IH))) y')))) = Part.some (evalp O b ((Nat.pair xs.l (Nat.pair y' (Nat.rec (evalp O a xs.l) (fun y IH ↦ evalp O b (Nat.pair xs.l (Nat.pair y IH))) y'))))) from by exact congrFun (_root_.id (Eq.symm hb_ih)) ((Nat.pair xs.l (Nat.pair y' (Nat.rec (evalp O a xs.l) (fun y IH ↦ evalp O b (Nat.pair xs.l (Nat.pair y IH))) y'))))]
theorem evalp_eq_eval_ext (h:code_prim c): eval O c x = evalp O c x := congrFun (_root_.id (Eq.symm (@evalp_eq_eval c O h))) x
@[simp 1000] theorem code_prim_prop : Nat.PrimrecIn O (evalp O c) := by
  induction c with
  | zero => exact Nat.PrimrecIn.zero
  | succ => exact Nat.PrimrecIn.succ
  | left => exact Nat.PrimrecIn.left
  | right => exact Nat.PrimrecIn.right
  | oracle => exact Nat.PrimrecIn.oracle
  | pair ha hb ha_ih hb_ih => unfold evalp; exact Nat.PrimrecIn.pair (ha_ih) (hb_ih)
  | comp ha hb ha_ih hb_ih => unfold evalp; exact Nat.PrimrecIn.comp (ha_ih) (hb_ih)
  | prec ha hb ha_ih hb_ih => unfold evalp; exact Nat.PrimrecIn.prec (ha_ih) (hb_ih)
  | rfind' ha ha_ih => exact Nat.PrimrecIn.zero
theorem code_prim_of_primrecIn (h:Nat.PrimrecIn O f) : ∃ c, code_prim c ∧ f=evalp O c := by
  induction h with
  | zero => use Code.zero; exact ⟨code_prim.zero,rfl⟩
  | succ => use Code.succ; exact ⟨code_prim.succ,rfl⟩
  | left => use Code.left; exact ⟨code_prim.left,rfl⟩
  | right => use Code.right; exact ⟨code_prim.right,rfl⟩
  | oracle => use Code.oracle; exact ⟨code_prim.oracle,rfl⟩
  | pair pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.pair cf cg;
    constructor
    · exact code_prim.pair hcf.left hcg.left
    · simp only [evalp]; rw [hcf.right, hcg.right]
  | comp pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.comp cf cg;
    constructor
    · exact code_prim.comp hcf.left hcg.left
    · simp only [evalp]; rw [hcf.right, hcg.right]
  | prec pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.prec cf cg;
    constructor
    · exact code_prim.prec hcf.left hcg.left
    · simp only [evalp]; rw [hcf.right, hcg.right]
end Computability.Code
end primrec

section total
namespace Computability.Code
def evalt (O:ℕ→ℕ) (c:Code) (h:code_total O c) : ℕ→ℕ := λ x ↦ (eval O c x).get (h x)
theorem total_pair_iff : (code_total O cf) ∧ (code_total O cg) ↔ (code_total O (pair cf cg)) :=
  ⟨
    λ h x ↦ ⟨h.left x, h.right x⟩
  ,
    λ h ↦ ⟨λ x ↦ Part.left_dom_of_sub_dom (h x) , λ x ↦ Part.right_dom_of_div_dom (h x)⟩
  ⟩
@[simp] theorem total_pair_of (hcf : code_total O cf) (hcg : code_total O cg) : (code_total O (pair cf cg)) := total_pair_iff.mp ⟨hcf,hcg⟩
theorem total_comp_of (hcf : code_total O cf) (hcg : code_total O cg) : (code_total O (comp cf cg)) := by
  intro x
  simp [eval]
  use hcg x
  exact hcf ((eval O cg x).get (hcg x))
@[simp] theorem total_of_pair_left {O} (h:code_total O (pair cf cg)) : code_total O cf :=
  (total_pair_iff.mpr h).left
@[simp] theorem total_of_pair_right {O} (h:code_total O (pair cf cg)) : code_total O cg :=
  (total_pair_iff.mpr h).right
@[simp] theorem total_of_comp_left {O} (h:code_total O (comp cf cg)) : code_total O cg := by
  intro h2
  exact Part.Dom.of_bind (h h2)
@[simp] theorem total_of_comp_right {O} (h:code_total O (comp cf cg)) : ∀x, (eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).Dom := by
  exact fun x ↦ Part.right_dom_of_div_dom (h x)
@[simp] theorem total_of_prec_left {O} (h:code_total O (prec cf cg)) : code_total O cf := by
  intro x
  unfold code_total at h
  simp [eval] at h
  have hx := h (Nat.pair x 0)
  simp at hx
  exact hx
theorem eval_total_comp (h:code_total O (comp cf cg)) :
  eval O (comp cf cg) x = Part.some ((eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).get (total_of_comp_right h x)) := by
    simp
    simp [eval]
    exact Part.Dom.bind (Part.Dom.of_bind (h x)) (eval O cf)
end Computability.Code
end total

namespace Computability.Code
@[simp 1000] theorem RecursiveIn_of_eval : Nat.RecursiveIn O (eval O c) := by
  induction c with
  | zero => exact Nat.RecursiveIn.zero
  | succ => exact Nat.RecursiveIn.succ
  | left => exact Nat.RecursiveIn.left
  | right => exact Nat.RecursiveIn.right
  | oracle => exact Nat.RecursiveIn.oracle
  | pair ha hb ha_ih hb_ih => unfold eval; exact Nat.RecursiveIn.pair (ha_ih) (hb_ih)
  | comp ha hb ha_ih hb_ih => unfold eval; exact Nat.RecursiveIn.comp (ha_ih) (hb_ih)
  | prec ha hb ha_ih hb_ih => unfold eval; exact Nat.RecursiveIn.prec (ha_ih) (hb_ih)
  | rfind' ha ha_ih => unfold eval; exact RecursiveIn.rfind ha_ih

end Computability.Code
