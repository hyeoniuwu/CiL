import Computability.Oracle
import Mathlib.Order.Antisymmetrization

@[simp] abbrev TuringReducible (f g : ℕ → ℕ) : Prop := Nat.RecursiveIn g f
@[simp] abbrev TuringReducibleStrict (f g : ℕ → ℕ) : Prop := Nat.RecursiveIn g f ∧ ¬ Nat.RecursiveIn f g
@[simp] abbrev TuringEquivalent (f g : ℕ → ℕ) : Prop := AntisymmRel TuringReducible f g

@[reducible,simp,inherit_doc] scoped[Computability] infix:50 " ≤ᵀᶠ " => TuringReducible
@[reducible,simp,inherit_doc] scoped[Computability] infix:50 " ≡ᵀᶠ " => TuringEquivalent
@[reducible,simp,inherit_doc] scoped[Computability] infix:50 " <ᵀᶠ " => TuringReducibleStrict

open scoped Computability

protected theorem TuringReducible.refl (f : ℕ → ℕ) : f ≤ᵀᶠ f := by exact Nat.RecursiveIn.oracle
protected theorem TuringReducible.rfl : f ≤ᵀᶠ f := .refl _

instance : IsRefl (ℕ → ℕ) TuringReducible where refl _ := .rfl

theorem TuringReducible.trans (hg : f ≤ᵀᶠ g) (hh : g ≤ᵀᶠ h) : f ≤ᵀᶠ h := by
  generalize z : (↑f:ℕ→.ℕ)=x at hg
  simp only [TuringReducible,z] at *
  induction hg with
  | zero => exact Nat.RecursiveIn.zero
  | succ => exact Nat.RecursiveIn.succ
  | left => exact Nat.RecursiveIn.left
  | right => exact Nat.RecursiveIn.right
  | oracle => exact hh
  | pair hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.pair hf_ih hh_ih)
  | comp hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.comp hf_ih hh_ih)
  | prec hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.prec hf_ih hh_ih)
  | rfind hf ih => (expose_names; exact Nat.RecursiveIn.rfind ih)

theorem TuringReducible.trans' (hg : Nat.RecursiveIn g f) (hh : g ≤ᵀᶠ h) : Nat.RecursiveIn h f := by
  generalize z : (↑f:ℕ→.ℕ)=x at hg
  simp only [TuringReducible,z] at *
  induction hg with
  | zero => exact Nat.RecursiveIn.zero
  | succ => exact Nat.RecursiveIn.succ
  | left => exact Nat.RecursiveIn.left
  | right => exact Nat.RecursiveIn.right
  | oracle => exact hh
  | pair hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.pair hf_ih hh_ih)
  | comp hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.comp hf_ih hh_ih)
  | prec hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.prec hf_ih hh_ih)
  | rfind hf ih => (expose_names; exact Nat.RecursiveIn.rfind ih)

instance : IsTrans (ℕ→ℕ) TuringReducible := ⟨@TuringReducible.trans⟩
instance : IsPreorder (ℕ→ℕ) TuringReducible where refl := .refl
theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent := (AntisymmRel.setoid _ _).iseqv
@[refl] protected theorem TuringEquivalent.refl (f : ℕ→ℕ) : f ≡ᵀᶠ f := Equivalence.refl equivalence f
@[symm] theorem TuringEquivalent.symm {f g : ℕ→ℕ} (h : f ≡ᵀᶠ g) : g ≡ᵀᶠ f := Equivalence.symm equivalence h
@[trans] theorem TuringEquivalent.trans {f g h : ℕ→ℕ} (h₁ : f ≡ᵀᶠ g) (h₂ : g ≡ᵀᶠ h) : f ≡ᵀᶠ h := Equivalence.trans equivalence h₁ h₂

/--
Instance declaring that `Nat.RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ→ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

abbrev FuncTuringDegree :=
  Antisymmetrization _ TuringReducible
private instance : Preorder (ℕ→ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans
  lt := TuringReducibleStrict
