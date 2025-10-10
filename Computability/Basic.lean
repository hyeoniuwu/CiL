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



-- helper funcs:

-- @[simp] lemma Nat.RecursiveIn.partCompTotal {O:ℕ→ℕ} {f:ℕ→.ℕ} {g:ℕ→ℕ} (h1: Nat.RecursiveIn O f) (h2: Nat.RecursiveIn O g):(Nat.RecursiveIn O ↑(f∘g)) := by
--   have h3:(↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
--     funext xs
--     simp only [Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
--   rw [h3]
--   exact comp h1 h2
-- @[simp] lemma Nat.RecursiveIn.totalComp {O:ℕ→ℕ} {f g:ℕ→ℕ} (h1: Nat.RecursiveIn O f) (h2: Nat.RecursiveIn O g):(Nat.RecursiveIn O ↑(f∘g)) := by
--   have h3:(↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
--     funext xs
--     simp only [PFun.coe_val, Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
--   rw [h3]
--   exact comp h1 h2
-- @[simp] lemma Nat.RecursiveIn.id {O:ℕ→ℕ}:Nat.RecursiveIn O fun x => x := by apply of_primrec Nat.Primrec.id
-- @[simp] lemma Nat.RecursiveIn.someTotal (O:ℕ→ℕ) (f:ℕ→ℕ) (h1: Nat.RecursiveIn O f): Nat.RecursiveIn O fun x => Part.some (f x) := by
--   apply Nat.RecursiveIn.totalComp
--   · exact h1
--   · apply Nat.RecursiveIn.id
-- @[simp] lemma Nat.RecursiveIn.pair' (f g:ℕ→ℕ):((↑fun x ↦ Nat.pair (f x) (g x)):ℕ→.ℕ)= fun (x:ℕ) => (Nat.pair <$> (f x) <*> (g x)) := by
--   simp [Seq.seq]
--   funext xs
--   simp only [PFun.coe_val]
-- @[simp] lemma Nat.RecursiveIn.totalComp' {O:ℕ→ℕ} {f g:ℕ→ℕ} (hf: Nat.RecursiveIn O f) (hg: Nat.RecursiveIn O g): (Nat.RecursiveIn O (fun x => (f (g x)):ℕ→ℕ) ) := by apply Nat.RecursiveIn.totalComp (hf) (hg)
-- @[simp] lemma Nat.RecursiveIn.comp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→.ℕ} {g h:ℕ→ℕ} (hf: Nat.RecursiveIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.RecursiveIn O g) (hh: Nat.RecursiveIn O h): (Nat.RecursiveIn O (fun x => (f (g x) (h x))) ) := by
--   have main:(fun x => (f (g x) (h x))) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
--     funext xs
--     simp only [Function.comp_apply, unpair_pair]
--   rw [main]
--   refine partCompTotal hf ?_
--   · rw [Nat.RecursiveIn.pair']
--     apply Nat.RecursiveIn.pair hg hh
-- @[simp] lemma Nat.RecursiveIn.totalComp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→ℕ} {g h:ℕ→ℕ} (hf: Nat.RecursiveIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.RecursiveIn O g) (hh: Nat.RecursiveIn O h): (Nat.RecursiveIn O (fun x => (f (g x) (h x)):ℕ→ℕ) ) := by
--   have main:(fun x => (f (g x) (h x)):ℕ→ℕ) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
--     funext xs
--     simp only [Function.comp_apply, Nat.unpair_pair]
--   rw [main]
--   apply Nat.RecursiveIn.totalComp
--   · exact hf
--   · rw [Nat.RecursiveIn.pair']
--     apply Nat.RecursiveIn.pair hg hh

-- @[simp] lemma Nat.PrimrecIn.totalComp {O:ℕ→ℕ} {f g:ℕ→ℕ} (h1: Nat.PrimrecIn O f) (h2: Nat.PrimrecIn O g):(Nat.PrimrecIn O ↑(f∘g)) := by
--   rw [show (f∘g) = fun x => f (g x) from rfl]
--   exact comp h1 h2
-- @[simp] lemma Nat.PrimrecIn.comp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→ℕ} {g h:ℕ→ℕ} (hf: Nat.PrimrecIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.PrimrecIn O g) (hh: Nat.PrimrecIn O h): (Nat.PrimrecIn O (fun x => (f (g x) (h x)):ℕ→ℕ) ) := by
--   have main:(fun x => (f (g x) (h x)):ℕ→ℕ) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
--     funext xs
--     simp only [Function.comp_apply, Nat.unpair_pair]
--   rw [main]
--   apply Nat.PrimrecIn.totalComp
--   · exact hf
--   · apply Nat.PrimrecIn.pair hg hh
