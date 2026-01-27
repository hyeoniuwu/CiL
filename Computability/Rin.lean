/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Jump

namespace Nat.RecursiveIn.Rin
open Part

alias zero   := _root_.Nat.RecursiveIn.zero
alias succ   := _root_.Nat.RecursiveIn.succ
alias left   := _root_.Nat.RecursiveIn.left
alias right  := _root_.Nat.RecursiveIn.right
alias oracle := _root_.Nat.RecursiveIn.oracle
alias pair   := _root_.Nat.RecursiveIn.pair
alias comp   := _root_.Nat.RecursiveIn.comp
alias prec   := _root_.Nat.RecursiveIn.prec
alias rfind  := _root_.Nat.RecursiveIn.rfind

theorem of_eq {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (H : ∀ n, f n = g n) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : RecursiveIn O f) (H : ∀ n, g n ∈ f n) : RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)
theorem of_primrecIn {f : ℕ → ℕ} (hf : Nat.PrimrecIn O f) : RecursiveIn O f := by
  induction hf with
  | zero => exact zero
  | succ => exact succ
  | left => exact left
  | right => exact right
  | oracle => exact oracle
  | pair _ _ pf pg =>
    refine of_eq_tot (pair pf pg) fun n => ?_
    simp [Seq.seq]
  | comp _ _ pf pg =>
    refine of_eq_tot (comp pf pg) fun n => (by simp)
  | prec _ _ pf pg =>
    refine of_eq_tot (prec pf pg) fun n => ?_
    simp only [unpaired, PFun.coe_val, bind_eq_bind]
    induction n.unpair.2 with
    | zero => simp
    | succ m IH =>
      simp only [mem_bind_iff, mem_some_iff]
      exact ⟨_, IH, rfl⟩

@[simp] lemma partCompTotal {O:ℕ→ℕ} {f:ℕ→.ℕ} {g:ℕ→ℕ} (h1: Nat.RecursiveIn O f) (h2: Nat.RecursiveIn O g):(Nat.RecursiveIn O ↑(f∘g)) := by
  have h3:(↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
    funext xs
    simp only [Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [h3]
  exact comp h1 h2
@[simp] lemma totalComp {O:ℕ→ℕ} {f g:ℕ→ℕ} (h1: Nat.RecursiveIn O f) (h2: Nat.RecursiveIn O g):(Nat.RecursiveIn O ↑(f∘g)) := by
  have h3:(↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
    funext xs
    simp only [PFun.coe_val, Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [h3]
  exact comp h1 h2
@[simp] lemma id {O:ℕ→ℕ}:Nat.RecursiveIn O fun x => x := by apply of_primrecIn Nat.PrimrecIn.id
@[simp] lemma someTotal (O:ℕ→ℕ) (f:ℕ→ℕ) (h1: Nat.RecursiveIn O f): Nat.RecursiveIn O fun x => Part.some (f x) := by
  apply totalComp
  · exact h1
  · apply id
@[simp] lemma pair' (f g:ℕ→ℕ):((↑fun x ↦ Nat.pair (f x) (g x)):ℕ→.ℕ)= fun (x:ℕ) => (Nat.pair <$> (f x) <*> (g x)) := by
  simp [Seq.seq]
  funext xs
  simp only [PFun.coe_val]
@[simp] lemma totalComp' {O:ℕ→ℕ} {f g:ℕ→ℕ} (hf: Nat.RecursiveIn O f) (hg: Nat.RecursiveIn O g): (Nat.RecursiveIn O (fun x => (f (g x)):ℕ→ℕ) ) := by apply totalComp (hf) (hg)
@[simp] lemma comp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→.ℕ} {g h:ℕ→ℕ} (hf: Nat.RecursiveIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.RecursiveIn O g) (hh: Nat.RecursiveIn O h): (Nat.RecursiveIn O (fun x => (f (g x) (h x))) ) := by
  have main:(fun x => (f (g x) (h x))) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, unpair_pair]
  rw [main]
  refine partCompTotal hf ?_
  · rw [pair']
    apply pair hg hh
@[simp] lemma totalComp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→ℕ} {g h:ℕ→ℕ} (hf: Nat.RecursiveIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.RecursiveIn O g) (hh: Nat.RecursiveIn O h): (Nat.RecursiveIn O (fun x => (f (g x) (h x)):ℕ→ℕ) ) := by
  have main:(fun x => (f (g x) (h x)):ℕ→ℕ) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [main]
  apply totalComp
  · exact hf
  · rw [pair']
    apply pair hg hh

@[simp] lemma Nat.PrimrecIn.totalComp {O:ℕ→ℕ} {f g:ℕ→ℕ} (h1: Nat.PrimrecIn O f) (h2: Nat.PrimrecIn O g) : Nat.PrimrecIn O ↑(f∘g) := by
  rw [show (f∘g) = fun x => f (g x) from rfl]
  exact PrimrecIn.comp h1 h2
@[simp] lemma Nat.PrimrecIn.comp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→ℕ} {g h:ℕ→ℕ} (hf: Nat.PrimrecIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.PrimrecIn O g) (hh: Nat.PrimrecIn O h): (Nat.PrimrecIn O (fun x => (f (g x) (h x)):ℕ→ℕ) ) := by
  have main:(fun x => (f (g x) (h x)):ℕ→ℕ) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [main]
  apply Nat.PrimrecIn.totalComp
  · exact hf
  · apply Nat.PrimrecIn.pair hg hh

open Computability
open Computability.Code
theorem _root_.Nat.RecursiveIn.eval_K_computable:Nat.RecursiveIn O (fun x ↦ Computability.eval O x x) := by
  have h:(fun (x:ℕ) ↦ Computability.eval O x x) = (fun (x:ℕ) => Computability.eval O x.unpair.1 x.unpair.2) ∘ (fun x=>Nat.pair x x) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [h]
  refine Nat.RecursiveIn.Rin.partCompTotal ?_ ?_
  exact rec_eval₁
  exact Nat.RecursiveIn.Rin.of_primrecIn (Nat.PrimrecIn.pair Nat.PrimrecIn.id Nat.PrimrecIn.id)

end Nat.RecursiveIn.Rin
namespace Computability.Code
def c_pair_proj (x:ℕ) : Code := pair (c_const x) c_id
theorem c_pair_proj_evp : evalp O (c_pair_proj x) = Nat.pair x := by simp [c_pair_proj]
lemma _root_.Nat.PrimrecIn.pair_proj : Nat.PrimrecIn O (Nat.pair x) := by
  rw [←c_pair_proj_evp]
  exact code_prim_prop
