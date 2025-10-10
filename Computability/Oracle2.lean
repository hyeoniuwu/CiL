import Mathlib.Data.Nat.Pairing
import Mathlib.Data.PFun
import Mathlib.Computability.Partrec

open Part

namespace Nat

-- inductive RecursiveIn (O : ℕ → ℕ) : (ℕ →. ℕ) → Prop
--   | zero : RecursiveIn O fun _ => 0
--   | succ : RecursiveIn O Nat.succ
--   | left : RecursiveIn O fun n => (Nat.unpair n).1
--   | right : RecursiveIn O fun n => (Nat.unpair n).2
--   | oracle : RecursiveIn O O
--   | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
--       RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
--   | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
--       RecursiveIn O fun n => h n >>= f
--   | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
--       RecursiveIn O fun p =>
--         let (a, n) := Nat.unpair p
--         n.rec (f a) fun y IH => do
--           let i ← IH
--           h (Nat.pair a (Nat.pair y i))
--   | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
--       RecursiveIn O fun a =>
--         Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)
inductive RecursiveIn (O : ℕ → ℕ) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : RecursiveIn O O
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O
        -- fun a =>
        $ Nat.unpaired fun a m =>
          (Nat.rfind fun n => (fun x => x = 0) <$> f (Nat.pair a (n + m))).map (· + m)

/-- The primitive recursive functions `ℕ → ℕ`. -/
protected inductive PrimrecIn (O:ℕ→ℕ) : (ℕ → ℕ) → Prop
  | zero : Nat.PrimrecIn O fun _ => 0
  | protected succ : Nat.PrimrecIn O succ
  | left : Nat.PrimrecIn O fun n => n.unpair.1
  | right : Nat.PrimrecIn O fun n => n.unpair.2
  | oracle : Nat.PrimrecIn O O
  | pair {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => pair (f n) (g n)
  | comp {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => f (g n)
  | prec {f g} :
      Nat.PrimrecIn O f →
        Nat.PrimrecIn O g →
          Nat.PrimrecIn O (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

end Nat
