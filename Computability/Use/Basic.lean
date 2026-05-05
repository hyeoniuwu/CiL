/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Basic
import Computability.Helper.Partial
import Computability.Helper.List
import Computability.Use.Helper
import Mathlib.Tactic.Linarith

/-!
# Use.lean

In this file we specify the use function. In particular, we implement the *exact* use function,
which returns exactly the greatest natural queried during a computation (using `eval`), wrapped in
an option type. (If no naturals are queried, `Option.none` is returned.)

We first define the `usen` function, which acts like the `use` function for computations with
bounded steps (corresponding to `evaln`). As was done for `evaln` and `eval`, we prove
soundness/completeness/monotonicity of `usen` with respect to `use`, yielding a normal form theorem
analogous to that of `evaln`.

The main result is the use principle, which states that two different oracles that agree up to the
use of a computation, may be interchanged in a computation without changing its result.

For the construction of the use function given here, see Constructions/Use.lean.

## Main declarations

- `usen`: use function for computations with bounded steps.
- `use`: use function.
- `usen_mono`: theorem asserting monotonicity of `usen` w.r.t steps.
- `usen_sound`: theorem asserting soundness of `usen` w.r.t `use`.
- `usen_complete`: theorem asserting completeness of `usen` w.r.t `use`.
- `usen_princple`: the use principle, for computations with bounded steps.
- `use_principle`: the use principle.

## Structure

`usen_none_iff_evaln_none`
`use_dom_iff_eval_dom` : asserts that

## Notation/quirks

 - Where `x`, `y` are naturals, `⟪x, y⟫ = Nat.pair x y`.

## References

-/
open List Nat
open Oracle.Single.Code
namespace Oracle.Single.Code


-- /--
-- we define the use `max(all naturals queried to the oracle)+1`
-- use=0 when no queries are made.
-- use=none when the computation diverges.
-- -/
open Classical in
noncomputable def use (O : ℕ → ℕ) (c : Code) (x : ℕ) : Part ℕ :=
match c with
| zero        => Part.some (0)
| succ        => Part.some (0)
| left        => Part.some (0)
| right       => Part.some (0)
| oracle      => Part.some (x+1)
| pair cf cg  => Nat.max <$> (use O cf x) <*> (use O cg x)
| comp cf cg  => Nat.max <$> (use O cg x) <*> (eval O cg x >>= use O cf)
| prec cf cg  =>
  let (xl, i) := Nat.unpair x
  i.rec (use O cf xl)
  fun iM1 IH => do
    let IH_N ← eval O (prec cf cg) ⟪xl, iM1⟫;
    Nat.max <$> IH <*> use O cg (Nat.pair xl (Nat.pair iM1 IH_N))
| Code.rfind' cf =>
  do
    let guard ← eval O (rfind' cf) x;
    let ro := guard - x.r
    let mut max := 0
    for i in List.reverse (List.range (ro+1)) do
      let use_i ← (use O cf ⟪x.l, i+x.r⟫)
      max := Nat.max max use_i
    max
/-- `usen; the use of [c : O]ₛ(x)` -/
def usen (O : ℕ → ℕ) (c : Code) (s : ℕ) : ℕ → Option ℕ :=
match c,s with
| _, 0            => fun _ ↦ Option.none
| zero      , s + 1 => fun x ↦ do guard (x ≤ s); return 0
| succ      , s + 1 => fun x ↦ do guard (x ≤ s); return 0
| left      , s + 1 => fun x ↦ do guard (x ≤ s); return 0
| right     , s + 1 => fun x ↦ do guard (x ≤ s); return 0
| oracle    , s + 1 => fun x ↦ do guard (x ≤ s); return x+1
| pair cf cg, s + 1 => fun x ↦
  do
    guard (x ≤ s);
    let usen_cf ← usen O cf (s + 1) x
    let usen_cg ← usen O cg (s + 1) x
    return Nat.max usen_cf usen_cg
| comp cf cg, s + 1  => fun x ↦
  do
    guard (x ≤ s);
    let usen_cg  ← usen O cg (s + 1) x
    let evaln_cg ← evaln O (s + 1) cg x
    let usen_cf  ← usen O cf (s + 1) evaln_cg
    return Nat.max usen_cf usen_cg
| prec cf cg, s + 1 => fun x ↦ do
  guard (x ≤ s);
  let (xl, i) := Nat.unpair x
  (i.casesOn
  (usen O cf (s + 1) xl)
  fun iM1 =>
  do
    let usen_prev  ← usen  O (prec cf cg) s ⟪xl, iM1⟫
    let evaln_prev ← evaln O s (prec cf cg) ⟪xl, iM1⟫
    let usen_indt  ← usen  O cg (s + 1) (Nat.pair xl (Nat.pair iM1 evaln_prev))
    return Nat.max usen_prev usen_indt)
| rfind' cf, s + 1 => fun x ↦
  do
    guard (x ≤ s);
    let usen_base  ← usen O cf (s + 1) x
    let evaln_base ← evaln O (s + 1) cf x
    if evaln_base=0 then usen_base else
    let usen_indt  ← usen O (rfind' cf) s ⟪x.l, x.r+1⟫
    Nat.max usen_base usen_indt
end Oracle.Single.Code
