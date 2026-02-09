/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.SetOracles
import Computability.Constructions.EvalString

/-!
# KP54.lean

In this file we specify the construction procedure in the KP54 proof, and show that the sets it defines are incomparable.

## Structure

In section `finite_ext`, we define the procedure for finding the finite extension of a string such that it allows a certain computation
to halt.

We then define the main construction procedure, `KP54`, and the corresponding sets it builds by stage `s`, `As s` and `Bs s`.

In section `AsBs_Mono`, we prove various theorems about the growth of the set with respect to the stage. In particular, `AsBsSize` shows that the sets have at least `s` elements by stage `s`, allowing us to define the completed sets `A` and `B`.

Finally, we prove the requirements `R` and `S` in sections R and S respectively.

## Main declarations

- `KP54.KP54`: a function which takes the stage as input, and returns the sets built up to that stage.
- `KP54.A`, `KP54.B`: The sets built by the construction procedure.
- `KP54.R`: requirement R, asserting that `B` is not reducible to `A`.
- `KP54.S`: requirement S, asserting that `A` is not reducible to `B`.

## Notation/quirks

 - Where `x`, `y` are naturals, `⟪x, y⟫ = Nat.pair x y`.

## References

* Cooper 2004, Computability Theory section 10.6

-/

open Computability.Code
open Classical
open Computability
open Nat

namespace Computability.Code

end Computability.Code

set_option linter.dupNamespace false
namespace KP54

section finite_ext
/-!
We define the procedure of finding a finite extension explicitly as a code, as it is simpler this way.

The reason is that the search procedure has to involve dovetailing, and our dovetail implementation depends fundamentally on the code that is being dovetailed.

So, there would be extra 'unnecessary' work involved to remove any codes in the definition of `finite_ext`.

### Structure
We define `c_kp54_aux` which checks whether a something is a valid finite extension or not.

Then we can define the search procedure for a finite extension, `finite_ext`, via dovetailing `c_kp54_aux`.

-/

/--
[c_kp54_aux i n](x,y) checks if `y` is a finite extension to `x` for the computation [i](n).

That is,
[c_kp54_aux i n](x,y):
  let list = x ++ y.
  if [i:list](n) halts, then return 0 else diverge.

Later simp calls blow up without `@[irreducible]`. Why?
-/
@[irreducible] def c_kp54_aux (i n:ℕ) :=
  c_ifdom
  (c_evals.comp₃ (c_list_append.comp₂ left (succ.comp right)) (c_const i) (c_const n))
  Code.zero
theorem c_kp54_aux_evp :
  eval (λ_↦0) (c_kp54_aux i n) x
    =
  if (evals (x.l.n2l ++ (x.r+1).n2l) i n).Dom then Part.some 0 else Part.none
:= by
  simp [c_kp54_aux, -Denumerable.list_ofNat_succ]
  simp [Computability.eval, -Denumerable.list_ofNat_succ]
  simp [Seq.seq, -Denumerable.list_ofNat_succ]
/--
`finite_ext S i l` gives `x` s.t. `[i:S++x](l)↓`.

If no such `x` exists, returns `Part.none`.
-/
def finite_ext (S i n) := eval (λ_↦0) (dovetail (c_kp54_aux i n)) S
theorem finite_ext_prop (halts:(finite_ext S i n).Dom) :
  have dvt := (finite_ext S i n).get halts
  (evals ((n2l S) ++ (n2l (dvt+1))) i n).Dom := by
    have := dovetail_ev_0 halts
    extract_lets at this ⊢
    expose_names
    simp only [c_kp54_aux_evp] at this
    contrapose this
    simp [-Denumerable.list_ofNat_succ]
    exact this
theorem finite_ext_prop_div (h: ¬ (finite_ext S i n).Dom) :
  ∀ y, ¬ (evals ((n2l S) ++ (n2l (y+1))) i n).Dom := by
    have := dovetail_ev_1.mp (Part.eq_none_iff'.mpr h)
    simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at this
    exact fun y ↦ this y
end finite_ext

open Nat List in
/--
The construction procedure in the KP54 proof.

Input: stage `s`
Output: (string `αₛ`, string `βₛ`)

(The strings are encoded as a list of naturals.)

Each string `αₛ` and `βₛ` increase in length by at least 1 every stage.
-/
noncomputable def KP54 : ℕ → ℕ := λ s ↦
match s with
| 0 => ⟪0, 0⟫
| s+1 =>
  let i  := s.div2
  let αₚ := (KP54 s).l
  let βₚ := (KP54 s).r
  let lb := βₚ.n2l.length
  let la := αₚ.n2l.length

  if (s+1)%2=0 then -- then s+1=2i+2, and we will work on Rᵢ.
    let dvt := finite_ext αₚ i lb -- this is the step where we search for a finite extension.
    if halts : dvt.Dom then
      let rf := dvt.get halts -- rf is a natural such that (evals (αₚ ++ (rf+1)) i n).Dom.
      let αₛ := αₚ.n2l ++ (rf+1).n2l
      let A_result := (evals αₛ i lb).get (finite_ext_prop halts)
      Nat.pair αₛ (βₚ.n2l.concat (Nat.sg' A_result))
    else -- if there is no finite extension, extend both strings by 0
      Nat.pair (αₚ.n2l.concat 0) (βₚ.n2l.concat 0)
  else -- then s+1=2i+1, and we will work on Sᵢ.
    let dvt := finite_ext βₚ i la
    if halts : dvt.Dom then
      let rf := dvt.get halts
      let βₛ := βₚ.n2l ++ (rf+1).n2l
      let B_result := (evals (βₛ) i la).get (finite_ext_prop halts)
      Nat.pair (αₚ.n2l.concat (Nat.sg' B_result)) βₛ
    else
      Nat.pair (αₚ.n2l.concat 0) (βₚ.n2l.concat 0)
@[simp] theorem KP54_0_r : n2l (KP54 0).r = [] := by simp [KP54]
@[simp] theorem KP54_0_l : n2l (KP54 0).l = [] := by simp [KP54]

noncomputable def As (s:ℕ) := n2l (KP54 s).l
noncomputable def Bs (s:ℕ) := n2l (KP54 s).r

section AsBs_Mono
-- We prove a bunch of theorems about the monotonicity of growth of the strings `As` and `Bs`, and their sizes.
theorem AsBs_Mono_0 : (As i) <+: (As (i+1)) ∧ (Bs i) <+: (Bs (i+1)) := by
  unfold As
  unfold Bs
  rw (config:={occs:=.pos [1,2]}) [KP54]
  simp (config := {zeta:=false}) [-Nat.rfind_dom]
  if h0 : (i+1) % 2 = 0 then
    simp [h0,-Nat.rfind_dom]
    split <;> simp
  else
    simp [h0,-Nat.rfind_dom]
    split <;> simp
theorem AsBs_Mono_1 : (As i) <+: (As (i+j)) ∧ (Bs i) <+: (Bs (i+j)) := by
  induction j with
  | zero => simp_all
  | succ jM1 ihj =>
    rw [←add_assoc]
    constructor
    exact List.IsPrefix.trans ihj.left (@AsBs_Mono_0 (i + jM1)).left
    exact List.IsPrefix.trans ihj.right (@AsBs_Mono_0 (i + jM1)).right
theorem AsBs_Mono_2 (h:i≤j) : (As i) <+: (As j) ∧ (Bs i) <+: (Bs j) := by
  rw [Eq.symm (Nat.add_sub_of_le h)]
  exact AsBs_Mono_1
theorem As_Mono_3 (hi:k<(As i).length) (hh:k<(As j).length) : (As i)[k] = (As j)[k] := by
  cases Classical.em (i≤j) with
  | inl h => exact List.IsPrefix.getElem ((AsBs_Mono_2 h).left) hi
  | inr h =>
    simp at h
    exact (List.IsPrefix.getElem (AsBs_Mono_2 (Nat.le_of_succ_le h)).left hh).symm
theorem Bs_Mono_3 (hi:k<(Bs i).length) (hh:k<(Bs j).length) : (Bs i)[k] = (Bs j)[k] := by
  cases Classical.em (i≤j) with
  | inl h => exact List.IsPrefix.getElem ((AsBs_Mono_2 h).right) hi
  | inr h =>
    simp at h
    have := (AsBs_Mono_2 (Nat.le_of_succ_le h)).right
    exact Eq.symm (List.IsPrefix.getElem this hh)
theorem As_Mono_4 (hii : ii < (As j).length) (asz : ii < (As k).length) :
((As j)[ii]?.getD smth) = (As k)[ii] := by
  have : (As j)[ii]?.getD smth = (As k)[ii] := by
    have : (As j)[ii]?.getD smth = (As j)[ii] := by simp only [getElem?_pos, Option.getD_some,hii]
    rw [this]
    exact As_Mono_3 hii asz
  rw [this]
theorem Bs_Mono_4 (hii : ii < (Bs j).length) (asz : ii < (Bs k).length) :
((Bs j)[ii]?.getD smth) = (Bs k)[ii] := by
  have : (Bs j)[ii]?.getD smth = (Bs k)[ii] := by
    have : (Bs j)[ii]?.getD smth = (Bs j)[ii] := by simp only [getElem?_pos, Option.getD_some,hii]
    rw [this]
    exact Bs_Mono_3 hii asz
  rw [this]
@[simp] private lemma AsBsSize_aux_0 : (2 * i + 1 + 1) % 2 = 0 := by omega
theorem AsSize_o2e : (As (2*i+1)).length = (As (2*i)).length + 1 := by
  rw [As, KP54]
  simp (config := {zeta:=false})
  extract_lets; expose_names
  if h0:dvt.Dom then simp [h0]; rfl
  else simp [h0]; rfl
theorem AsSize_e2o : (As (2*i+1)).length < (As (2*i+2)).length:= by
  rw (config:={occs:=.pos [2]}) [As]
  unfold KP54
  simp (config := {zeta:=false})
  extract_lets; expose_names
  rw [show As (2*i+1) = n2l αₚ from rfl]
  if h0:dvt.Dom then simp [h0]
  else simp [h0]
theorem BsSize_o2e : (Bs (2*i+2)).length = (Bs (2*i+1)).length + 1 := by
  rw [Bs, KP54]
  simp (config := {zeta:=false})
  extract_lets; expose_names
  if h0:dvt.Dom then simp [h0]; rfl
  else simp [h0]; rfl
theorem BsSize_e2o : (Bs (2*i)).length < (Bs (2*i+1)).length:= by
  rw (config:={occs:=.pos [2]}) [Bs]
  unfold KP54
  simp (config := {zeta:=false})
  extract_lets; expose_names
  rw [show Bs (2*i) = n2l βₚ from rfl]
  if h0:dvt.Dom then simp [h0]
  else simp [h0]

theorem AsSize_mono' : (As i).length < (As (i+1)).length := by
  cases Nat.even_or_odd i with
  | inl h =>
    rcases h with ⟨h1,h2⟩
    have a0 : i=2*h1 := by
      rw [h2]
      exact Eq.symm (Nat.two_mul h1)
    rw [a0]
    simp [@AsSize_o2e h1]
  | inr h =>
    rcases h with ⟨h1,h2⟩
    rw [h2]
    simp [@AsSize_e2o h1]
theorem AsSize_mono (hij:i<j) : (As i).length < (As j).length := by
  have a0 := @AsSize_mono' i
  have a1 := (@AsBs_Mono_2 (i+1) j (hij)).left
  exact Nat.lt_of_lt_of_le a0 (List.IsPrefix.length_le a1)
theorem append_len_geq (A B : List α) (h1 : A.length < B.length) (h2 : A ++ lst = B) : lst.length > 0 := by
  grind
theorem nonempt_l2n (A : List ℕ) (h1 : A.length > 0) : l2n A ≠ 0 := by
  contrapose h1
  simp at h1 ⊢
  apply Encodable.encode_inj.mp h1
theorem As_ex_ext (hij:i<j): ∃ lM1, (As i)++(n2l (lM1+1))=As j := by
  rcases (@AsBs_Mono_2 i j (Nat.le_of_succ_le hij)).left with ⟨h1,h2⟩
  have a2 : h1.length > 0 := append_len_geq (As i) (As j) (AsSize_mono hij) h2
  have a4 : (l2n h1)-1+1=l2n h1 := Nat.succ_pred_eq_of_ne_zero (nonempt_l2n h1 a2)
  use (l2n h1)-1
  simpa [a4]
theorem BsSize_mono' : (Bs i).length < (Bs (i+1)).length := by
  cases Nat.even_or_odd i with
  | inl h =>
    rcases h with ⟨h1,h2⟩
    have a0 : i=2*h1 := by
      rw [h2]
      exact Eq.symm (Nat.two_mul h1)
    rw [a0]
    simp [@BsSize_e2o h1]
  | inr h =>
    rcases h with ⟨h1,h2⟩
    rw [h2]
    simp [@BsSize_o2e h1]
theorem BsSize_mono (hij:i<j) : (Bs i).length < (Bs j).length := by
  have a0 := @BsSize_mono' i
  have a1 := (@AsBs_Mono_2 (i+1) j (hij)).right
  exact Nat.lt_of_lt_of_le a0 (List.IsPrefix.length_le a1)
theorem Bs_ex_ext (hij:i<j): ∃ lM1, (Bs i)++(n2l (lM1+1))=Bs j := by
  rcases (@AsBs_Mono_2 i j (Nat.le_of_succ_le hij)).right with ⟨h1,h2⟩
  have a2 : h1.length > 0 := append_len_geq (Bs i) (Bs j) (BsSize_mono hij) h2
  have a4 : (l2n h1)-1+1=l2n h1 := Nat.succ_pred_eq_of_ne_zero (nonempt_l2n h1 a2)
  use (l2n h1)-1
  simpa [a4]
theorem AsBsSize : i≤(As i).length ∧ i≤(Bs i).length := by
  induction i with
  | zero => exact ⟨Nat.zero_le (As 0).length, Nat.zero_le (Bs 0).length⟩
  | succ i ih =>
    unfold As
    unfold Bs
    unfold KP54
    simp (config := {zeta:=false}) [-Nat.rfind_dom]
    lift_lets
    extract_lets
    expose_names
    if h0:(i + 1) % 2 = 0 then
      simp [h0,-Nat.rfind_dom]
      if h1 : dvt.Dom  then
        simp [h1,-Nat.rfind_dom]
        constructor
        refine Nat.add_le_add ih.left ?_
        exact Nat.le_add_left 1 _
        exact ih.right
      else
        simp [h1,-Nat.rfind_dom]
        exact ih
    else
      simp [h0,-Nat.rfind_dom]
      if h1 : (dvt_1).Dom  then
        simp [h1,-Nat.rfind_dom]
        constructor
        exact ih.left
        refine Nat.add_le_add ih.right ?_
        exact Nat.le_add_left 1 _
      else
        simp [h1,-Nat.rfind_dom]
        exact ih

@[simp] theorem AsSize : i<(As (i+1)).length := (@AsBsSize (i+1)).left
@[simp] theorem BsSize : i<(Bs (i+1)).length := (@AsBsSize (i+1)).right

-- The "completed" sets `A` and `B`, defined from `As` and `Bs` noting that by stage `x+1`, index `x` is defined by the monotonicty theorems above.
-- The [x] 's require the theorems AsSize and BsSize above.
def A := { x | n2b (As (x+1))[x] }
def B := { x | n2b (Bs (x+1))[x] }
end AsBs_Mono

section R
/-
We wish to prove
`theorem R (i:ℕ) : eval A i ≠ χ B`.

We shall prove this with two auxiliary lemmas. The first, `R_aux_0`, states that for any $i\in\N$, $n=\sz{B_s(2i+1)}$ witnesses:
\begin{align}
	[i:A_{2i+2}](n)\ne \lss{n\in B_{2i+2}}.
\end{align}

We will define that witness as `R_wt`.

The second, `As_Uninjured`, states that the computation $[i:A_{2i+2}](x)$ will have its value unchanged through subsequent stages.

We split the proof into two cases, `As_Uninjured_0` and `As_Uninjured_1`, depending on whether the value halts or not (respectively).
-/

/-- R_wt i is the natural that witnesses the requirement `R i`. -/
private noncomputable def R_wt (i:ℕ) := (Bs (2*(i+1)-1)).length
@[simp] theorem BsSize_o2e_Rwt : R_wt i < (Bs (2 * (i + 1))).length := by
  rw [show R_wt i = (Bs (2*(i+1)-1)).length from rfl]
  have : 2 * (i + 1) - 1 = 2*i+1 := by exact rfl
  rw [this]
  have : 2*(i+1) = 2*i + 2:= by exact rfl
  rw [this]
  have := @BsSize_o2e i
  simp_all only [Nat.add_one_sub_one, lt_add_iff_pos_right, zero_lt_one]

/--
`R_aux_0` proves that `R_wt i` witnesses the failure of program `i` to be the characteristic function of `Bs`;
that [i:As](R_wt i) ≠ (R_wt i) ∈ Bs.

The proof follows easily from unravelling if-statements.
-/
private theorem R_aux_0 (i:ℕ) (h:(evals (As (2*i+1+1)) i (R_wt i)).Dom):
(evals (As (2*i+1+1)) i (R_wt i)).get h ≠ b2n (n2b $ (Bs (2*i+1+1))[R_wt i]'(@BsSize_o2e_Rwt i)) := by
  unfold Bs
  unfold As
  unfold KP54
  simp (config := {zeta:=false})
  simp (config := {zetaHave:=false}) only []
  -- memory blows up if i lift the non-have lets. why?

  lift_lets; extract_lets; expose_names
  have i_1_simp: i_1 = i := rfl
  let (eq:=hdvt) dvt := (finite_ext αₚ i_1 lb)
  simp (config := {zeta:=false}) only [←hdvt]

  -- if ¬ dvt.Dom, then our entire computation would have diverged, contradicting `h`.
  have halts : dvt.Dom := by
    apply byContradiction
    intro halts
    rcases @As_ex_ext (2*i+1) (2*i+2) (Nat.lt_add_one (2 * i + 1)) with ⟨h3,h2⟩
    have := finite_ext_prop_div halts h3
    rw [show n2l αₚ = As (2*i+1) from rfl, h2, i_1_simp] at this
    exact this h

  let (eq:=hrf) rf := dvt.get halts -- rf is a natural such that (eval_string ((n2l A) ++ (n2l rf)) i n).Dom.
  let (eq:=hαₛ) αₛ := (n2l αₚ) ++ (n2l (rf+1))
  simp (config := {zeta:=false}) only [←hrf, ←hαₛ, halts]
  simp (config := {zeta:=false}) []
  lift_lets; extract_lets; expose_names

  have lbrw : R_wt i = (n2l βₚ).length := rfl
  simp [lbrw]; simp only [←lbrw]
  simp [show (evals (αₛ) i (R_wt i)).get (finite_ext_prop halts) = A_result from rfl]
  cases A_result <;> simp [n2b,b2n]

theorem R_aux_χ: χ B (R_wt i) = b2n (n2b ((Bs (2 * (i + 1)))[(R_wt i)]'(@BsSize_o2e_Rwt i))) := by
  simp [B,χ]
  simp [Bs_Mono_3 (@BsSize (R_wt i)) (@BsSize_o2e_Rwt i)]
  exact rfl

/--
If `[i:As](k)` halts, then its value will be unchanged in all subsequent steps.

The proof follows from an invocation of the use principle. The monotonicity of As proves that the oracles are in-
deed equivalent up to the use.
-/
theorem As_Uninjured_0 (hh:(evals (As (2*(i+1))) i k).Dom): evals (As (2*(i+1))) i k = evalSet A i k := by
  simp [A,evalSet]; unfold χ; simp [evals] -- unfold defns

  have h1 := evalc_prop_0 hh
  simp at h1
  rw [h1]
  have hh2 := hh
  simp [evals, h1] at hh2
  apply use_principle_eval hh2
  intro ii hii
  rw [As_Mono_4 (Nat.lt_of_lt_of_le hii (evalc_prop_1 hh)) AsSize]
  split <;> next h => simp [b2n,h]

/- contrapositive of As_Uninjured_0. -/
theorem As_Uninjured_0' {i:ℕ} : ¬ (evalSet A i k).Dom → ¬ (evals (As (2*(i+1))) i k).Dom := by
  contrapose
  intro h
  rwa [←As_Uninjured_0 h]

/--
If `[i:As](k)` diverges, then it will always diverge in subsequent steps.

This is proven by contraposition; if the final computation converges, we must have found some finite extension.

If the final computation converges, it must have some finite use $u$.

To show \mono{(evals (As (2*(i+1))) i (R\_wt i)).Dom}, it suffices to show that the corresponding finite extension was found in the KP54 construction procedure.

But we know a finite extension must exist, as the use of the computation is finite.

-/
lemma As_Uninjured_1 : ¬(evals (As (2*i+1+1)) i (R_wt i)).Dom → ¬(evalSet A i (R_wt i)).Dom := by
  unfold As
  unfold KP54
  simp (config := {zeta:=false})
  lift_lets; extract_lets; expose_names
  have i_1_simp: i_1 = i := rfl
  have keqlb : R_wt i=lb := rfl

  -- if dvt.Dom, this contradicts our assumption that the computation diverges.
  if h0 : dvt.Dom then
    simp (config := {zeta:=false}) [h0]
    lift_lets; extract_lets; expose_names
    simp only [List.concat_eq_append, pair_l, Denumerable.ofNat_encode]
    intro h
    exfalso
    have := finite_ext_prop h0
    simp only [i_1_simp] at this
    exact h this
  else

  simp (config := {zeta:=false}) [h0]

  have a1 := finite_ext_prop_div h0
  intro h; clear h
  contrapose a1
  -- simp at a1
  rename' a1 => final_comp_halts
  simp [-Denumerable.list_ofNat_succ]
  -- the goal now reads:
  -- if the final computation converges, we must have found some finite extension `x` at stage `2*i+1`.

  rw [i_1_simp]
  rw [←keqlb]
  simp only [evals]
  have use_dom := e2u final_comp_halts
  let use_compl := (use (χ A) (i.n2c) (R_wt i)).get use_dom
  rw [show n2l αₚ = As (2*i+1) from rfl]
  /-
  As the final computation (on index `i`, input `R_wt i`) only uses up to `use_compl`, this means we only need our string `As` to be as long as `use_compl` for our computation to halt.

  That is, the string `As (use_compl + 1)` is enough to make the computation halt.

  We are currently at stage `2*i+1`, so we split into two cases.

  If `2*i+1 ≤ use_compl`, then we use the extension that will get us to the string `As (use_compl + 1)`.
  (This can be extracted with `As_ex_ext`).

  If `use_compl < 2*i+1`, this means that we don't need an extension at all, as our current string is already an extension of `As (use_compl + 1)`.

  To actually prove the computation halts, we appeal to `evalc_prop_4.mp`, which tells us that `evalc` halts if the use is defined and is smaller than the imposed limit (which here is the size of the string `As`),

  That the use is defined is proved via the use principle, showing our use is equivalent to the final computation's use.

  To show that our use is smaller than the limit:
    · in the case we use `As (use_compl + 1)`, note by monotonicty of `As` its length is `≥ use_compl + 1`.
    · in the other case this follows directly from `use_compl < 2*i+1`.

  -/
  if h0 : 2*i+1 ≤ use_compl then
    rcases @As_ex_ext (2*i+1) (use_compl+1) (Nat.add_lt_add_right h0 1) with ⟨x,hx⟩
    use x
    rw [hx]
    -- showing that the current use is equivalent to the final computation's use
    have mainrw : use (fun e ↦ b2n (n2b ((As (use_compl + 1)).getD e whatever))) i (R_wt i) = use (χ A) i (R_wt i) := by
      apply Eq.symm
      refine use_principle_use final_comp_halts ?_
      intro i2 hi2
      simp [χ,A]
      have hi3 : i2 < (As (use_compl + 1)).length := calc
        i2 < use_compl  := hi2
        use_compl <  (As (use_compl + 1)).length := AsSize
      rw [@As_Mono_4 i2 (use_compl+1) (i2 + 1) whatever hi3 (AsSize)]
      simp only [b2n, ite_eq_ite]
    have := Nat.le_of_succ_le (@AsSize use_compl)
    apply evalc_prop_4.mp <;> (simp only [mainrw]; assumption)

  else

  simp at h0
  use 0 -- use 0, as we do not need any extension
  -- showing that the use is below the length of our string
  have a6 : use_compl < (As (2 * i + 1)).length := calc
    use_compl < 2 * i + 1 := h0
    _     ≤ (As (2 * i + 1)).length := AsSize
  have a5 : use_compl ≤ (As (2 * i + 1) ++ n2l (0 + 1)).length := calc
    use_compl ≤ 2 * i + 1 := Nat.le_of_succ_le h0
    _     ≤ (As (2 * i + 1)).length := AsSize
    _     ≤ (As (2 * i + 1) ++ n2l (0 + 1)).length := by
      simp only [zero_add, List.length_append, le_add_iff_nonneg_right, zero_le]

  -- showing that the current use is equivalent to the final computation's use
  have mainrw : use (fun e ↦ b2n (n2b ((As (2 * i + 1) ++ n2l (0 + 1)).getD e whatever))) i.n2c (R_wt i) = use (χ A) i.n2c (R_wt i):= by
    apply Eq.symm
    refine use_principle_use final_comp_halts ?_
    intro i2 hi2
    have hi3 := lt_trans hi2 a6
    unfold χ
    unfold A
    simp
    rw [@list_access_small _ _ _ [0] hi3]
    rw [@As_Mono_4 i2 (2*i+1) (i2 + 1) whatever (hi3) (AsSize)]
    simp only [b2n, ite_eq_ite]
  apply evalc_prop_4.mp <;> (simp only [mainrw]; assumption)
lemma As_Uninjured_1' {i:ℕ} : (evalSet A i (R_wt i)).Dom  → (evals (As (2*(i+1))) i (R_wt i)).Dom := not_imp_not.mp (@As_Uninjured_1 i)

/-- states that the computation [i](R_wt i) will remain unchanged. -/
theorem As_Uninjured (i:ℕ) : evalSet A i (R_wt i) = evals (As (2*(i+1))) i (R_wt i) := by
  if h : (evalSet A i (R_wt i)).Dom then
    rw [@As_Uninjured_0 (i) (R_wt i) (As_Uninjured_1' h)]
  else
    rw [Part.eq_none_iff'.mpr h]
    rw [Part.eq_none_iff'.mpr (As_Uninjured_0' h)]

theorem R_aux_1 (i:ℕ) : (evalSet A i (R_wt i)) ≠ Part.some ((χ B) (R_wt i)) := by
  if h0 : (evalSet A i (R_wt i)).Dom then
    rw [R_aux_χ] -- rw the rhs
    simp only [As_Uninjured i] -- rw the lhs
    exact Part.ne_of_get_ne' $ R_aux_0 i (As_Uninjured_1' h0)
  else
    simp [Part.eq_none_iff'.mpr h0]

theorem R (i:ℕ) : evalSet A i ≠ χ B := Function.ne_iff.mpr ⟨R_wt i, R_aux_1 i⟩
end R

section S
/-
This section is essentially identical to section R, so we remove any comments.
-/
private noncomputable def S_wt (i:ℕ) := (As (2*i)).length
@[simp] theorem AsSize_o2e_wt : S_wt i < (As (2*i+1)).length := by
  rw [show S_wt i = (As (2*i)).length from rfl]
  exact AsSize_mono'
private theorem S_aux_0 (i:ℕ) (h:(evals (Bs (2*i+1)) i (S_wt i)).Dom):
(evals (Bs (2*i+1)) i (S_wt i)).get h ≠ b2n (n2b $ (As (2*i+1))[S_wt i]'(@AsSize_o2e_wt i)) := by
  unfold Bs
  unfold As
  unfold KP54
  simp (config := {zeta:=false})
  simp (config := {zetaHave:=false}) only []
  lift_lets; extract_lets; expose_names
  have i_1_simp: i_1 = i := rfl
  let (eq:=hdvt) dvt := (finite_ext βₚ i_1 la)
  simp (config := {zeta:=false}) only [←hdvt]
  have halts : dvt.Dom := by
    apply byContradiction
    intro halts
    rcases @Bs_ex_ext (2*i) (2*i+1) (Nat.lt_add_one (2*i)) with ⟨h3,h2⟩
    have := finite_ext_prop_div halts h3
    rw [show n2l βₚ = Bs (2*i) from rfl, h2, i_1_simp] at this
    exact this h
  let (eq:=hrf) rf := dvt.get halts
  let (eq:=hβₛ) βₛ := (n2l βₚ) ++ (n2l (rf+1))
  simp (config := {zeta:=false}) only [←hrf, ←hβₛ, halts]
  simp (config := {zeta:=false}) []
  lift_lets; extract_lets; expose_names
  have lbrw : S_wt i = (n2l αₚ).length := rfl
  simp [lbrw]; simp only [←lbrw]
  simp [show (evals (βₛ) i (S_wt i)).get (finite_ext_prop halts) = B_result from rfl]
  cases B_result <;> simp [n2b,b2n]
theorem S_aux_χ: χ A (S_wt i) = b2n (n2b ((As (2*i+1))[(S_wt i)]'(@AsSize_o2e_wt i))) := by
  simp [A, χ]
  simp [As_Mono_3 (@AsSize (S_wt i)) (@AsSize_o2e_wt i)]
  exact rfl
theorem Bs_Uninjured_0 (hh:(evals (Bs (2*i+1)) i k).Dom): evals (Bs (2*i+1)) i k = evalSet B i k := by
  simp [B, evalSet]; unfold χ; simp [evals]
  have h1 := evalc_prop_0 hh
  simp at h1
  rw [h1]
  have hh2 := hh
  simp [evals, h1] at hh2
  apply use_principle_eval hh2
  intro ii hii
  rw [Bs_Mono_4 (Nat.lt_of_lt_of_le hii (evalc_prop_1 hh)) BsSize]
  split <;> next h => simp [b2n,h]
theorem Bs_Uninjured_0' {i:ℕ} : ¬ (evalSet B i k).Dom → ¬ (evals (Bs (2*i+1)) i k).Dom := by
  contrapose
  intro h
  rwa [←Bs_Uninjured_0 h]
lemma Bs_Uninjured_1 : ¬(evals (Bs (2*i+1)) i (S_wt i)).Dom → ¬(evalSet B i (S_wt i)).Dom := by
  unfold Bs
  unfold KP54
  simp (config := {zeta:=false})
  lift_lets; extract_lets; expose_names
  have i_1_simp: i_1 = i := rfl
  have keqlb : S_wt i = la := rfl
  if h0 : dvt.Dom then
    simp (config := {zeta:=false}) [h0]
    lift_lets; extract_lets; expose_names
    simp only [List.concat_eq_append, pair_r, Denumerable.ofNat_encode]
    intro h
    exfalso
    have := finite_ext_prop h0
    simp only [i_1_simp] at this
    exact h this
  else
  simp (config := {zeta:=false}) [h0]
  have a1 := finite_ext_prop_div h0
  intro h; clear h
  contrapose a1
  rename' a1 => final_comp_halts
  simp [-Denumerable.list_ofNat_succ]
  rw [i_1_simp]
  rw [←keqlb]
  simp only [evals]
  have use_dom := e2u final_comp_halts
  let use_compl := (use (χ B) (i.n2c) (S_wt i)).get use_dom
  rw [show n2l βₚ = Bs (2*i) from rfl]
  if h0 : 2*i ≤ use_compl then
    rcases @Bs_ex_ext (2*i) (use_compl+1) (Nat.lt_add_one_of_le h0) with ⟨x,hx⟩
    use x
    rw [hx]
    have mainrw : use (fun e ↦ b2n (n2b ((Bs (use_compl + 1)).getD e whatever))) i (S_wt i) = use (χ B) i (S_wt i) := by
      apply Eq.symm
      refine use_principle_use final_comp_halts ?_
      intro i2 hi2
      simp [χ,B]
      have hi3 : i2 < (Bs (use_compl + 1)).length := calc
        i2 < use_compl  := hi2
        use_compl <  (Bs (use_compl + 1)).length := BsSize
      rw [@Bs_Mono_4 i2 (use_compl+1) (i2 + 1) whatever hi3 (BsSize)]
      simp only [b2n, ite_eq_ite]
    have := Nat.le_of_succ_le (@BsSize use_compl)
    apply evalc_prop_4.mp <;> (simp only [mainrw]; assumption)
  else
  simp at h0
  use 0
  have a6 : use_compl < (Bs (2*i)).length := calc
    use_compl < 2*i := h0
    _     ≤ (Bs (2*i)).length := (@AsBsSize $ 2*i).right
  have a5 : use_compl ≤ (Bs (2*i) ++ n2l (0 + 1)).length := calc
    use_compl ≤ 2*i := Nat.le_of_succ_le h0
    _     ≤ (Bs (2*i)).length := (@AsBsSize $ 2*i).right
    _     ≤ (Bs (2*i) ++ n2l (0 + 1)).length := by
      simp only [zero_add, List.length_append, le_add_iff_nonneg_right, zero_le]
  have mainrw : use (fun e ↦ b2n (n2b ((Bs (2*i) ++ n2l (0 + 1)).getD e whatever))) (i.n2c) (S_wt i) = use (χ B) (i.n2c) (S_wt i):= by
    apply Eq.symm
    refine use_principle_use final_comp_halts ?_
    intro i2 hi2
    have hi3 := Nat.lt_trans hi2 a6
    unfold χ
    unfold B
    simp
    rw [@list_access_small _ _ _ [0] hi3]
    rw [@Bs_Mono_4 i2 (2*i) (i2 + 1) whatever (hi3) (BsSize)]
    simp only [b2n, ite_eq_ite]
  apply evalc_prop_4.mp <;> (simp only [mainrw]; assumption)
lemma Bs_Uninjured_1' {i:ℕ} : (evalSet B i (S_wt i)).Dom  → (evals (Bs (2*i+1)) i (S_wt i)).Dom := not_imp_not.mp (@Bs_Uninjured_1 i)
theorem Bs_Uninjured (i:ℕ) : evalSet B i (S_wt i) = evals (Bs (2*i+1)) i (S_wt i) := by
  if h : (evalSet B i (S_wt i)).Dom then
    rw [@Bs_Uninjured_0 i (S_wt i) (Bs_Uninjured_1' h)]
  else
    rw [Part.eq_none_iff'.mpr h]
    rw [Part.eq_none_iff'.mpr (Bs_Uninjured_0' h)]
theorem S_aux_1 (i:ℕ) : (evalSet B i (S_wt i)) ≠ Part.some ((χ A) (S_wt i)) := by
  if h0 : (evalSet B i (S_wt i)).Dom then
    rw [S_aux_χ]
    simp only [Bs_Uninjured i]
    exact Part.ne_of_get_ne' $ S_aux_0 i (Bs_Uninjured_1' h0)
  else
    simp [Part.eq_none_iff'.mpr h0]
theorem S (i:ℕ) : evalSet B i ≠ χ A := Function.ne_iff.mpr ⟨S_wt i, S_aux_1 i⟩
end S

theorem ex_incomparable_sets : ∃ A B:Set ℕ, A|ᵀB := by
  use A
  use B
  constructor
  · change ¬SetTuringReducible A B
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    have contrad := S c
    exact contrad hc
  · change ¬SetTuringReducible B A
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    have contrad := R c
    exact contrad hc

end KP54
