import Computability.SetOracles
import Computability.Constructions.EvalString

/-!
# KP54

In this file we specify the construction procedure in the KP54 proof, and show that the sets it defines are incomparable.
-/

open Computability.Code
open Classical
open Computability

namespace Computability.Code

end Computability.Code

set_option linter.dupNamespace false
namespace KP54

-- c_kp54_aux check if x.r+1 is a finite extension to A for the computation [i](n).
@[irreducible] noncomputable def c_kp54_aux (i n:ℕ) :=
  c_ifdom
  (c_evals.comp₃ (c_list_append.comp₂ left (succ.comp right)) (c_const i) (c_const n))
  zero
theorem c_kp54_aux_evp :
  eval (λ_↦0) (c_kp54_aux i n) x
    =
  if (evals ((n2l x.l) ++ (n2l (x.r+1))) i n).Dom then Part.some 0 else Part.none
:= by
  simp [c_kp54_aux, -Denumerable.list_ofNat_succ]
  simp [Computability.eval, -Denumerable.list_ofNat_succ]
  simp [Seq.seq, -Denumerable.list_ofNat_succ]
theorem c_kp54_aux_2 (halts:(eval (λ_↦0) (dovetail (c_kp54_aux i lb)) Aₚ).Dom) :
  have dvt := (eval (λ_↦0) (dovetail (c_kp54_aux i lb)) Aₚ).get halts
  (evals ((n2l Aₚ) ++ (n2l (dvt+1))) i lb).Dom := by
    have := dovetail_ev_0 halts
    extract_lets at this ⊢
    expose_names
    simp only [c_kp54_aux_evp] at this
    contrapose this
    simp [-Denumerable.list_ofNat_succ]
    exact this

open Nat List in
/--
The construction procedure in the KP54 proof.

Input: stage `s`
Output: (string `Aₛ`, string `Bₛ`)

(The strings are encoded as a list of naturals.)

Each string `Aₛ` and `Bₛ` increase in length by at least 1 every stage.
-/
noncomputable def KP54 : ℕ → ℕ := λ s ↦
match s with
| 0 => ⟪0, 0⟫
| s+1 =>
  have i  := s.div2
  have Aₚ := (KP54 s).l
  have Bₚ := (KP54 s).r
  have lb := (n2l Bₚ).length
  have la := (n2l Aₚ).length

  if (s+1)%2=0 then -- then s+1=2i+2, and we will work on Rᵢ.
    let dvt := eval (λ_↦0) (dovetail (c_kp54_aux i lb)) Aₚ -- this is the step where we search for a finite extension.
    if halts:dvt.Dom then
      let rf := dvt.get halts -- rf is a natural such that (eval_string ((n2l A) ++ (n2l rf)) i n).Dom.
      let Aₛ := (n2l Aₚ) ++ (n2l (rf+1))
      let A_result := (evals Aₛ i lb).get (c_kp54_aux_2 halts)
      Nat.pair Aₛ ((n2l Bₚ).concat (Nat.sg' A_result))
    else
      Nat.pair (l2n $ (n2l Aₚ).concat 0) (l2n $ (n2l Bₚ).concat 0)
  else -- then s+1=2i+1, and we will work on Sᵢ.
    let dvt := eval (λ_↦0) (dovetail (c_kp54_aux i la)) Bₚ
    if halts:dvt.Dom then
      let rf := dvt.get halts
      let Bₛ := (n2l Bₚ) ++ (n2l (rf+1))
      let B_result := (evals (Bₛ) i la).get (c_kp54_aux_2 halts)
      Nat.pair ((n2l Aₚ).concat (Nat.sg' B_result)) Bₛ
    else
      Nat.pair (l2n $ (n2l Aₚ).concat 0) (l2n $ (n2l Bₚ).concat 0)
@[simp] theorem KP54_0_r : n2l (KP54 0).r = [] := by simp [KP54]
@[simp] theorem KP54_0_l : n2l (KP54 0).l = [] := by simp [KP54]

noncomputable def As (s:ℕ) := n2l (KP54 s).l
noncomputable def Bs (s:ℕ) := n2l (KP54 s).r


-- We prove a bunch of theorems about the monotonicity of growth of the strings `As` and `Bs`, and their sizes.
theorem AsBs_Mono_0 : (As i) <+: (As (i+1)) ∧ (Bs i) <+: (Bs (i+1)) := by
  unfold As
  unfold Bs
  -- rw (config:={occs:=.pos [2,3]}) [KP54]
  rw (config:={occs:=.pos [1,2]}) [KP54]
  simp (config := {zeta:=false}) [-Nat.rfind_dom]
  -- lift_lets
  -- extract_lets
  -- expose_names
  if h0: (i+1) % 2 = 0 then
    simp [h0,-Nat.rfind_dom]
    aesop
  else
    simp [h0,-Nat.rfind_dom]
    aesop
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

theorem As_Mono_3
(hi:k<(As i).length)
(hh:k<(As j).length)
: (As i)[k] = (As j)[k] := by
  cases Classical.em (i≤j) with
  | inl h =>
    have := (AsBs_Mono_2 h).left
    exact List.IsPrefix.getElem this hi
  | inr h =>
    simp at h
    have := (AsBs_Mono_2 (Nat.le_of_succ_le h)).left
    exact Eq.symm (List.IsPrefix.getElem this hh)
theorem Bs_Mono_3
(hi:k<(Bs i).length)
(hh:k<(Bs j).length)
: (Bs i)[k] = (Bs j)[k] := by
  cases Classical.em (i≤j) with
  | inl h =>
    have := (AsBs_Mono_2 h).right
    exact List.IsPrefix.getElem this hi
  | inr h =>
    simp at h
    have := (AsBs_Mono_2 (Nat.le_of_succ_le h)).right
    exact Eq.symm (List.IsPrefix.getElem this hh)
theorem As_Mono_4
(hii : ii < (As j).length)
(asz : ii < (As k).length)
:
((As j)[ii]?.getD smth) = (As k)[ii] := by
  have : (As j)[ii]?.getD smth = (As k)[ii] := by
    have : (As j)[ii]?.getD smth = (As j)[ii] := by simp only [getElem?_pos, Option.getD_some,hii]
    rw [this]
    exact As_Mono_3 hii asz
  rw [this]
theorem Bs_Mono_4
(hii : ii < (Bs j).length)
(asz : ii < (Bs k).length)
:
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
  rw [show As (2*i+1) = n2l Aₚ from rfl]
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
  rw [show Bs (2*i) = n2l Bₚ from rfl]
  if h0:dvt.Dom then simp [h0]
  else simp [h0]

theorem AsSize_mono' : (As i).length < (As (i+1)).length := by
  cases Nat.even_or_odd i with
  | inl h =>
    rcases h with ⟨h1,h2⟩
    have := @AsSize_o2e h1
    have a0 : i=2*h1 := by
      rw [h2]
      exact Eq.symm (Nat.two_mul h1)
    rw [a0]
    simp_all only [lt_add_iff_pos_right, zero_lt_one]
  | inr h =>
    rcases h with ⟨h1,h2⟩
    have := @AsSize_e2o h1
    rw [h2]
    simp_all only []
theorem AsSize_mono (hij:i<j) : (As i).length < (As j).length := by
  have a0 := @AsSize_mono' i
  have a1 := (@AsBs_Mono_2 (i+1) j (hij)).left
  exact Nat.lt_of_lt_of_le a0 (List.IsPrefix.length_le a1)
theorem Asexext (hij:i<j): ∃ lM1, (As i)++(n2l (lM1+1))=As j := by
  have a0 := (@AsBs_Mono_2 i j (Nat.le_of_succ_le hij)).left
  have a1 : (As i).length < (As j).length := by exact AsSize_mono hij
  rcases a0 with ⟨h1,h2⟩
  have a2 : h1.length > 0 := by grind
  have a3 : l2n h1 ≠ 0 := by
    contrapose a2
    simp at a2 ⊢
    apply Encodable.encode_inj.mp a2
  have a4 : (l2n h1)-1+1=l2n h1 := by exact Nat.succ_pred_eq_of_ne_zero a3
  use (l2n h1)-1
  simp [a4]
  exact h2
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

-- wt stands for witness. R_wt i is the natural that witnesses requirement `R i`.
private noncomputable def R_wt (i:ℕ) := (Bs (2*(i+1)-1)).length
@[simp] theorem BsSize_o2e' : R_wt i < (Bs (2 * (i + 1))).length := by
  rw [show R_wt i = (Bs (2*(i+1)-1)).length from rfl]
  have : 2 * (i + 1) - 1 = 2*i+1 := by exact rfl
  rw [this]
  have : 2*(i+1) = 2*i + 2:= by exact rfl
  rw [this]
  have := @BsSize_o2e i
  simp_all only [Nat.add_one_sub_one, lt_add_iff_pos_right, zero_lt_one]

-- private noncomputable def S_wt (i:ℕ) := (As (2*(i+1)-1)).length
-- @[simp] theorem AsSize_o2e' : S_wt i < (As (2 * (i + 1))).length := by
--   rw [show S_wt i = (As (2*(i+1)-1)).length from rfl]
--   exact AsSize_mono'

-- The "completed" sets `A` and `B`, defined from `As` and `Bs` noting that by stage `x+1`, index `x` is defined by the monotonicty theorems above.
-- The [x] 's require the theorems AsSize and BsSize above.
def A := { x | n2b (As (x+1))[x] }
def B := { x | n2b (Bs (x+1))[x] }

private theorem R_aux_0 (i:ℕ) (h:(evals (As (2*i+1+1)) i (R_wt i)).Dom):
(evals (As (2*i+1+1)) i (R_wt i)).get h ≠ b2n (n2b $ (Bs (2*i+1+1))[R_wt i]'(@BsSize_o2e' i)) := by
  unfold Bs
  unfold As
  unfold KP54
  simp (config := {zeta:=false})
  simp (config := {zetaHave:=false}) only []
  -- memory blows up if i lift the non-have lets. why?

  lift_lets; extract_lets; expose_names
  have i_1_simp: i_1 = i := rfl

  let (eq:=hdvt) dvt := (Computability.eval (λ_↦0) (c_kp54_aux i_1 lb).dovetail Aₚ)
  simp (config := {zeta:=false}) only [←hdvt]

  if halts: dvt.Dom then
    let (eq:=hrf) rf  := dvt.get halts -- rf is a natural such that (eval_string ((n2l A) ++ (n2l rf)) i n).Dom.
    simp (config := {zeta:=false}) only [←hrf]
    let (eq:=hAₛ) Aₛ := (n2l Aₚ) ++ (n2l (rf+1))
    simp (config := {zeta:=false}) only [←hAₛ]
    simp (config := {zeta:=false}) [halts]
    lift_lets; extract_lets; expose_names

    have lbrw : R_wt i = (n2l Bₚ).length := rfl
    simp [lbrw]; simp only [←lbrw]

    have aaa : A_result = (evals (Aₛ) i_1 (R_wt i)).get (c_kp54_aux_2 (of_eq_true (eq_true halts))) := rfl
    simp (config := {zeta:=false}) only [i_1_simp] at aaa
    simp [←aaa]

    cases A_result <;> simp [n2b,b2n]

  else
    exfalso
    rcases @Asexext (2*i+1) (2*i+2) (Nat.lt_add_one (2 * i + 1)) with ⟨h3,h2⟩
    have := dovetail_ev_1.mp (Part.eq_none_iff'.mpr halts) h3
    simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at this
    rw [show n2l Aₚ = As (2*i+1) from rfl, h2, i_1_simp] at this
    exact this h

theorem R_aux_χ: χ B (R_wt i) = b2n (n2b ((Bs (2 * (i + 1)))[(R_wt i)]'(@BsSize_o2e' i))) := by
  simp [B,χ]
  simp [Bs_Mono_3 (@BsSize (R_wt i)) (@BsSize_o2e' i)]
  exact rfl

/--
If `[i:As](k)` halts, then its value will be unchanged in all subsequent steps.
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
  split
  next h => simp [b2n,h]
  next h => simp [b2n,h]
theorem As_Uninjured_0' {i:ℕ} : ¬ (evalSet A i k).Dom → ¬ (evals (As (2*(i+1))) i k).Dom := by
  contrapose
  simp only [Decidable.not_not]
  intro h
  rw [←As_Uninjured_0 h]
  exact h
/--
If `[i:As](k)` diverges, then it will always diverge in subsequent steps.
-/
theorem As_Uninjured_1 : ¬(evals (As (2*i+1+1)) i (R_wt i)).Dom → ¬(evalSet A i (R_wt i)).Dom := by
  unfold As
  unfold KP54
  simp (config := {zeta:=false})
  lift_lets; extract_lets; expose_names
  have i_1_simp: i_1 = i := rfl
  have keqlb : R_wt i=lb := rfl

  if h0:dvt.Dom then
    simp (config := {zeta:=false}) [h0]
    lift_lets; extract_lets; expose_names
    simp only [List.concat_eq_append, pair_l, Denumerable.ofNat_encode]
    intro h
    exfalso
    have := c_kp54_aux_2 h0
    simp only [i_1_simp] at this
    exact h this

  else

  simp at h0
  simp (config := {zeta:=false}) [h0]

  have a1 := dovetail_ev_1.mp (Part.eq_none_iff'.mpr h0)
  simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at a1
  intro h; clear h
  contrapose a1
  simp at a1
  simp [-Denumerable.list_ofNat_succ]

  rw [i_1_simp]
  rw [←keqlb]

  simp only [evals]

  have a2 := e2u a1
  let usecn := (use (χ A) (n2c i) (R_wt i)).get a2

  have a4 := a2
  unfold A at a4
  unfold χ at a4
  simp at a4

  -- use reverse of evalc_prop'' to rephrase the evalc in the goal to just eval.
  -- then, use the extension that will get the oracle string to As (use).
  -- the inequality will be satisfies as the list as size greater than use.

  have Aprw : n2l Aₚ = As (2*i+1) := rfl
  rw [Aprw]
  if h0:2*i+1≤usecn then
    -- we want to make (As (2 * i + 1) ++ n2l (x + 1)) equal to (As (usecn + 1))
    rcases @Asexext (2*i+1) (usecn+1) (Nat.add_lt_add_right h0 1) with ⟨x,hx⟩
    use x
    rw [hx]

    have mainrw : (use (χ A) (n2c i) (R_wt i)) = (use (fun e ↦ b2n (n2b ((As (usecn + 1)).getD e whatever))) (n2c i) (R_wt i)) := by
      refine use_principle_use a1 ?_
      intro i2 hi2
      simp [χ,A]
      have hi3 : i2 < (As (usecn + 1)).length := calc
        i2 < usecn  := hi2
        usecn <  (As (usecn + 1)).length := AsSize
      have := @As_Mono_4 i2 (usecn+1) (i2 + 1) whatever hi3 (AsSize)
      rw [this]
      simp only [b2n, ite_eq_ite]
    apply evalc_prop_4.mp
    simp only [←mainrw]
    exact Nat.le_of_succ_le (@AsSize usecn)
    simp only [←mainrw]
    exact a2

  else

  simp at h0
  use 0

  have a6 : usecn < (As (2 * i + 1)).length := calc
    usecn < 2 * i + 1 := h0
    _     ≤ (As (2 * i + 1)).length := AsSize
  have a5 : usecn ≤ (As (2 * i + 1) ++ n2l (0 + 1)).length := calc
    usecn ≤ 2 * i + 1 := Nat.le_of_succ_le h0
    _     ≤ (As (2 * i + 1)).length := AsSize
    _     ≤ (As (2 * i + 1) ++ n2l (0 + 1)).length := by
      simp only [zero_add, List.length_append, le_add_iff_nonneg_right, zero_le]

  have mainrw : (use (χ A) (n2c i) (R_wt i)) = (use (fun e ↦ b2n (n2b ((As (2 * i + 1) ++ n2l (0 + 1)).getD e whatever))) (n2c i) (R_wt i)):= by
    refine use_principle_use a1 ?_
    intro i2
    intro hi2
    have hi3 : i2 < (As (2 * i + 1)).length := by exact Nat.lt_trans hi2 a6
    unfold χ
    unfold A
    simp
    have : (As (2 * i + 1) ++ [0])[i2]? = (As (2 * i + 1))[i2]? := by
      simp [hi3]
      grind
    rw [this]
    have := @As_Mono_4 i2 (2*i+1) (i2 + 1) whatever (hi3) (AsSize)
    rw [this]

    simp only [b2n, ite_eq_ite]
  apply evalc_prop_4.mp
  simp only [←mainrw]
  exact a5
  simp only [←mainrw]
  exact a2
theorem As_Uninjured_1' {i:ℕ} : (evalSet A i (R_wt i)).Dom  → (evals (As (2*(i+1))) i (R_wt i)).Dom := not_imp_not.mp (@As_Uninjured_1 i)
theorem As_Uninjured (i:ℕ) : evalSet A i (R_wt i) = evals (As (2*(i+1))) i (R_wt i) := by
  if h:(evalSet A i (R_wt i)).Dom then
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
theorem S (i:ℕ) : evalSet B i ≠ χ A := by sorry

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
