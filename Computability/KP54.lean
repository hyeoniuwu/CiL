import Computability.SetOracles

open Nat.RecursiveIn.Code
open Classical
open Computability

namespace Nat.RecursiveIn.Code



def n2b (n:ℕ) : Bool := if n=0 then false else true
def b2n (b:Bool) : ℕ := if b then 1 else 0

-- the b2n $ n2b is to simplify later proofs where evals will be compared against _.
def evals (σ:List ℕ) (c:Code) (x:ℕ):= eval_clamped (fun e=> b2n $ n2b $ σ.getD e 999) σ.length c x
end Nat.RecursiveIn.Code

set_option linter.dupNamespace false
namespace KP54

/-
bsunion doesnt work bc it changes prev values
it should actually just be... join!
so itd be convenient to use lists of bool
but i defined c_list functions for list of naturals...
which is fine. (i think i remember doing that on purpose, because you can interpret the natural that you get from the list afterwards.)
and here i can just directly work with a list of nat anyways, interpreting 0 as false and anything else as true.
-/
-- the proofs later however are simplified if A_s,B_s are treated as List Bool...
-- /mnt/Q/Mathematics/LaTeX/Writings/Computability.pdf
-- c_kp54_aux check if x.r+1 is a finite extension to A for the computation [i](n).
def c_kp54_aux (A i n:ℕ) := zero
theorem c_kp54_aux_evp :
  eval Nat.fzero (c_kp54_aux A i n) x
    =
  if (evals ((n2l A) ++ (n2l (x.r+1))) i n).Dom then Part.some 0 else Part.some 1
:= by
  sorry
theorem c_kp54_aux_2 (halts:(eval Nat.fzero (dovetail (c_kp54_aux Aₚ i lb)) 17).Dom) :
  let dvt := (eval Nat.fzero (dovetail (c_kp54_aux Aₚ i lb)) 17).get halts
  (evals ((n2l Aₚ) ++ (n2l (dvt.l+1))) i lb).Dom := by
    have := dovetail_ev_0' halts
    extract_lets at this ⊢
    expose_names
    simp only [c_kp54_aux_evp] at this
    contrapose this
    simp [-Denumerable.list_ofNat_succ]
    exact this
#check eval Nat.fzero

open Nat List in
/--
Input: stage `s`
Output: (code for `Aₛ`, code for `Bₛ`)
-/
noncomputable def KP54 : ℕ→ℕ := λ s ↦
  if s=0 then Nat.pair 0 0 else

  let i  := (s-1).div2
  let Aₚ := (KP54 (s-1)).l
  let Bₚ := (KP54 (s-1)).r
  let lb := List.length (n2l Bₚ)
  let la := List.length (n2l Aₚ)

  if s%2=0 then -- then s=2i+2, and we will work on Rᵢ.
    let dvt := eval Nat.fzero (dovetail (c_kp54_aux Aₚ i lb)) 17
    if halts:dvt.Dom then
      let rf := (dvt.get halts).l -- rf is a natural such that (eval_string ((n2l A) ++ (n2l rf)) i n).Dom.
      let Aₛ := (n2l Aₚ) ++ (n2l (rf+1))
      let A_result := (evals Aₛ i lb).get (c_kp54_aux_2 halts)
      Nat.pair Aₛ ((n2l Bₚ).concat (Nat.sg' A_result))
    else
      Nat.pair (l2n $ (n2l Aₚ).concat 0) (l2n $ (n2l Bₚ).concat 0)
  else -- then s=2i+1, and we will work on Sᵢ.
    let dvt := eval Nat.fzero (dovetail (c_kp54_aux Bₚ i la)) 17
    if halts:dvt.Dom then
      let rf := (dvt.get halts).l
      let Bₛ := (n2l Bₚ) ++ (n2l (rf+1))
      let B_result := (evals (Bₛ) i la).get (c_kp54_aux_2 halts)
      Nat.pair ((n2l Aₚ).concat (Nat.sg' B_result)) Bₛ
    else
      Nat.pair (l2n $ (n2l Aₚ).concat 0) (l2n $ (n2l Bₚ).concat 0)

/-
`KP54(s)=(a,b)` where `D a, D b` correspond to sets `A` and `B` at stage `s`.
We note that:
 · by stage 2n,   `χ_B(n)` is bound to be defined.
 · by stage 2n+1, `χ_A(n)` is bound to be defined.

actually now i changed it so that i think
 · by stage n,   `χ_B(n)` is bound to be defined.
 · by stage n,   `χ_A(n)` is bound to be defined.
-/
private noncomputable def As (s:ℕ) := n2l (KP54 s).l
private noncomputable def Bs (s:ℕ) := n2l (KP54 s).r

theorem AsBs_Mono_0 : (As i) <+: (As (i+1)) ∧ (Bs i) <+: (Bs (i+1)) := by
  unfold As
  unfold Bs
  rw (config:={occs:=.pos [2,3]}) [KP54]
  simp (config := {zeta:=false}) [-Nat.rfind_dom]
  lift_lets
  extract_lets
  expose_names
  if h0:(i + 1) % 2 = 0 then
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
theorem AsSize : i<(As (i+1)).length := (@AsBsSize (i+1)).left
theorem BsSize : i<(Bs (i+1)).length := (@AsBsSize (i+1)).right

theorem BsSize_o2e': (Bs (2 * (i + 1) - 1)).length < (Bs (2 * (i + 1))).length := by
  have : 2 * (i + 1) - 1 = 2*i+1 := by exact rfl
  rw [this]
  have : 2*(i+1) = 2*i + 2:= by exact rfl
  rw [this]
  have := @BsSize_o2e i
  simp_all only [Nat.add_one_sub_one, lt_add_iff_pos_right, zero_lt_one]


private def A := {x | n2b $ (As (x+1))[x]'AsSize}
private def B := {x | n2b $ (Bs (x+1))[x]'BsSize}

noncomputable def Bsize (i:ℕ) := (Bs i).length

theorem R_aux' : (n2l (Bs (2*(i+1)-1))).length < (Bs (2*(i+1))).length := by
  simp only [Denumerable.ofNat_encode]
  exact BsSize_o2e'

private noncomputable def R_wt (i:ℕ) := (n2l (Bs (2*(i+1)-1))).length
private theorem R_aux (i:ℕ) (h:(evals (As (2*(i+1))) i (R_wt i)).Dom):
(evals (As (2*(i+1))) i (R_wt i)).get h ≠ b2n (n2b $ (Bs (2*(i+1)))[R_wt i]'(R_aux')) := by
  unfold Bs
  unfold As
  unfold KP54
  simp (config := {zeta:=false})
  lift_lets
  extract_lets
  expose_names
  have i_1_simp: i_1 = i := Nat.div2_bit1 i
  have keqlb : R_wt i=lb := by
    rw [show R_wt i=(n2l (l2n (Bs (2 * (i+1) - 1)))).length from rfl]
    simp
    rw [show lb=(n2l Bₚ).length from rfl]
    unfold Bs
    rw [show Bₚ=(KP54 (2 * (i + 1) - 1)).r from rfl]


  if h1: dvt.Dom then
    simp (config := {zeta:=false}) [h1]
    lift_lets
    extract_lets
    expose_names

    simp [keqlb]
    have lbrw : lb = (n2l Bₚ).length := rfl
    simp only [lbrw]
    simp
    have aaa : A_result = (evals (n2l Aₚ ++ n2l (rf + 1)) (decodeCode i_1) lb).get (c_kp54_aux_2
      (Eq.mpr_prop (Eq.refl dvt.Dom)
        (Eq.mpr_prop
          (congrArg (fun x ↦ dvt.Dom) i_1_simp)
          (of_eq_true (eq_true h1))))) := rfl

    simp [-Denumerable.list_ofNat_succ] at aaa
    have : (n2l Aₚ ++ n2l (rf + 1))=Aₛ:= rfl
    simp only [this] at aaa
    simp (config := {zeta:=false}) only [i_1_simp] at aaa
    simp only [←lbrw]
    have Aresrw : evals Aₛ (decodeCode (i)) lb = Part.some A_result := by
      rw [aaa]
      simp
    simp [Aresrw]
    cases A_result <;> simp [n2b,b2n]

  else
    exfalso
    have keqlb_2 : R_wt i = lb := by exact keqlb
    rw [keqlb_2] at h
    rw [show dvt = eval Nat.fzero (c_kp54_aux Aₚ i_1 lb).dovetail 17 from rfl] at h1
    have := dovetail_ev_1.mp (Part.eq_none_iff'.mpr h1)
    clear h1
    -- simp? [c_kp54_aux_evp] at this
    simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at this

    have Aprw : n2l Aₚ = As (2*i+1) := rfl
    rw [Aprw] at this
    have aux0 : 2*(i+1) = 2*i+2 := rfl
    rw [aux0] at h
    -- have := @Asexext' (2*i+1)
    have := @Asexext (2*i+1) (2*i+2) (Nat.lt_add_one (2 * i + 1))
    rcases this with ⟨h1,h2⟩
    have := this h1
    rw [h2] at this
    rw [show 2 * i + 1 + 1= 2*i+2 from rfl] at this
    rw [i_1_simp] at this
    exact this h

/--
If `[i:As](k)` halts, then its value will be unchanged in all subsequent steps.
-/
theorem As_Uninjured_0 (hh:(evals (As (2*(i+1))) i k).Dom): evals (As (2*(i+1))) i k = eval A i k := by
  unfold A
  simp
  unfold χ
  simp
  unfold evals
  simp

  have h1 := eval_clamped_prop_0 hh
  have h1r := eval_clamped_prop_1 hh
  simp at h1
  rw [h1]

  have hh2 := hh
  unfold evals at hh2
  simp at hh2
  rw [h1] at hh2
  apply use_principle_eval
  rotate_left
  exact hh2

  suffices ∀ i_1 < (As (2*(i+1))).length,
  b2n (n2b ((As (2*(i+1)))[i_1]?.getD 999)) = if n2b ((As (i_1 + 1))[i_1]'AsSize) = true then 1 else 0
    from by
    intro h3 h4
    have h5 := this h3 (Nat.le_trans h4 h1r)
    simp only [h5, ite_eq_ite]

  intro ii hii
  have asz := @AsSize ii
  rw [@As_Mono_4 ii (2*(i+1)) (ii + 1) 999 hii asz]
  rfl

theorem As_Uninjured_0' {i:ℕ} : ¬ (eval A i k).Dom → ¬ (evals (As (2*(i+1))) i k).Dom := by
  contrapose
  simp only [Decidable.not_not]
  intro h
  have := As_Uninjured_0 h
  rw [←this]
  exact h

/--
If `[i:As](k)` diverges, then it will always diverge in subsequent steps.
-/
theorem As_Uninjured_1 :
¬(evals (As (2*(i+1))) i (R_wt i)).Dom → ¬(eval A i (R_wt i)).Dom := by
  unfold As
  unfold KP54
  simp (config := {zeta:=false})
  lift_lets
  extract_lets
  expose_names
  have i_1_simp: i_1 = i := Nat.div2_bit1 i
  have keqlb : R_wt i=lb := by
    rw [show R_wt i=(n2l (l2n (Bs (2 * (i+1) - 1)))).length from rfl]
    simp
    rw [show lb=(n2l Bₚ).length from rfl]
    unfold Bs
    rw [show Bₚ=(KP54 (2 * (i + 1) - 1)).r from rfl]

  if h0:dvt.Dom then
    simp (config := {zeta:=false}) [h0]
    lift_lets
    extract_lets
    expose_names
    simp
    intro h
    exfalso
    have := c_kp54_aux_2 h0
    simp [-Denumerable.list_ofNat_succ] at this
    rw [i_1_simp] at this
    have a0 : (n2l Aₚ ++ n2l (((eval Nat.fzero (c_kp54_aux Aₚ i lb).dovetail 17).get h0).l + 1)) = Aₛ := by exact rfl
    rw [a0] at this
    rw [keqlb] at h
    exact h this



  else
  simp at h0
  simp (config := {zeta:=false}) [h0]
  have a0 : eval Nat.fzero (c_kp54_aux Aₚ i_1 lb).dovetail 17 = Part.none := by exact Part.eq_none_iff'.mpr h0

  have a1 := dovetail_ev_1.mp a0; clear a0
  simp [c_kp54_aux_evp, -Denumerable.list_ofNat_succ] at a1
  intro h; clear h
  contrapose a1
  simp at a1
  simp [-Denumerable.list_ofNat_succ]

  rw [i_1_simp]
  rw [←keqlb]

  -- unfold A at a1
  -- unfold χ at a1
  -- simp at a1
  simp only [evals]

  let compl := ((eval (χ A) (decodeCode i) (R_wt i)))
  let usecomp := (use (χ A) (decodeCode i) (R_wt i))
  have a2 := e2u a1
  have : usecomp.Dom := by exact a2
  let usecn := usecomp.get a2

  have a4 := a2
  unfold A at a4
  unfold χ at a4
  simp at a4

  -- use reverse of eval_clamped_prop'' to rephrase the eval_clamped in the goal to just eval.
  -- then, use the extension that will get the oracle string to As (use).
  -- the inequality will be satisfies as the list as size greater than use.
  have := eval_clamped_prop''_rev (a1) (Nat.le_refl ((usecomp).get (e2u a1)))
  have a3 : (eval_clamped (χ A) (usecn) (decodeCode i) (R_wt i)).Dom := by exact Part.eq_some_imp_dom this
  unfold A at this
  unfold χ at this
  simp at this
  have Aprw : n2l Aₚ = As (2*i+1) := rfl
  rw [Aprw]
  if h0:2*i+1≤usecn then
    -- we want to make (As (2 * i + 1) ++ n2l (x + 1)) equal to (As (usecn + 1))
    rcases @Asexext (2*i+1) (usecn+1) (Nat.add_lt_add_right h0 1) with ⟨x,hx⟩
    use x
    rw [hx]

    have mainrw : (use (χ A) (decodeCode i) (R_wt i)) = (use (fun e ↦ b2n (n2b ((As (usecn + 1)).getD e 999))) (decodeCode i) (R_wt i)) := by
      refine use_principle_use a1 ?_
      intro i2 hi2
      unfold χ
      unfold A
      simp
      have hi3 : i2 < (As (usecn + 1)).length := calc
        i2 < usecn  := hi2
        usecn <  (As (usecn + 1)).length := AsSize
      have := @As_Mono_4 i2 (usecn+1) (i2 + 1) 999 hi3 (AsSize)
      rw [this]
      simp only [b2n, ite_eq_ite]
    apply eval_clamped_prop''_rev2.mp
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

  have mainrw : (use (χ A) (decodeCode i) (R_wt i)) = (use (fun e ↦ b2n (n2b ((As (2 * i + 1) ++ n2l (0 + 1)).getD e 999))) (decodeCode i) (R_wt i)):= by
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
    have := @As_Mono_4 i2 (2*i+1) (i2 + 1) 999 (hi3) (AsSize)
    rw [this]

    -- have : (n2b ((As (2 * i + 1) ++ [0])[i2]?.getD 999)) = n2b ((As (i2 + 1))[i2]'AsSize) := by

    --   sorry
    -- rw [this]
    simp only [b2n, ite_eq_ite]
  apply eval_clamped_prop''_rev2.mp
  simp only [←mainrw]
  exact a5
  simp only [←mainrw]
  exact a2

theorem As_Uninjured_1' {i:ℕ} :
(eval A i (R_wt i)).Dom  → (evals (As (2*(i+1))) i (R_wt i)).Dom := by
  have := @As_Uninjured_1 i
  have := not_imp_not.mp this
  exact this

theorem As_Uninjured (i:ℕ) : eval A i (R_wt i) = evals (As (2*(i+1))) i (R_wt i) := by
  if h:(eval A i (R_wt i)).Dom then
    rw [@As_Uninjured_0 (i) (R_wt i) (@As_Uninjured_1' i h)]
  else
    rw [Part.eq_none_iff'.mpr h]
    rw [Part.eq_none_iff'.mpr (As_Uninjured_0' h)]

private theorem R (i:ℕ) : eval A i ≠ χ B := by
  apply Function.ne_iff.mpr
  have main := R_aux i
  use (R_wt i)
  if h0:(eval A (decodeCode i) (R_wt i)).Dom then

  -- change goal from Part ℕ to ℕ
  suffices (eval A (decodeCode i) (R_wt i)).get h0 ≠ (χ B) (R_wt i) from by
    contrapose this
    simp at this ⊢
    exact Part.get_eq_iff_eq_some.mpr this

  have := As_Uninjured i
  simp only [this]
  have main1 := main (this ▸ h0); clear main
  have rasd2aux := @R_aux' i

  have : χ B (R_wt i) = b2n (n2b (Bs (2 * (i + 1)))[(R_wt i)]) := by
    simp [B,χ]
    simp [Bs_Mono_3 (@BsSize (R_wt i)) (rasd2aux)]
    exact rfl
  
  exact Ne.symm (ne_of_eq_of_ne this (id (Ne.symm main1)))
  else
  aesop
private theorem S (i:ℕ) : eval B i ≠ χ A := by sorry

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
