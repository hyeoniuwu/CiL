/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.CovRec

/-!
# Constructions/Bitwise.lean

This file constructs primitive recursive codes for bitwise operations.

The main construction is `c_bitwise`, which allows bitwise operation of an arbitrary code/function.
The code constructed mirrors the Lean definition of `Nat.bitwise`, using course-of-values recursion.

For more documentation on theorems related to codes using course-of-values is proven, see
`Constructions\CovRec.lean`.

## Main declarations

- `c_bitwise`: Code implementing `Nat.bitwise`.
- `c_or`: Code implementing `Nat.lor`.
- `c_and`: Code implementing `Nat.land`.
- `c_xor`: Code implementing `Nat.xor`.

-/

section bitwise
namespace Oracle.Single.Code
/--
c.f. the definition of `bitwise` in Init\Data\Nat\Bitwise\Basic.lean.
-/
def c_bitwise_aux (c : Code) :=
  let iP1 := succ.comp (left.comp right)
  let comp_hist         := right.comp right
  let lookup (n'' m'')  := cListGetI.comp₂ comp_hist (pair n'' m'')
  let n := left.comp iP1
  let m := right.comp iP1
  let n' := cDiv.comp₂ n (cConst 2)
  let m' := cDiv.comp₂ m (cConst 2)
  let b₁ := cMod.comp₂ n (cConst 2)
  let b₂ := cMod.comp₂ m (cConst 2)
  let r := lookup n' m'
  cCovRec
    (cConst 0) <|
    cIfz.comp₃ n
      (cIft.comp₃ (c.comp₂ zero (cConst 1)) m zero) <|
    cIfz.comp₃ m
      (cIft.comp₃ (c.comp₂ (cConst 1) zero) n zero) <|
    cIft.comp₃ (c.comp₂ b₁ b₂)
    (succ.comp (cAdd.comp₂ r r))
    (cAdd.comp₂ r r)
def c_bitwise (c : Code) := cListGetLastI.comp ((c_bitwise_aux c).comp₂ (cConst 17) cId)
@[cp] theorem c_bitwise_prim {c} (hc : IsPrim c) : IsPrim (c_bitwise c) := by
  unfold c_bitwise;
  unfold c_bitwise_aux
  extract_lets;
  expose_names;
  have cpcomp_hist : IsPrim comp_hist := by apply_cp
  have cpiP1 : IsPrim iP1 := by apply_cp
  have cpn   : IsPrim n   := by apply_cp
  have cpm   : IsPrim m   := by apply_cp
  have cpn'  : IsPrim n'  := by apply_cp
  have cpm'  : IsPrim m'  := by apply_cp
  have cpb₁  : IsPrim b₁  := by apply_cp
  have cpb₂  : IsPrim b₂  := by apply_cp
  have cpr   : IsPrim r   := by apply_cp
  apply_cp 50
private lemma lt_pair_of_lt_lt {a c b d} (ha : a < c) (hb : b < d) : ⟪a,b⟫ < ⟪c,d⟫ := by
  have a0 : ⟪a,b⟫ < ⟪c,b⟫ := Nat.pair_lt_pair_left b ha
  have a1 : ⟪c,b⟫ < ⟪c,d⟫ := Nat.pair_lt_pair_right c hb
  exact Nat.lt_trans a0 a1
lemma c_bitwise_evp_rec_bounds {n m : ℕ} : ⟪(n + 1) / 2,(m + 1) / 2⟫ < ⟪n + 1,m + 1⟫ :=
  lt_pair_of_lt_lt (Nat.div_lt_self' n 0) (Nat.div_lt_self' m 0)
theorem c_bitwise_evp_0_0 {O c} :
    evalp O (c_bitwise c) ⟪0, 0⟫ =
    Nat.bitwise (fun a b => n2b <| evalp O c ⟪b2n a, b2n b⟫) 0 0 := by
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  rw [show Nat.pair 0 0 = 0 from rfl]
  simp [Nat.bitwise]

theorem c_bitwise_evp_0_m {O c m} :
    evalp O (c_bitwise c) ⟪0, m+1⟫ =
    Nat.bitwise (fun a b => n2b <| evalp O c ⟪b2n a, b2n b⟫) 0 (m+1) := by
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  let k := ⟪0, m+1⟫ - 1
  have hkP1: k+1 = ⟪0, m+1⟫ := Nat.sub_add_cancel pair_pos_of_right
  rw [← hkP1]
  -- more unfolding
  let (eq := hinp) inp := evalp O (c_bitwise_aux c) ⟪17, k⟫
  let (eq := hcri) cri := ⟪17, k, inp⟫
  unfold c_bitwise_aux at hinp; lift_lets at hinp
  simp [← hinp, ← hcri]
  -- simplify lets
  have hiP1 : evalp O iP1 cri = ⟪0,m+1⟫ := by simp [iP1, cri, hkP1]
  have hn : evalp O n cri = 0 := by simp [n, hiP1]
  have hm : evalp O m_1 cri = m+1 := by simp [m_1, hiP1]
  -- terminal simp
  simp [hn, hm, b2n, Nat.bitwise]
theorem c_bitwise_evp_n_0 {O c n} :
    evalp O (c_bitwise c) ⟪n+1, 0⟫ =
    Nat.bitwise (fun a b => n2b <| evalp O c ⟪b2n a, b2n b⟫) (n+1) 0 := by
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  let k := ⟪n+1, 0⟫ - 1
  have hkP1: k+1 = ⟪n+1, 0⟫ := Nat.sub_add_cancel pair_pos_of_left
  rw [← hkP1]
  -- more unfolding
  let (eq := hinp) inp := evalp O (c_bitwise_aux c) ⟪17, k⟫
  let (eq := hcri) cri := ⟪17, k, inp⟫
  unfold c_bitwise_aux at hinp; lift_lets at hinp
  simp [← hinp, ← hcri]
  -- simplify lets
  have hiP1 : evalp O iP1 cri = ⟪n+1, 0⟫ := by simp [iP1, cri, hkP1]
  have hn : evalp O n_1 cri = n+1 := by simp [n_1, hiP1]
  have hm : evalp O m cri = 0 := by simp [m, hiP1]
  -- terminal simp
  simp [hn, hm, b2n, Nat.bitwise]
theorem c_bitwise_evp_n_m {O c n m} : evalp O (c_bitwise c) ⟪n+1,m+1⟫ = (
    let n' := (n+1) / 2
    let m' := (m+1) / 2
    let b₁ := (n+1) % 2
    let b₂ := (m+1) % 2
    let r := evalp O (c_bitwise c) ⟪n',m'⟫
    if n2b <| evalp O c ⟪b₁, b₂⟫ then r+r+1 else r+r) := by
  lift_lets; extract_lets; expose_names
  unfold c_bitwise; unfold c_bitwise_aux;
  lift_lets; extract_lets; expose_names
  let k := ⟪n+1, m+1⟫ - 1
  have kP1_gt_0 : ⟪n+1, m+1⟫ > 0 := pair_pos_of_right
  have hkP1: k+1 = ⟪n+1, m+1⟫ := by
    exact Nat.sub_add_cancel kP1_gt_0
  rw [←hkP1]
  -- we will simplify terms in the goal with inp and cri (short for coverec input)
  let (eq := hinp) inp := evalp O (c_bitwise_aux c) ⟪17, k⟫
  let (eq := hcri) cri := ⟪17, k, inp⟫
  unfold c_bitwise_aux at hinp; lift_lets at hinp
  simp [← hinp, ← hcri]
  -- show that the code let-bindings correspond to our let-bindings
  have hiP1 : evalp O iP1 cri = ⟪n+1,m+1⟫ := by simp [iP1, cri, hkP1]
  have hn : evalp O n_1 cri = n+1 := by simp [n_1, hiP1]
  have hm : evalp O m_1 cri = m+1 := by simp [m_1, hiP1]
  have hn' : evalp O n'_1 cri = n' := by simp [n'_1, hn, n']
  have hm' : evalp O m'_1 cri = m' := by simp [m'_1, hm, m']
  have hb₁ : evalp O b₁_1 cri = b₁ := by simp [b₁_1, hn, b₁]
  have hb₂ : evalp O b₂_1 cri = b₂ := by simp [b₂_1, hm, b₂]
  have hr : evalp O r_1 cri = r := by
    simp only [comp₂_evp, evalp, pair_r, hn', hm', cListGetI_evp, r_1, lookup, comp_hist, cri,
      inp]
    simp only [r]
    unfold c_bitwise c_bitwise_aux
    lift_lets
    have : ⟪n',m'⟫ ≤ k := by
      simp only [k]
      apply Nat.le_of_lt_succ
      simpa [Nat.sub_add_cancel pair_pos_of_right] using c_bitwise_evp_rec_bounds
    simp [this]
  simp [hn, hm, hb₁, hb₂, hr]
@[simp, evp_simps] theorem c_bitwise_evp {O c} :
    evalp O (c_bitwise c) =
    Nat.unpaired2 (Nat.bitwise (fun a b => n2b <| evalp O c ⟪b2n a, b2n b⟫)) := by
  funext nm
  induction nm using Nat.strong_induction_on with
  | h nm ih =>
  let n := nm.left; let m := nm.right
  have nm_eq : nm = Nat.pair n m := Eq.symm pair_lr
  rw [nm_eq]
  match hn_val : n, hm_val : m with
  | 0,    0    => simp [c_bitwise_evp_0_0]
  | 0,    m+1  => simp [c_bitwise_evp_0_m]
  | n+1,  0    => simp [c_bitwise_evp_n_0]
  | n+1,  m+1  =>
    simp only [c_bitwise_evp_n_m, Nat.unpaired2, pair_l, pair_r]
    have b0 : ⟪(n+1)/2, (m+1)/2⟫ < nm := by
      simp only [nm_eq]
      exact c_bitwise_evp_rec_bounds
    have ih0 := ih ⟪(n+1)/2, (m+1)/2⟫ b0
    have rw0 {x} : b2n (decide ((x + 1) % 2 = 1)) = (x + 1) % 2 := by
      cases Classical.em ((x + 1) % 2 = 1) with
      | inl h => simp [h, b2n]
      | inr h =>
        simp only [b2n, h, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact (Nat.mod_two_ne_one.mp h).symm
    unfold Nat.bitwise
    simp [ih0, rw0]
end Oracle.Single.Code
end bitwise

section lor
namespace Oracle.Single.Code
def c_lor := cIfz.comp₃ left
  (cIfz.comp₃ right zero (cConst 1))
  (cConst 1)
@[cp] theorem c_lor_prim : IsPrim c_lor := by unfold c_lor; apply_cp
theorem c_lor_evp {O a b} : evalp O c_lor ⟪a, b⟫ = b2n (n2b a || n2b b) := by
  simp [c_lor, n2b, b2n]
  split <;> simp_all
@[simp, evp_simps] theorem c_lor_evp' {O : ℕ → ℕ} :
    (fun a b => n2b <| evalp O c_lor ⟪b2n a, b2n b⟫) = Bool.or := by
  funext a b;
  simp [c_lor, n2b, b2n]
  split <;> simp_all
end Oracle.Single.Code
end lor

section lxor
namespace Oracle.Single.Code
def c_lxor := cIfz.comp₃ left
  (cIfz.comp₃ right zero (cConst 1))
  (cIfz.comp₃ right (cConst 1) zero)
@[cp] theorem c_lxor_prim : IsPrim c_lxor := by unfold c_lxor; apply_cp
theorem c_lxor_evp {O a b} : evalp O c_lxor ⟪a, b⟫ = b2n (n2b a ^^ n2b b) := by
  simp [c_lxor, n2b, b2n]
  split <;> simp_all
@[simp, evp_simps] theorem c_lxor_evp' {O : ℕ → ℕ} :
    (fun a b => n2b <| evalp O c_lxor ⟪b2n a, b2n b⟫) = Bool.xor := by
  funext a b;
  simp [c_lxor, n2b, b2n]
  split <;> simp_all
end Oracle.Single.Code
end lxor

section land
namespace Oracle.Single.Code
def c_land := cIfz.comp₃ left
  zero
  (cIfz.comp₃ right zero (cConst 1))
@[cp] theorem c_land_prim : IsPrim c_land := by unfold c_land; apply_cp
theorem c_land_evp {O a b} : evalp O c_land ⟪a, b⟫ = b2n (n2b a && n2b b) := by
  simp [c_land, n2b, b2n]
  split <;> simp_all
@[simp, evp_simps] theorem c_land_evp' {O : ℕ → ℕ} :
    (fun a b => n2b <| evalp O c_land ⟪b2n a, b2n b⟫) = Bool.and := by
  funext a b;
  simp [c_land, n2b, b2n]
end Oracle.Single.Code
end land

section or
namespace Oracle.Single.Code
def c_or := c_bitwise (c_lor)
@[cp] theorem c_or_prim : IsPrim c_or := by unfold c_or; apply_cp
@[simp, evp_simps] theorem c_or_evp {O x y} : evalp O c_or ⟪x,y⟫ = (x ||| y) := by simp [c_or]; rfl
end Oracle.Single.Code
end or

section and
namespace Oracle.Single.Code
def c_and := c_bitwise (c_land)
@[cp] theorem c_and_prim : IsPrim c_and := by unfold c_and; apply_cp
@[simp, evp_simps] theorem c_and_evp {O x y} : evalp O c_and ⟪x,y⟫ = x &&& y := by simp [c_and]; rfl
end Oracle.Single.Code
end and

section xor
namespace Oracle.Single.Code
def c_xor := c_bitwise (c_lxor)
@[cp] theorem c_xor_prim : IsPrim c_xor := by unfold c_xor; apply_cp
@[simp, evp_simps] theorem c_xor_evp {O x y} : evalp O c_xor ⟪x,y⟫ = x ^^^ y := by simp [c_xor]; rfl
end Oracle.Single.Code
end xor
