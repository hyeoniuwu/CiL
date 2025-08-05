import Computability.Constructions

#eval Encodable.encode (Option.none:Option ℕ)
#eval Encodable.encode (Option.some 1:Option ℕ)
#eval Encodable.encode (Option.some 2:Option ℕ)

section replace_oracle
namespace Nat.RecursiveIn.Code
def encodeCode_replace_oracle (o:ℕ) : Code → ℕ
| Code.zero        => 0
| Code.succ        => 1
| Code.left        => 2
| Code.right       => 3
| Code.oracle      => o
| Code.pair cf cg  => 2*(2*(Nat.pair (encodeCode cf) (encodeCode cg))  )   + 5
| Code.comp cf cg  => 2*(2*(Nat.pair (encodeCode cf) (encodeCode cg))  )+1 + 5
| Code.prec cf cg  => 2*(2*(Nat.pair (encodeCode cf) (encodeCode cg))+1)   + 5
| Code.rfind' cf   => 2*(2*(encodeCode cf                            )+1)+1 + 5
def replace_oracle (o:ℕ) := fun n => (encodeCode_replace_oracle o (decodeCode n))




/-- `eval c_replace_oracle (o,code)` = `code` but with calls to oracle replaced with calls to code `o` -/
def c_replace_oracle :=
  let o               := left
  let input_to_decode := succ.comp (left.comp right)
  let comp_hist       := right.comp right
  let n               := c_sub.comp₂ input_to_decode (c_const 5)
  let m               := c_div2.comp $ c_div2.comp n
  let ml              := c_l_get.comp₂ comp_hist (left.comp m)
  let mr              := c_l_get.comp₂ comp_hist (right.comp m)
  let nMod4           := c_mod.comp₂ n (c_const 4)
  let pair_code       := c_add.comp₂ (            c_mul2.comp $             c_mul2.comp (pair ml mr)) (c_const 5)
  let comp_code       := c_add.comp₂ (succ.comp $ c_mul2.comp $             c_mul2.comp (pair ml mr)) (c_const 5)
  let prec_code       := c_add.comp₂ (            c_mul2.comp $ succ.comp $ c_mul2.comp (pair ml mr)) (c_const 5)
  let rfind'_code     := c_add.comp₂ (succ.comp $ c_mul2.comp $ succ.comp $ c_mul2.comp ml          ) (c_const 5)

  c_l_get_last.comp $
  c_cov_rec

  (c_const 0) $

  c_if_eq_te.comp₄ input_to_decode (c_const 1) (c_const 1) $
  c_if_eq_te.comp₄ input_to_decode (c_const 2) (c_const 2) $
  c_if_eq_te.comp₄ input_to_decode (c_const 3) (c_const 3) $
  c_if_eq_te.comp₄ input_to_decode (c_const 4) o           $
  c_if_eq_te.comp₄ nMod4           (c_const 0) (pair_code) $
  c_if_eq_te.comp₄ nMod4           (c_const 1) (comp_code) $
  c_if_eq_te.comp₄ nMod4           (c_const 2) (prec_code) $
                                                rfind'_code

-- @[simp] theorem c_replace_oracle_ev_pr:code_prim (c_replace_oracle) := by unfold c_replace_oracle; repeat (constructor; try simp)

-- set_option maxHeartbeats 1000000 in
-- set_option maxHeartbeats 1000 in
@[simp] theorem c_replace_oracle_evp_aux_aux (h:n%4=0): eval_prim O (c_replace_oracle) (Nat.pair o ((n+4)+1)) =
  -- let m:=n.div2.div2
  let m:=(n/2)/2
  let ml := eval_prim O (c_replace_oracle) (Nat.pair o m.l)
  let mr := eval_prim O (c_replace_oracle) (Nat.pair o m.r)

  2*(2*(Nat.pair (ml) (mr))  )   + 5
  -- if n%4=0 then 2*(2*(Nat.pair (ml) (mr))  )   + 5 else
  -- if n%4=1 then 2*(2*(Nat.pair (ml) (mr))  )+1 + 5 else
  -- if n%4=2 then 2*(2*(Nat.pair (ml) (mr))+1)   + 5 else
  --               2*(2*(ml                )+1)+1 + 5



 := by
  simp only []
  rw (config := {occs := .pos [1]}) [c_replace_oracle]
  -- rw [c_replace_oracle]
  simp only [eval_prim]

  -- rw [eval_prim]
  -- simp only [c_cov_rec_evp_0]
  -- simp only [eval_prim, c_cov_rec_evp_0, comp₄_evp, l, r, unpair_pair, succ_eq_add_one, c_const_evp, comp₂_evp,
  -- c_sub_evp, unpaired, sub_eq, reduceSubDiff, c_mod_evp, c_div2_evp, c_l_get_evp, c_mul2_evp, c_add_evp, add_eq,
  -- c_if_eq_te_evp, reduceEqDiff, Nat.add_eq_right, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, OfNat.ofNat_ne_zero, h]



  -- simp? [eval_prim, h]
  rw (config := {occs := .pos [1]}) [c_replace_oracle]
  -- simp [eval_prim, h]

  -- simp?
  -- rw [c_cov_rec_evp_0]

  -- sorry
  -- simp only [div2]
  -- simp [eval_prim, h]
  -- simp [eval_prim]

set_option maxHeartbeats 3 in
@[simp] theorem c_replace_oracle_evp_aux: eval_prim O (c_replace_oracle) (Nat.pair o n) =
  let m:=n.div2.div2
  let ml := eval_prim O (c_replace_oracle) (Nat.pair o m.l)
  let mr := eval_prim O (c_replace_oracle) (Nat.pair o m.r)

  if n=0 then 0 else
  if n=1 then 1 else
  if n=2 then 2 else
  if n=3 then 3 else
  if n=4 then o else
  if n%4=0 then 2*(2*(Nat.pair (ml) (mr))  )   + 5 else
  if n%4=1 then 2*(2*(Nat.pair (ml) (mr))  )+1 + 5 else
  if n%4=2 then 2*(2*(Nat.pair (ml) (mr))+1)   + 5 else
                2*(2*(ml                )+1)+1 + 5



 :=
 match n with
  | 0 => by
    rw [c_replace_oracle]
    simp [eval_prim]
  | 1 => by
    rw [c_replace_oracle]
    simp [eval_prim]
  | 2 => by
    rw [c_replace_oracle]
    simp [eval_prim]
  | 3 => by
    rw [c_replace_oracle]
    simp [eval_prim]
  | 4 => by
    rw [c_replace_oracle]
    simp [eval_prim]
  | n + 5 => by
    sorry
    -- rw [c_replace_oracle]
    -- simp [eval_prim]
--  by

--   rw (config := {occs := .pos [1]}) [c_replace_oracle]
--   simp [eval_prim]
--   rw (config := {occs := .pos [1]}) [c_replace_oracle]
--   simp [eval_prim]

-- set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 3 in
@[simp] theorem c_replace_oracle_evp_1: eval_prim O (c_replace_oracle) = unpaired replace_oracle := by
  sorry
  funext oc
  let o:=oc.l
  let c:=oc.r
  have oc_eq : oc = Nat.pair o c := by exact Eq.symm (pair_unpair oc)
  rw [oc_eq]



  induction c using Nat.strong_induction_on with
  | _ c ih =>
    match c with
    | 0 =>
      sorry
      unfold c_replace_oracle
      unfold replace_oracle
      simp [encodeCode_replace_oracle, decodeCode]
      simp [eval_prim]
    | 1 =>
      sorry
      unfold c_replace_oracle
      unfold replace_oracle
      simp [encodeCode_replace_oracle, decodeCode]
      simp [eval_prim]
    | 2 =>
      sorry
      unfold c_replace_oracle
      unfold replace_oracle
      simp [encodeCode_replace_oracle, decodeCode]
      simp [eval_prim]
    | 3 =>
      sorry
      unfold c_replace_oracle
      unfold replace_oracle
      simp [encodeCode_replace_oracle, decodeCode]
      simp [eval_prim]
    | 4 =>
      sorry
      unfold c_replace_oracle
      unfold replace_oracle
      simp [encodeCode_replace_oracle, decodeCode]
      simp [eval_prim]
    | n + 5 =>
      let m := n.div2.div2
      have hm : m < n + 5 := by
        simp only [m, Nat.div2_val]
        exact lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)) (Nat.succ_le_succ (Nat.le_add_right _ _))
      have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
      have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
      -- have IH := encodeCode_decodeCode m
      -- have IH1 := encodeCode_decodeCode m.unpair.1
      -- have IH2 := encodeCode_decodeCode m.unpair.2
      -- conv_rhs => rw [← Nat.bit_decomp n, ← Nat.bit_decomp n.div2]
      -- simp only [decodeCode.eq_6]
      -- cases n.bodd <;> cases n.div2.bodd <;> simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]


      unfold c_replace_oracle
      unfold replace_oracle
      -- simp [encodeCode_replace_oracle, decodeCode]
      -- simp [eval_prim]

      cases n.bodd with
      | false => cases n.div2.bodd with
        | true =>
          have h0: (n+4+1)%4=2 := by sorry
          -- simp only [h0, ↓reduceIte]
          simp only []

        | false => sorry
      | true => sorry


      -- -- general case
      -- let m := n.div2.div2
      -- have hm : m < n + 5 := by
      --   -- your proof of this inequality
      --   sorry
      -- -- continue using `ih m`
      sorry

@[simp] theorem c_replace_oracle_ev:eval O (c_replace_oracle o) = (replace_oracle o) := by rw [← eval_prim_eq_eval c_replace_oracle_ev_pr]; simp only [c_replace_oracle_evp]
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.replace_oracle:Nat.PrimrecIn O (replace_oracle o) := by rw [← c_replace_oracle_evp]; apply code_prim_prop c_replace_oracle_ev_pr
theorem Nat.Primrec.replace_oracle:Nat.Primrec (replace_oracle o) := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.replace_oracle
end replace_oracle
