import Computability.Constructions

#eval Encodable.encode (Option.none:Option ℕ)
#eval Encodable.encode (Option.some 1:Option ℕ)
#eval Encodable.encode (Option.some 2:Option ℕ)



















section div
namespace Nat.RecursiveIn.Code
def c_div_flip2 :=
  let dividend := succ.comp $ left.comp right
  let divisor := left
  let list_of_prev_values := right.comp right

  -- c_l_get_last.comp $
  c_cov_rec

  (c_const 0) $            -- base case: if dividend is 0, return 0

  c_ifz.comp₂ divisor $    -- in general, test if the divisor is zero
  pair (c_const 0) $       -- if so, return 0
  c_if_lt_te.comp₄ dividend divisor (c_const 0) $ -- if dividend < divisor, return 0
  (succ.comp (c_l_get.comp₂ list_of_prev_values (c_sub.comp₂ dividend divisor))) -- else return (dividend-divisor)/divisor+1

-- def c_div := c_div_flip.comp (pair right left)
-- i want the inductive case to be simplified to an expression involving c_div_flip2.
-- this cannot be done after unfolding c_div_flip2, as that will destroy all 'c_div_flip2' 's.
-- not sure how to do it automatically. in the meanwhile, i can explicitly define it, like below:

-- set_option trace.Meta.Tactic.simp true in
theorem c_div_flip_evp_aux_aux_test2 :
  Nat.list_get_last (eval_prim O c_div_flip2 (Nat.pair (d+1) (n+1)))
    =
  if n<d then 0 else Nat.list_get_last (eval_prim O c_div_flip2 (Nat.pair (d+1) (n-d))) + 1
    := by

    rw (config := {occs := .pos [1]}) [c_div_flip2]
    -- simp? [eval_prim]

    -- simp [eval_prim,
    --   -c_cov_rec_evp_0,
    --   -c_cov_rec_evp_1,
    --   -c_cov_rec_evp_2,
    --   -c_cov_rec_evp_3,
    --   -c_cov_rec_evp_4,
    -- ]

    -- simp only [eval_prim]
    simp only [c_cov_rec_evp_3]
    -- simp only [c_cov_rec_evp_0]
    -- simp? [eval_prim]

    have wtf :
      eval_prim O
      (let dividend := succ.comp $ left.comp right
      let divisor := left
      let list_of_prev_values := right.comp right

      -- c_l_get_last.comp $
      c_cov_rec

      (c_const 0) $            -- base case: if dividend is 0, return 0

      c_ifz.comp₂ divisor $    -- in general, test if the divisor is zero
      pair (c_const 0) $       -- if so, return 0
      c_if_lt_te.comp₄ dividend divisor (c_const 0) $ -- if dividend < divisor, return 0
      (succ.comp (c_l_get.comp₂ list_of_prev_values (c_sub.comp₂ dividend divisor)))) -- else return (dividend-divisor)/divisor+1)
      (Nat.pair (d + 1) n)
    =
      eval_prim O c_div_flip2 (Nat.pair (d + 1) n)
      := by exact rfl

    -- have fyhbuioAWEFBHYUIOASRGYBHUIOASRFGBHUIORFSEBYUIOQ : (eval_prim O
    --       ((c_const 0).c_cov_rec
    --         (c_ifz.comp₂ left
    --           ((c_const 0).pair
    --             (c_if_lt_te.comp₄ (succ.comp (left.comp right)) left (c_const 0)
    --               (succ.comp (c_l_get.comp₂ (right.comp right) (c_sub.comp₂ (succ.comp (left.comp right)) left)))))))
    --       (Nat.pair (d + 1) n)) =eval_prim O c_div_flip2 (Nat.pair (d+1) (n)) := by exact rfl
    -- rw [fyhbuioAWEFBHYUIOASRGYBHUIOASRFGBHUIORFSEBYUIOQ]
    
    rw [wtf]
    simp [eval_prim]
    have h0: n-d≤n := by exact sub_le n d
    #check c_cov_rec_evp_2 h0
    unfold c_div_flip2
    rw [c_cov_rec_evp_2 h0]



    
    -- simp only [comp₂_evp]
    -- simp only [eval_prim]
    -- simp only [l]
    -- simp only [unpair_pair]
    -- simp only [c_const_evp]
    -- simp only [comp₄_evp]

    -- -- simp only [comp₂_evp]
    -- simp only [eval_prim]
    -- simp only [l]
    -- simp only [unpair_pair]
    -- simp only [c_const_evp]
    -- -- simp only [comp₄_evp]

    
    -- simp only [r]
    -- simp only [succ_eq_add_one]
    -- simp only [c_sub_evp]
    -- simp only [unpaired]
    -- simp only [sub_eq]
    -- simp only [reduceSubDiff]
    -- simp only [c_l_get_evp]
    -- simp only [tsub_le_iff_right]
    -- simp only [le_add_iff_nonneg_right]
    -- simp only [_root_.zero_le]
    -- simp only [c_cov_rec_evp_2]
    -- simp only [c_if_lt_te_evp]
    -- simp only [add_lt_add_iff_right]
    -- simp only [c_ifz_evp]
    -- simp only [Nat.add_eq_zero]
    -- simp only [one_ne_zero]
    -- simp only [and_false]
    -- simp only [↓reduceIte]




    
    have rwh : (eval_prim O
          ((c_const 0).c_cov_rec
            (c_ifz.comp₂ left
              ((c_const 0).pair
                (c_if_lt_te.comp₄ (succ.comp (left.comp right)) left (c_const 0)
                  (succ.comp (c_l_get.comp₂ (right.comp right) (c_sub.comp₂ (succ.comp (left.comp right)) left)))))))
          (Nat.pair (d + 1) (n - d))).list_get_last = eval_prim O c_div_flip (Nat.pair (d + 1) (n - d)) := by
            rw [c_div_flip]
            simp [eval_prim]
    rw [rwh]
    -- calc

    -- rw (config := {occs := .pos [1]}) [c_div_flip]
    -- simp [eval_prim]



    -- rw [c_div_flip]

    -- simp only [eval_prim]
    -- simp [c_cov_rec_evp_0]
    -- simp [eval_prim]

    -- simp? [eval_prim] says simp only [eval_prim, c_cov_rec_evp_0, comp₂_evp, l, unpair_pair, c_const_evp, comp₄_evp, r,
    --   succ_eq_add_one, c_sub_evp, unpaired, sub_eq, reduceSubDiff, c_l_get_evp, tsub_le_iff_right,
    --   le_add_iff_nonneg_right, _root_.zero_le, c_cov_rec_evp_2, c_if_lt_te_evp,
    --   add_lt_add_iff_right, c_ifz_evp, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    --   c_l_get_last_evp, list_get_last_append]













































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

  -- c_l_get_last.comp $
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

set_option maxHeartbeats 5000000 in
-- set_option maxHeartbeats 1000000 in
-- set_option maxHeartbeats 1000 in
-- set_option trace.Meta.Tactic.simp true in
@[simp] theorem c_replace_oracle_evp_aux_aux (h:n%4=0):
Nat.list_get_last (eval_prim O (c_replace_oracle) (Nat.pair o ((n+4)+1)))
  =
  -- let m:=n.div2.div2
  let m:=(n/2)/2
  let ml := Nat.list_get_last (eval_prim O (c_replace_oracle) (Nat.pair o m.l))
  let mr := Nat.list_get_last (eval_prim O (c_replace_oracle) (Nat.pair o m.r))

  2*(2*(Nat.pair (ml) (mr))  )   + 5
  -- if n%4=0 then 2*(2*(Nat.pair (ml) (mr))  )   + 5 else
  -- if n%4=1 then 2*(2*(Nat.pair (ml) (mr))  )+1 + 5 else
  -- if n%4=2 then 2*(2*(Nat.pair (ml) (mr))+1)   + 5 else
  --               2*(2*(ml                )+1)+1 + 5



 := by
  -- rw [ml]
  rw (config := {occs := .pos [1]}) [c_replace_oracle]
  -- rw [c_replace_oracle]
  simp only [c_cov_rec_evp_3]








  have wtfman1 :
  eval_prim O
    (  let o               := left
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

    -- c_l_get_last.comp $
    c_cov_rec

    (c_const 0) $

    c_if_eq_te.comp₄ input_to_decode (c_const 1) (c_const 1) $
    c_if_eq_te.comp₄ input_to_decode (c_const 2) (c_const 2) $
    c_if_eq_te.comp₄ input_to_decode (c_const 3) (c_const 3) $
    c_if_eq_te.comp₄ input_to_decode (c_const 4) o           $
    c_if_eq_te.comp₄ nMod4           (c_const 0) (pair_code) $
    c_if_eq_te.comp₄ nMod4           (c_const 1) (comp_code) $
    c_if_eq_te.comp₄ nMod4           (c_const 2) (prec_code) $
                                                  rfind'_code)
    (Nat.pair o (n+4))
  =
    eval_prim O c_replace_oracle (Nat.pair o (n+4))
    :=
  by exact rfl
  rw [wtfman1]

  simp [eval_prim, h]

  have h2: (n/2/2)≤n := by
    exact le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
  -- have h0: (n/2/2).l≤n/2/2 := by
  --   exact 
  -- have h1 : (n/2/2).l≤n := by exact 
  -- have h1 : (n/2/2).l≤n := by exact Nat.le_trans h0 h2
  -- have h1' : (unpair (n / 2 / 2)).1≤n := by exact Nat.le_trans h0 h2
  have h3 : (n/2/2).l≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_left_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
  have h4 : (n/2/2).r≤n+4 := by exact le_add_right_of_le (Nat.le_trans (unpair_right_le (n/2/2)) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
    
  -- #check c_cov_rec_evp_2 h1
  unfold c_replace_oracle
  rw [c_cov_rec_evp_2 h3]
  rw [c_cov_rec_evp_2 h4]

  -- simp
  simp only []
  simp

  #check mul_comm
  rw [mul_comm]
  simp
  rw [mul_comm]
  -- exact rfl
  -- exact rfl
  



















  
  -- simp only [eval_prim]

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
