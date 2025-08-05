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
    
    -- rw [wtf]
    -- change eval_prim O c_div_flip2 (Nat.pair (d + 1) n)
    change (eval_prim O c_div_flip2 (Nat.pair (d + 1) n)) with (eval_prim O c_div_flip2 (Nat.pair (d + 1) n))

    
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


def test (x:ℕ) := 3*3*3*x*3*3*3

theorem 
