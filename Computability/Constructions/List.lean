import Computability.Constructions.Basic

open Nat
open Denumerable
open Encodable
open List

abbrev n2l := @ofNat (List ℕ) _
abbrev l2n := @encode (List ℕ) _
abbrev n2o := @ofNat (Option ℕ) _
abbrev o2n := @encode (Option ℕ) _

instance : OfNat (List ℕ) lN where ofNat := n2l lN
instance : Coe ℕ (List ℕ) := ⟨n2l⟩
instance : Coe (List ℕ) ℕ := ⟨l2n⟩

section list_nil
namespace Nat.RecursiveIn.Code
def c_list_nil := zero
@[simp] theorem c_list_nil_ev_pr:code_prim c_list_nil := by unfold c_list_nil; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_nil_evp :eval_prim O c_list_nil x = l2n ([]) := by simp [c_list_nil]
@[simp] theorem c_list_nil_ev :eval O c_list_nil x = l2n ([]) := by simp [←eval_prim_eq_eval c_list_nil_ev_pr]
end Nat.RecursiveIn.Code
end list_nil

section list_cons
namespace Nat.RecursiveIn.Code
def c_list_cons := succ
@[simp] theorem c_list_cons_ev_pr:code_prim c_list_cons := by unfold c_list_cons; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_cons_evp :eval_prim O c_list_cons (Nat.pair a lN)= l2n (List.cons a (n2l lN)) := by simp [c_list_cons]
@[simp] theorem c_list_cons_ev :eval O c_list_cons (Nat.pair a lN)= l2n (List.cons a (n2l lN)) := by simp [←eval_prim_eq_eval c_list_cons_ev_pr]
end Nat.RecursiveIn.Code
end list_cons

section list_tail
namespace Nat.RecursiveIn.Code
def c_list_tail := right.comp c_pred
@[simp] theorem c_list_tail_ev_pr:code_prim c_list_tail := by unfold c_list_tail; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_tail_evp : eval_prim O c_list_tail lN = l2n (List.tail (n2l lN)) := by
  simp [c_list_tail]
  by_cases hl:lN=0
  · simp [hl,r]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_tail_ev:eval O c_list_tail lN = l2n (List.tail (n2l lN)) := by simp [← eval_prim_eq_eval c_list_tail_ev_pr]
end Nat.RecursiveIn.Code
end list_tail

section list_head?
namespace Nat.RecursiveIn.Code
def c_list_head? := c_ifz.comp₃ c_id zero $ succ.comp (left.comp c_pred)
@[simp] theorem c_list_head?_ev_pr:code_prim c_list_head? := by unfold c_list_head?; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_head?_evp : eval_prim O c_list_head? lN = o2n (List.head? (n2l lN)) := by
  simp [c_list_head?]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_head?_ev:eval O c_list_head? lN = o2n (List.head? (n2l lN)) := by simp [← eval_prim_eq_eval c_list_head?_ev_pr]
end Nat.RecursiveIn.Code
end list_head?



section list_headI
namespace Nat.RecursiveIn.Code
def c_list_headI := c_ifz.comp₃ c_id zero (left.comp c_pred)
@[simp] theorem c_list_headI_ev_pr:code_prim c_list_headI := by unfold c_list_headI; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_headI_evp : eval_prim O c_list_headI lN = List.headI (n2l lN) := by
  simp [c_list_headI]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_headI_ev:eval O c_list_headI lN = List.headI (n2l lN) := by simp [← eval_prim_eq_eval c_list_headI_ev_pr]
end Nat.RecursiveIn.Code
end list_headI

section list_casesOn
namespace Nat.RecursiveIn.Code
def c_list_casesOn (cl cf cg:Code) :=
  let x := left.comp (c_pred.comp cl)
  let xs := right.comp (c_pred.comp cl)
  c_if_eq_te.comp₄ cl (c_const 0) cf (cg.comp₂ x xs)
@[simp] theorem c_list_casesOn_ev_pr (hcl:code_prim cl) (hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_list_casesOn cl cf cg) := by unfold c_list_casesOn; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_casesOn_evp : eval_prim O (c_list_casesOn cl cf cg) input =
  List.casesOn
  (n2l (eval_prim O cl input))
  (eval_prim O cf input)
  (fun x xs => eval_prim O cg (Nat.pair (@encode ℕ _ x) (l2n xs)))
  := by
  simp [c_list_casesOn]
  by_cases hl:(eval_prim O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
-- @[simp] theorem c_list_casesOn_ev :eval O (c_list_casesOn cl cf cg) input =
--   List.casesOn
--   (n2l (eval_prim O cl input))
--   (eval_prim O cf input)
--   (fun x xs => eval_prim O cg (Nat.pair (@encode ℕ _ x) (l2n xs))) := by
--     simp [← eval_prim_eq_eval c_list_casesOn_ev_pr]
end Nat.RecursiveIn.Code
end list_casesOn
section list_casesOn'
namespace Nat.RecursiveIn.Code
def c_list_casesOn' (cl cf cg:Code) :=
  c_if_eq_te.comp₄ cl (c_const 0) cf cg
@[simp] theorem c_list_casesOn'_ev_pr (hcl:code_prim cl) (hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_list_casesOn' cl cf cg) := by unfold c_list_casesOn'; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_casesOn'_evp : eval_prim O (c_list_casesOn' cl cf cg) input =
  List.casesOn
  (n2l (eval_prim O cl input))
  (eval_prim O cf input)
  (fun _ => eval_prim O cg input)
  := by
  simp [c_list_casesOn']
  by_cases hl:(eval_prim O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
-- @[simp] theorem c_list_casesOn'_ev :eval O (c_list_casesOn' cf cg) lN =
--   List.casesOn
--   (n2l lN)
--   (eval_prim O cf lN)
--   (fun x xs => eval_prim O cg (Nat.pair (@encode ℕ _ x) (l2n xs))) := by
--     simp [← eval_prim_eq_eval c_list_casesOn'_ev_pr]
end Nat.RecursiveIn.Code
end list_casesOn'

section list_drop
namespace Nat.RecursiveIn.Code
def c_list_drop :=
  (
    prec
    c_id $
    c_list_tail.comp (right.comp right)
  ).comp c_flip
@[simp] theorem c_list_drop_ev_pr:code_prim c_list_drop := by unfold c_list_drop; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_drop_evp : eval_prim O c_list_drop (Nat.pair i lN) = l2n (List.drop i (n2l lN)) := by
  simp [c_list_drop]
  by_cases hl:lN=0
  · simp [hl]
    induction i with
    | zero => simp
    | succ n ih => simp [ih]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
    induction i with
    | zero => simp
    | succ n ih => simp [ih]
@[simp] theorem c_list_drop_ev:eval O c_list_drop (Nat.pair i lN) = l2n (List.drop i (n2l lN)) := by simp [← eval_prim_eq_eval c_list_drop_ev_pr]
end Nat.RecursiveIn.Code
end list_drop

section list_getElem?
namespace Nat.RecursiveIn.Code
def c_list_getElem? := c_list_head?.comp (c_list_drop.comp c_flip)
@[simp] theorem c_list_getElem?_ev_pr:code_prim c_list_getElem? := by unfold c_list_getElem?; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_getElem?_evp : eval_prim O c_list_getElem? (Nat.pair lN i) = o2n (n2l lN)[i]? := by simp [c_list_getElem?]
@[simp] theorem c_list_getElem?_ev : eval O c_list_getElem? (Nat.pair lN i) = o2n (n2l lN)[i]? := by simp [← eval_prim_eq_eval c_list_getElem?_ev_pr]
end Nat.RecursiveIn.Code
end list_getElem?

section list_getI
namespace Nat.RecursiveIn.Code
def c_list_getI := c_pred.comp c_list_getElem?
@[simp] theorem c_list_getI_ev_pr:code_prim c_list_getI := by unfold c_list_getI; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_getI_evp : eval_prim O c_list_getI (Nat.pair lN i) = ((n2l lN).getI i) := by
  simp [c_list_getI]
  by_cases hl:i<(n2l lN).length <;> simp [hl, List.getI]
@[simp] theorem c_list_getI_ev : eval O c_list_getI (Nat.pair lN i) = ((n2l lN).getI i) := by simp [← eval_prim_eq_eval c_list_getI_ev_pr]
end Nat.RecursiveIn.Code
end list_getI

section nat_iterate
namespace Nat.RecursiveIn.Code
def c_nat_iterate (cf:Code) :=
  prec
  c_id
  (cf.comp (right.comp right))

@[simp] theorem c_nat_iterate_ev_pr (hcf:code_prim cf) : code_prim (c_nat_iterate cf) := by unfold c_nat_iterate; repeat (first|assumption|simp|constructor)
@[simp] theorem c_nat_iterate_evp : eval_prim O (c_nat_iterate cf) (Nat.pair input i) = (eval_prim O cf)^[i] (input) := by
  simp [c_nat_iterate]
  induction i with
  | zero => simp
  | succ n ih =>
    simp [ih]
    exact Eq.symm (Function.iterate_succ_apply' (eval_prim O cf) n input)
-- @[simp] theorem c_nat_iterate_ev :eval O (c_nat_iterate cf) (Nat.pair input i) = (eval_prim O cf)^[i] (input) := by
--     simp [← eval_prim_eq_eval c_nat_iterate_ev_pr]
end Nat.RecursiveIn.Code
end nat_iterate

/-
`foldl :: (a -> b -> a) -> a -> [b] -> a`
`foldl fn acc [] = acc`
`foldl fn acc (x:xs) = foldl fn (fn acc x) xs`
-/
section list_foldl
namespace Nat.RecursiveIn.Code
def c_list_foldl_aux (cf:Code) :=
  let x:=left.comp (c_pred.comp right)
  let xs:=right.comp (c_pred.comp right)
  c_list_casesOn' right c_id (pair (cf.comp₂ left x) (xs))
def c_list_foldl_aux2 (cf:Code) := (c_nat_iterate (c_list_foldl_aux cf)).comp₂ c_id right
def c_list_foldl (cf:Code) := left.comp (c_list_foldl_aux2 cf)
@[simp] theorem c_list_foldl_ev_pr(hcf:code_prim cf):code_prim (c_list_foldl cf) := by unfold c_list_foldl; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_foldl_aux_evp   : eval_prim O (c_list_foldl_aux cf) (Nat.pair init lN) = if (n2l lN) = [] then (Nat.pair init lN) else Nat.pair (eval_prim O cf (Nat.pair init (n2l lN).headI)) (l2n (List.tail (n2l lN))) := by
  simp [c_list_foldl_aux]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_foldl_evp : eval_prim O (c_list_foldl cf) (Nat.pair init lN) =
  (
    List.foldl
    (fun a b => eval_prim O cf (Nat.pair a b))
    (init)
    (n2l lN)
  )
  := by
  simp [c_list_foldl,c_list_foldl_aux2]
  
  suffices ∀ n,
  (eval_prim O cf.c_list_foldl_aux)^[n] (Nat.pair init lN)
    =
  Nat.pair (((n2l lN).take n).foldl (fun a b => eval_prim O cf (Nat.pair a b)) init) (l2n ((n2l lN).drop n)) by
    -- refine hF.of_eq fun a => ?_
    rw [this]
    rw (config := {occs := .pos [1]}) [show lN=(l2n (n2l lN)) from by simp]
    rw [List.take_of_length_le (length_le_encode _)]
    simp
  introv
  induction n with
  | zero => simp
  | succ n ih =>
    
    by_cases hl:lN=0
    ·
      simp [hl]
      have fixedp : eval_prim O cf.c_list_foldl_aux (Nat.pair init 0) = Nat.pair init 0 := by simp
      apply Function.iterate_fixed fixedp
    · 
      simp only [Function.iterate_succ']
      
      by_cases hl2:(n2l lN).length ≤ n
      · 
        simp [ih]
        simp [hl2]
        simp [List.drop_of_length_le hl2]
        simp [List.take_of_length_le hl2]
        simp [List.take_of_length_le (le_add_right_of_le hl2)]
        exact le_add_right_of_le hl2
      · 
        simp [ih]
        simp [hl2]

        have lgt_1 : (n2l lN).length ≥ n+1 := by exact gt_of_not_le hl2
        have vasd2 : (List.take (n + 1) (n2l lN)) = (List.take n (n2l lN)) ++ [(n2l lN)[n]] := by simp
        have vasd_aux : (n2l lN)[n] = (List.drop n (n2l lN)).headI := by
          have abc2 : List.length (List.drop n (n2l lN)) > 0 := by (expose_names; exact List.lt_length_drop lgt_1)
          have asdasdasd := @List.getElem_drop ℕ (n2l lN) n 0 abc2
          simp only [add_zero] at asdasdasd
          rw [←asdasdasd]
          have asd := List.exists_cons_of_length_pos abc2
          rcases asd with ⟨k,t,hkt⟩
          simp [hkt]

        have vasd : (List.take (n + 1) (n2l lN)) = (List.take n (n2l lN)) ++ [(List.drop n (n2l lN)).headI] := by
          rw [vasd2]
          rw [vasd_aux]
        rw [vasd]
        simp

-- @[simp] theorem c_list_foldl_ev : eval O (c_list_foldl cf) (Nat.pair init lN) =
--   (
--     List.foldl
--     (fun a b => eval_prim O cf (Nat.pair a b))
--     (init)
--     (n2l lN)
--   ) := by rw [← eval_prim_eq_eval c_list_foldl_ev_pr]; simp only [c_list_foldl_evp]
end Nat.RecursiveIn.Code
end list_foldl

-- reverse = foldl (flip (:)) []
section list_reverse
namespace Nat.RecursiveIn.Code
def c_list_reverse := (c_list_foldl (c_list_cons.comp c_flip)).comp₂ c_list_nil c_id
@[simp] theorem c_list_reverse_ev_pr:code_prim c_list_reverse := by unfold c_list_reverse; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_reverse_evp : eval_prim O c_list_reverse lN =  l2n (List.reverse (n2l lN)) := by
  simp only [c_list_reverse]
  simp [-encode_list_cons, -encode_list_nil]
  -- -encode_list_cons, -encode_list_nil these are needed!
  have aux : ∀ l r, List.foldl (fun (s : ℕ) (b : ℕ) => l2n (b :: (n2l s))) r l = l2n (List.reverseAux l (n2l r)) := fun l => by
    induction l with
    | nil => simp [*, List.reverseAux]
    | cons head tail ih => simp [*, List.reverseAux, -encode_list_cons]
  rw [aux (n2l lN) (l2n [])]
  simp
@[simp] theorem c_list_reverse_ev : eval O c_list_reverse lN =  l2n (List.reverse (n2l lN)) := by simp [← eval_prim_eq_eval c_list_reverse_ev_pr]
end Nat.RecursiveIn.Code
end list_reverse

/-
`foldr :: (a -> b -> b) -> b -> [a] -> b`
`foldr fn acc [] = acc`
`foldr fn acc (x:xs) = fn x (foldr fn acc xs)`
-/
section list_foldr
namespace Nat.RecursiveIn.Code
def c_list_foldr (cf:Code) := (c_list_foldl (cf.comp c_flip)).comp₂ left (c_list_reverse.comp right)
@[simp] theorem c_list_foldr_ev_pr(hcf:code_prim cf):code_prim (c_list_foldr cf) := by unfold c_list_foldr; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_foldr_evp : eval_prim O (c_list_foldr cf) (Nat.pair init lN) =
  (
    List.foldr
    (fun a b => eval_prim O cf (Nat.pair a b))
    (init)
    (n2l lN)
  )
  := by simp [c_list_foldr]
-- @[simp] theorem c_list_foldr_ev : eval O (c_list_foldr cf) (Nat.pair init lN) =
--   (
--     List.list_foldr
--     (fun a b => eval_prim O cf (Nat.pair a b))
--     (init)
--     (n2l lN)
--   ) := by rw [← eval_prim_eq_eval c_list_foldr_ev_pr]; simp only [c_list_foldr_evp]
end Nat.RecursiveIn.Code
end list_foldr

-- https://hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Data.Foldable.html#length
section list_length
namespace Nat.RecursiveIn.Code
def c_list_length := (c_list_foldl (succ.comp left)).comp₂ zero c_id
@[simp] theorem c_list_length_ev_pr:code_prim c_list_length := by unfold c_list_length; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_length_evp : eval_prim O c_list_length lN = List.length (n2l lN) := by simp [c_list_length]
@[simp] theorem c_list_length_ev : eval O c_list_length lN = List.length (n2l lN) := by simp [← eval_prim_eq_eval c_list_length_ev_pr]
end Nat.RecursiveIn.Code
end list_length

section list_getLast?
namespace Nat.RecursiveIn.Code
def c_list_getLast? := c_list_getElem?.comp₂ c_id (c_pred.comp $ c_list_length.comp c_id)
@[simp] theorem c_list_getLast?_ev_pr:code_prim c_list_getLast? := by unfold c_list_getLast?; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_getLast?_evp : eval_prim O c_list_getLast? lN = o2n (List.getLast? (n2l lN)) := by
  simp [c_list_getLast?]
  exact Eq.symm List.getLast?_eq_getElem?
@[simp] theorem c_list_getLast?_ev:eval O c_list_getLast? lN = o2n (List.getLast? (n2l lN)) := by simp [← eval_prim_eq_eval c_list_getLast?_ev_pr]
end Nat.RecursiveIn.Code
end list_getLast?

section opt_iget
namespace Nat.RecursiveIn.Code
def c_opt_iget := c_pred
@[simp] theorem c_opt_iget_ev_pr:code_prim c_opt_iget := by unfold c_opt_iget; repeat (first|assumption|simp|constructor)
@[simp] theorem c_opt_iget_evp : eval_prim O c_opt_iget o = Option.iget (n2o o) := by
  simp [c_opt_iget]
  by_cases ho:o=0
  · simp [ho]; exact rfl
  · have asd := exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho)
    rcases asd with ⟨k,hk⟩
    simp [←hk]
    have rwma : n2o (k + 1) = Option.some k := by exact rfl
    rw [rwma]
@[simp] theorem c_opt_iget_ev:eval O c_opt_iget o = Option.iget (n2o o) := by simp [← eval_prim_eq_eval c_opt_iget_ev_pr]
end Nat.RecursiveIn.Code
end opt_iget

section list_getLastI
namespace Nat.RecursiveIn.Code
def c_list_getLastI := c_opt_iget.comp c_list_getLast?
@[simp] theorem c_list_getLastI_ev_pr:code_prim c_list_getLastI := by unfold c_list_getLastI; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_getLastI_evp : eval_prim O c_list_getLastI lN = List.getLastI (n2l lN) := by
  simp [c_list_getLastI]
  exact Eq.symm (List.getLastI_eq_getLast? (n2l lN))
@[simp] theorem c_list_getLastI_ev:eval O c_list_getLastI lN = List.getLastI (n2l lN) := by simp [← eval_prim_eq_eval c_list_getLastI_ev_pr]
end Nat.RecursiveIn.Code
end list_getLastI

/-
(++) []     ys = ys
(++) (x:xs) ys = x : xs ++ ys
-/
section list_append
namespace Nat.RecursiveIn.Code
def c_list_append := (c_list_foldr (c_list_cons)).comp c_flip
@[simp] theorem c_list_append_ev_pr:code_prim c_list_append := by unfold c_list_append; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_append_evp : eval_prim O c_list_append (Nat.pair l1N l2N) = l2n ((n2l l1N) ++ (n2l l2N)) := by
  simp [c_list_append, -encode_list_cons, -encode_list_nil]
  induction (n2l l1N) with
  | nil => simp
  | cons head tail ih => simp [ih, -encode_list_cons, -encode_list_nil]
@[simp] theorem c_list_append_ev : eval O c_list_append (Nat.pair l1N l2N) = l2n ((n2l l1N) ++ (n2l l2N)) := by simp [← eval_prim_eq_eval c_list_append_ev_pr]
end Nat.RecursiveIn.Code
end list_append

section list_concat
namespace Nat.RecursiveIn.Code
def c_list_concat := c_list_append.comp₂ left (c_list_cons.comp₂ right c_list_nil)
@[simp] theorem c_list_concat_ev_pr:code_prim c_list_concat := by unfold c_list_concat; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_concat_evp : eval_prim O c_list_concat (Nat.pair lN i) = l2n ((n2l lN)++[i]) := by
  simp [c_list_concat, -encode_list_cons, -encode_list_nil]
@[simp] theorem c_list_concat_ev : eval O c_list_concat (Nat.pair lN i) = l2n ((n2l lN)++[i]) := by simp [← eval_prim_eq_eval c_list_concat_ev_pr]
end Nat.RecursiveIn.Code
end list_concat

-- https://hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Base.html#map
section list_map
namespace Nat.RecursiveIn.Code
def c_list_map (cf:Code) := (c_list_foldr (c_list_cons.comp₂ (cf.comp left) right)).comp₂ (c_list_nil) (c_id)
@[simp] theorem c_list_map_ev_pr (hcf:code_prim cf): code_prim (c_list_map cf) := by unfold c_list_map; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_map_evp : eval_prim O (c_list_map cf) lN = l2n ((n2l lN).map (eval_prim O cf)) := by
  simp [c_list_map, -encode_list_cons, -encode_list_nil]
  induction (n2l lN) with
  | nil => simp
  | cons head tail ih => simp [ih, -encode_list_cons, -encode_list_nil]
-- @[simp] theorem c_list_map_ev : eval O (c_list_map cf) lN = l2n ((n2l lN).map (eval_prim O cf)) := by simp [← eval_prim_eq_eval c_list_map_ev_pr]
end Nat.RecursiveIn.Code
end list_map

section list_range
namespace Nat.RecursiveIn.Code
def c_list_range :=
  let prev_list := right.comp right
  let i := (left.comp right)
  (prec
  (c_list_nil)
  (c_list_concat.comp₂ prev_list i)).comp₂ zero c_id
@[simp] theorem c_list_range_ev_pr : code_prim c_list_range := by unfold c_list_range; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_range_evp : eval_prim O c_list_range n = l2n (List.range n) := by
  simp [c_list_range, -encode_list_cons, -encode_list_nil]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [-encode_list_cons, -encode_list_nil, ih]
    exact Eq.symm List.range_succ
@[simp] theorem c_list_range_ev : eval O c_list_range n = l2n (List.range n) := by simp [← eval_prim_eq_eval c_list_range_ev_pr]
end Nat.RecursiveIn.Code
end list_range



-- 


@[simp] theorem getLastI_append {y:ℕ}: (x++[y]).getLastI = y := by
  rw [getLastI_eq_getLast?]
  simp
