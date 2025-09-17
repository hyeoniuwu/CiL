import Computability.Constructions.Option

open Nat
open Denumerable
open Encodable
open List

abbrev n2l := @ofNat (List ℕ) _
abbrev l2n := @encode (List ℕ) _
-- abbrev n2o := @ofNat (Option ℕ) _
-- abbrev o2n := @encode (Option ℕ) _

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
  (fun x xs => eval_prim O cg (Nat.pair x (l2n xs)))
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

section list_get
namespace Nat.RecursiveIn.Code
def c_list_get := c_list_getI
@[simp] theorem c_list_get_ev_pr:code_prim c_list_get := by unfold c_list_get; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_get_evp (h:i<(n2l lN).length) : eval_prim O c_list_get (Nat.pair lN i) = (n2l lN)[i] := by
  simp [c_list_get]
  simp [getI]
  by_cases hl:i<(n2l lN).length
  · simp [hl]
  · contradiction
@[simp] theorem c_list_get_ev (h:i<(n2l lN).length) : eval O c_list_get (Nat.pair lN i) = (n2l lN)[i] := by
  simp [← eval_prim_eq_eval c_list_get_ev_pr]
  simp [h]
end Nat.RecursiveIn.Code
end list_get

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
@[simp] theorem iget_evp_2 (h:o≠0):  Option.iget (n2o o) = o-1:= by
  have asd : o = (o-1)+1 := by exact Eq.symm (succ_pred_eq_of_ne_zero h)
  rw [asd]
  exact rfl

@[simp] theorem c_opt_iget_ev:eval O c_opt_iget o = Option.iget (n2o o) := by simp [← eval_prim_eq_eval c_opt_iget_ev_pr]
end Nat.RecursiveIn.Code
end opt_iget

section opt_none
namespace Nat.RecursiveIn.Code
def c_opt_none := (c_const 0)
@[simp] theorem c_opt_none_ev_pr:code_prim c_opt_none := by unfold c_opt_none; repeat (first|assumption|simp|constructor)
@[simp] theorem c_opt_none_evp : eval_prim O c_opt_none o = o2n Option.none := by
  simp [c_opt_none]
-- @[simp] theorem c_opt_none_ev: n2o (eval O c_opt_none o) = (Option.none : Option ℕ) := by simp [← eval_prim_eq_eval c_opt_none_ev_pr]
end Nat.RecursiveIn.Code
end opt_none

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

section list_singleton
namespace Nat.RecursiveIn.Code
def c_list_singleton (cf:Code) := c_list_cons.comp₂ cf c_list_nil
@[simp] theorem c_list_singleton_ev_pr :code_prim (c_list_singleton c_flip) := by unfold c_list_singleton; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_singleton_evp : eval_prim O (c_list_singleton cf) x = l2n ([eval_prim O cf x]) := by
  simp [c_list_singleton]
-- @[simp] theorem c_list_singleton_ev : eval O (c_list_singleton cf) x = l2n ([eval_prim O cf x]) := by simp [← eval_prim_eq_eval c_list_singleton_ev_pr]
end Nat.RecursiveIn.Code
end list_singleton

section list_concat
namespace Nat.RecursiveIn.Code
def c_list_concat := c_list_append.comp₂ left (c_list_singleton right)
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

section list_zipWith
namespace Nat.RecursiveIn.Code
/-
zipL :: [a] -> [b] -> [(a,b)]
zipL xs ys = reverse $ fst $ foldl step ([], ys) xs
  where
    step (acc, y:ys') x = ((x,y) : acc, ys')
    step (acc, [])    _ = (acc, [])
-/
def c_list_zipWith_aux (cf:Code):=
  let yys' := right.comp left
  let ys'  := c_list_tail.comp  yys'
  let y    := c_list_headI.comp yys'
  let x    := right
  let acc  := left.comp left

  let step :=
    c_list_casesOn'
    yys'
    left
    (pair (c_list_cons.comp₂ (cf.comp₂ x y) (acc)) ys')

  (c_list_foldl step).comp₂ (pair c_list_nil right) left
def c_list_zipWith (cf:Code) := c_list_reverse.comp $ left.comp (c_list_zipWith_aux cf)
-- #eval eval_prim (Nat.fzero) c_list_zipWith_aux (Nat.pair [1] [3])
-- theorem zip_aux : List.foldr () = List.zip ()
@[simp] theorem c_list_zipWith_ev_pr (hcf:code_prim cf) : code_prim (c_list_zipWith_aux cf) := by unfold c_list_zipWith_aux; repeat (first|assumption|simp|constructor)
-- @[simp] theorem c_list_zipWith_evp : eval_prim O c_list_zipWith_aux (Nat.pair l1N l2N) = l2n (List.zipWith Nat.pair (n2l l1N) (n2l l2N)) := by
theorem c_list_zipWith_evp_aux_2 {a b : List ℕ} {f:ℕ→ℕ→ℕ} (h:a.length≤b.length) : List.zipWith f (b++c) a = List.zipWith f b a := by
  have aux3 : b = take a.length (b) ++ drop a.length (b) := by
    exact Eq.symm (take_append_drop a.length (b))
  rw [aux3]
  have aux4 : (take a.length b ++ drop a.length b ++ c) = (take a.length b ++( drop a.length b ++ c)) := by exact append_assoc (take a.length b) (drop a.length b) c
  rw [aux4]
  have aux5 : (take a.length b).length = (take a.length b).length := by rfl
  have aux7 : (take a.length b).length = a.length := by exact length_take_of_le h

  have aux6 := @zipWith_append ℕ ℕ ℕ f (take a.length b) (drop a.length b ++ c) a [] aux7
  simp at aux6
  rw [aux6]
  simp
  have aux8 := @zipWith_append ℕ ℕ ℕ f (take a.length b) (drop a.length b) a [] aux7
  simp at aux8
  rw [aux8]
theorem zipWith_flip : List.zipWith f a b = List.zipWith (flip f) b a := by
    induction a generalizing b with
    | nil => simp
    | cons x xs xih =>
      induction b with
      | nil => simp
      | cons y ys yih =>
        simp [xih, flip]

theorem c_list_zipWith_evp_aux_1 {a b : List ℕ} {f:ℕ→ℕ→ℕ} (h:a.length≤b.length) : List.zipWith f a (b++c) = List.zipWith f a b := by
  rw [zipWith_flip]
  rw (config:={occs:=.pos [2]}) [zipWith_flip]
  exact c_list_zipWith_evp_aux_2 h


theorem c_list_zipWith_aux_evp :
  eval_prim O (c_list_zipWith_aux cf) (Nat.pair l1N l2N)
    =
  Nat.pair ((List.zipWith (fun x y => eval_prim O cf (Nat.pair x y)) l1N l2N).reverse) (drop (n2l l1N).length (n2l l2N)) := by

  let f:=fun x y => eval_prim O cf (Nat.pair x y)

  simp [c_list_zipWith_aux, -encode_list_cons, -encode_list_nil]
  have grind_helper_1: ((n2l l1N).reverse).reverse = (n2l l1N) := by exact reverse_reverse (n2l l1N)
  induction h:(n2l l1N).reverse generalizing l1N with
  | nil => simp_all
  | cons head tail ih =>
    have asd2 : (n2l l1N) = (tail.reverse).concat head := by
      rw [concat_eq_append]
      rw [←reverse_reverse (n2l l1N)]
      rw [h]
      apply reverse_cons
    rw [asd2]

    simp [-encode_list_cons, -encode_list_nil] at ih
    have asdd : (n2l (l2n tail.reverse)).reverse = tail := by simp
    simp [-encode_list_cons, -encode_list_nil, -foldl_reverse]
    have lolz := ih asdd
    simp [-encode_list_cons, -encode_list_nil, -foldl_reverse] at lolz
    rw [lolz]
    simp [-encode_list_cons, -encode_list_nil, -foldl_reverse]


    by_cases hh:(drop tail.length (n2l l2N))=([]:List ℕ)
    ·
      simp only [hh]
      have aux1: drop (tail.length + 1) (n2l l2N) = [] := by
        simp
        grind
      rw[aux1]
      have aux4 := List.drop_eq_nil_iff.mp hh
      have aux5 : tail.length = tail.reverse.length := by exact Eq.symm length_reverse
      rw [aux5] at aux4
      have aux2:(zipWith f (tail.reverse ++ [head]) (n2l l2N)) = (zipWith f tail.reverse (n2l l2N)) := by simp [c_list_zipWith_evp_aux_2 aux4]
      rw [aux2]
    -- sorry
    · -- this is the case where l2N is longer than l1N.
      have omwv: ∃ head2 list2, drop tail.length (n2l l2N) = head2::list2 := by exact ne_nil_iff_exists_cons.mp hh
      rcases omwv with ⟨head2,list2,hl2⟩
      simp only [hl2]

      have main : (f head (head2 :: list2).headI :: (zipWith f tail.reverse (n2l l2N)).reverse) = (zipWith f (tail.reverse ++ [head]) (n2l l2N)).reverse := by
        simp
        have aux1 := length_lt_of_drop_ne_nil hh
        have aux3 : (n2l l2N) = (take tail.length (n2l l2N)) ++ drop tail.length (n2l l2N) := by
          exact Eq.symm (take_append_drop tail.length (n2l l2N))
        have aux5 : (n2l l2N) = (take tail.length (n2l l2N)) ++ [head2] ++ list2 := by
          rw (config:={occs:=.pos [1]}) [aux3]
          rw [append_assoc]
          simp [hl2]

        have aux7 :
          let l₁:=tail.reverse ++ [head]
          let l₂:=take tail.length (n2l l2N) ++ [head2] ++ list2
          let l₁':=zipWith f (tail.reverse) (take tail.length (n2l l2N))
          let l₂':List ℕ :=[f head head2]
          -- let f:= f
          ∃ ws xs ys zs, ws.length = ys.length ∧ l₁ = ws ++ xs ∧ l₂ = ys ++ zs ∧ l₁' = zipWith f ws ys ∧ l₂' = zipWith f xs zs := by
            let ws := tail.reverse
            let ys := take tail.length (n2l l2N)
            let xs :List ℕ :=[head]
            let zs := [head2] ++ list2
            use ws,xs,ys,zs
            constructor
            · simp [ws,ys]
              exact le_of_succ_le aux1
            · constructor
              · exact rfl
              · constructor
                · exact append_assoc (take tail.length (n2l l2N)) [head2] list2
                · constructor
                  · exact rfl
                  · exact rfl
        have aux8 := zipWith_eq_append_iff.mpr aux7

        rw (config:={occs:=.pos [2]}) [aux5]
        rw [aux8]
        simp
        rw (config:={occs:=.pos [1]}) [aux5]
        rw [append_assoc (take tail.length (n2l l2N)) [head2] list2]

        have aux9 : tail.reverse.length ≤ (take tail.length (n2l l2N)).length := by
          simp
          exact le_of_succ_le aux1
        exact  c_list_zipWith_evp_aux_1 aux9
      rw [main]

@[simp] theorem c_list_zipWith_evp :
  eval_prim O (c_list_zipWith cf) (Nat.pair l1N l2N)
    =
  List.zipWith (fun x y => eval_prim O cf (Nat.pair x y)) l1N l2N := by
    simp [c_list_zipWith, c_list_zipWith_aux_evp]
-- @[simp] theorem c_list_zipWith_ev : eval O (c_list_zipWith_aux cf) lN = l2n ((n2l lN).map (eval_prim O cf)) := by simp [← eval_prim_eq_eval c_list_zipWith_ev_pr]
end Nat.RecursiveIn.Code
end list_zipWith

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

section list_replicate
namespace Nat.RecursiveIn.Code
def c_list_replicate :=
  let prev_list := right.comp right
  let x := left
  (prec
  (c_list_nil)
  (c_list_concat.comp₂ prev_list x)).comp c_flip
@[simp] theorem c_list_replicate_ev_pr : code_prim c_list_replicate := by unfold c_list_replicate; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_replicate_evp : eval_prim O c_list_replicate (Nat.pair n x) = l2n (List.replicate n x) := by
  simp [c_list_replicate, -encode_list_cons, -encode_list_nil]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [-encode_list_cons, -encode_list_nil, ih]
    exact Eq.symm replicate_succ'
@[simp] theorem c_list_replicate_ev : eval O c_list_replicate (Nat.pair n x) = l2n (List.replicate n x) := by simp [← eval_prim_eq_eval c_list_replicate_ev_pr]
end Nat.RecursiveIn.Code
end list_replicate

section list_map'
namespace Nat.RecursiveIn.Code
/--
`eval_prim O (c_list_map' cf) (Nat.pair lN aux) = ((n2l lN).map (fun ele => eval_prim O cf (Nat.pair ele aux)))`
-/
def c_list_map' (cf:Code) :=
  let lN  := left
  let aux := right
  (c_list_map cf).comp ((c_list_zipWith c_id).comp₂ lN (c_list_replicate.comp₂ (c_list_length.comp lN) aux))
@[simp, aesop safe] theorem c_list_map'_ev_pr (hcf:code_prim cf): code_prim (c_list_map' cf) := by unfold c_list_map'; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_map'_evp :
  eval_prim O (c_list_map' cf) (Nat.pair lN aux)
    =
  ((n2l lN).map (fun ele => eval_prim O cf (Nat.pair ele aux))) := by
  simp [c_list_map', -encode_list_cons, -encode_list_nil]
  induction (n2l lN) with
  | nil => simp [Nat.pair]
  | cons head tail ih =>
    simp [replicate_succ]
    exact ih
-- @[simp] theorem c_list_map'_ev : eval O (c_list_map' cf) lN = l2n ((n2l lN).map (eval_prim O cf)) := by simp [← eval_prim_eq_eval c_list_map'_ev_pr]
end Nat.RecursiveIn.Code
end list_map'



@[simp] theorem getLastI_append {y:ℕ}: (x++[y]).getLastI = y := by
  rw [getLastI_eq_getLast?]
  simp
