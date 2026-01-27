/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Computability.Constructions.Option

/-!
# Construction of basic primitive recursive functions on lists

This file defines basic primitive recursive codes for basic functions on lists.

## Structure
(See Computability.Constructions.Primitive for more details.)

The major constructions in this file are `c_list_foldl` and `c_list_zipWith`.

`c_list_foldl` allows easy definitions of subsequent constructs, although `c_list_zipWith` still requires
a nontrivial proof.

-/

open Nat
open Denumerable
open Encodable
open List

abbrev n2l := @ofNat (List ℕ) _
abbrev l2n := @encode (List ℕ) _

instance : OfNat (List ℕ) lN where ofNat := n2l lN
instance : Coe ℕ (List ℕ) := ⟨n2l⟩
instance : Coe (List ℕ) ℕ := ⟨l2n⟩

section list_nil
namespace Computability.Code
def c_list_nil := zero
@[cp] theorem c_list_nil_prim : code_prim c_list_nil := by unfold c_list_nil; apply_cp
@[simp] theorem c_list_nil_evp :evalp O c_list_nil x = l2n ([]) := by simp [c_list_nil]
@[simp] theorem c_list_nil_ev :eval O c_list_nil x = l2n ([]) := by simp [←evalp_eq_eval c_list_nil_prim]
end Computability.Code
end list_nil

section list_cons
namespace Computability.Code
def c_list_cons := succ
@[cp] theorem c_list_cons_prim : code_prim c_list_cons := by unfold c_list_cons; apply_cp
@[simp] theorem c_list_cons_evp :evalp O c_list_cons ⟪a, lN⟫= l2n (List.cons a (n2l lN)) := by simp [c_list_cons]
@[simp] theorem c_list_cons_ev :eval O c_list_cons ⟪a, lN⟫= l2n (List.cons a (n2l lN)) := by simp [←evalp_eq_eval c_list_cons_prim]
end Computability.Code
end list_cons

section list_tail
namespace Computability.Code
def c_list_tail := right.comp c_pred
@[cp] theorem c_list_tail_prim : code_prim c_list_tail := by unfold c_list_tail; apply_cp
@[simp] theorem c_list_tail_evp : evalp O c_list_tail lN = l2n (List.tail (n2l lN)) := by
  simp [c_list_tail]
  by_cases hl:lN=0
  · simp [hl,r]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_tail_ev:eval O c_list_tail lN = l2n (List.tail (n2l lN)) := by simp [← evalp_eq_eval c_list_tail_prim]
end Computability.Code
end list_tail

section list_head?
namespace Computability.Code
def c_list_head? := c_ifz.comp₃ c_id zero $ succ.comp (left.comp c_pred)
@[cp] theorem c_list_head?_prim : code_prim c_list_head? := by unfold c_list_head?; apply_cp
@[simp] theorem c_list_head?_evp : evalp O c_list_head? lN = o2n (List.head? (n2l lN)) := by
  simp [c_list_head?]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_head?_ev:eval O c_list_head? lN = o2n (List.head? (n2l lN)) := by simp [← evalp_eq_eval c_list_head?_prim]
end Computability.Code
end list_head?

section list_headI
namespace Computability.Code
def c_list_headI := c_ifz.comp₃ c_id zero (left.comp c_pred)
@[cp] theorem c_list_headI_prim : code_prim c_list_headI := by unfold c_list_headI; apply_cp
@[simp] theorem c_list_headI_evp : evalp O c_list_headI lN = List.headI (n2l lN) := by
  simp [c_list_headI]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_headI_ev:eval O c_list_headI lN = List.headI (n2l lN) := by simp [← evalp_eq_eval c_list_headI_prim]
end Computability.Code
end list_headI

section list_casesOn
namespace Computability.Code
def c_list_casesOn (cl cf cg:Code) :=
  let x := left.comp (c_pred.comp cl)
  let xs := right.comp (c_pred.comp cl)
  c_if_eq_te.comp₄ cl (c_const 0) cf (cg.comp₂ x xs)
@[cp] theorem c_list_casesOn_prim (hcl:code_prim cl) (hcf:code_prim cf) (hcg:code_prim cg) : code_prim (c_list_casesOn cl cf cg) := by unfold c_list_casesOn; apply_cp
@[simp] theorem c_list_casesOn_evp : evalp O (c_list_casesOn cl cf cg) input =
  List.casesOn
  (n2l (evalp O cl input))
  (evalp O cf input)
  (fun x xs => evalp O cg (Nat.pair x (l2n xs)))
  := by
  simp [c_list_casesOn]
  by_cases hl:(evalp O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
-- @[simp] theorem c_list_casesOn_ev :eval O (c_list_casesOn cl cf cg) input =
--   List.casesOn
--   (n2l (evalp O cl input))
--   (evalp O cf input)
--   (fun x xs => evalp O cg (Nat.pair (@encode ℕ _ x) (l2n xs))) := by
--     simp [← evalp_eq_eval c_list_casesOn_prim]
end Computability.Code
end list_casesOn
section list_casesOn'
namespace Computability.Code
def c_list_casesOn' (cl cf cg:Code) :=
  c_if_eq_te.comp₄ cl (c_const 0) cf cg
@[cp] theorem c_list_casesOn'_prim (hcl:code_prim cl) (hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_list_casesOn' cl cf cg) := by unfold c_list_casesOn'; apply_cp
@[simp] theorem c_list_casesOn'_evp : evalp O (c_list_casesOn' cl cf cg) input =
  List.casesOn
  (n2l (evalp O cl input))
  (evalp O cf input)
  (fun _ => evalp O cg input)
  := by
  simp [c_list_casesOn']
  by_cases hl:(evalp O cl input)=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
-- @[simp] theorem c_list_casesOn'_ev :eval O (c_list_casesOn' cf cg) lN =
--   List.casesOn
--   (n2l lN)
--   (evalp O cf lN)
--   (fun x xs => evalp O cg (Nat.pair (@encode ℕ _ x) (l2n xs))) := by
--     simp [← evalp_eq_eval c_list_casesOn'_prim]
end Computability.Code
end list_casesOn'

section list_drop
namespace Computability.Code
def c_list_drop :=
  (
    prec
    c_id $
    c_list_tail.comp (right.comp right)
  ).comp c_flip
@[cp] theorem c_list_drop_prim : code_prim c_list_drop := by unfold c_list_drop; apply_cp
@[simp] theorem c_list_drop_evp : evalp O c_list_drop (Nat.pair i lN) = l2n (List.drop i (n2l lN)) := by
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
@[simp] theorem c_list_drop_ev:eval O c_list_drop (Nat.pair i lN) = l2n (List.drop i (n2l lN)) := by simp [← evalp_eq_eval c_list_drop_prim]
end Computability.Code
end list_drop

section list_getElem?
namespace Computability.Code
def c_list_getElem? := c_list_head?.comp (c_list_drop.comp c_flip)
@[cp] theorem c_list_getElem?_prim : code_prim c_list_getElem? := by unfold c_list_getElem?; apply_cp
@[simp] theorem c_list_getElem?_evp : evalp O c_list_getElem? ⟪lN, i⟫ = o2n (n2l lN)[i]? := by simp [c_list_getElem?]
@[simp] theorem c_list_getElem?_ev : eval O c_list_getElem? ⟪lN, i⟫ = o2n (n2l lN)[i]? := by simp [← evalp_eq_eval c_list_getElem?_prim]
end Computability.Code
end list_getElem?

section list_getD
namespace Computability.Code
def c_list_getD := c_opt_getD.comp₂ (c_list_getElem?.comp₂ left (left.comp right)) (right.comp right)
@[cp] theorem c_list_getD_prim : code_prim c_list_getD := by unfold c_list_getD; apply_cp
@[simp] theorem c_list_getD_evp : evalp O c_list_getD ⟪lN, i, d⟫ = (n2l lN).getD i d := by simp [c_list_getD]
@[simp] theorem c_list_getD_ev : eval O c_list_getD ⟪lN, i, d⟫ = (n2l lN).getD i d := by simp [← evalp_eq_eval c_list_getD_prim]
end Computability.Code
end list_getD

section list_getI
namespace Computability.Code
def c_list_getI := c_pred.comp c_list_getElem?
@[cp] theorem c_list_getI_prim : code_prim c_list_getI := by unfold c_list_getI; apply_cp
@[simp] theorem c_list_getI_evp : evalp O c_list_getI ⟪lN, i⟫ = ((n2l lN).getI i) := by
  simp [c_list_getI]
  by_cases hl:i<(n2l lN).length <;> simp [hl, List.getI]
@[simp] theorem c_list_getI_ev : eval O c_list_getI ⟪lN, i⟫ = ((n2l lN).getI i) := by simp [← evalp_eq_eval c_list_getI_prim]
end Computability.Code
end list_getI

section list_get
namespace Computability.Code
def c_list_get := c_list_getI
@[cp] theorem c_list_get_prim : code_prim c_list_get := by unfold c_list_get; apply_cp
@[simp] theorem c_list_get_evp (h:i<(n2l lN).length) : evalp O c_list_get ⟪lN, i⟫ = (n2l lN)[i] := by
  simp [c_list_get]
  simp [getI]
  by_cases hl:i<(n2l lN).length
  · simp [hl]
  · contradiction
@[simp] theorem c_list_get_ev (h:i<(n2l lN).length) : eval O c_list_get ⟪lN, i⟫ = (n2l lN)[i] := by
  simp [← evalp_eq_eval c_list_get_prim]
  simp [h]
end Computability.Code
end list_get

/-
`foldl :: (a -> b -> a) -> a -> [b] -> a`
`foldl fn acc [] = acc`
`foldl fn acc (x:xs) = foldl fn (fn acc x) xs`
-/
section list_foldl
namespace Computability.Code
def c_list_foldl_aux (cf:Code) :=
  let x:=left.comp (c_pred.comp right)
  let xs:=right.comp (c_pred.comp right)
  c_list_casesOn' right c_id (pair (cf.comp₂ left x) (xs))
def c_list_foldl_aux2 (cf:Code) := (c_nat_iterate (c_list_foldl_aux cf)).comp₂ c_id right
def c_list_foldl (cf:Code) := left.comp (c_list_foldl_aux2 cf)
@[cp] theorem c_list_foldl_prim (hcf:code_prim cf) : code_prim (c_list_foldl cf) := by rewrite [c_list_foldl, c_list_foldl_aux2, c_list_foldl_aux]; apply_cp
@[simp] theorem c_list_foldl_aux_evp   : evalp O (c_list_foldl_aux cf) ⟪init, lN⟫ = if (n2l lN) = [] then ⟪init, lN⟫ else Nat.pair (evalp O cf (Nat.pair init (n2l lN).headI)) (l2n (List.tail (n2l lN))) := by
  simp [c_list_foldl_aux]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_foldl_evp : evalp O (c_list_foldl cf) ⟪init, lN⟫ =
  (
    List.foldl
    (fun a b => evalp O cf ⟪a,b⟫)
    (init)
    (n2l lN)
  )
  := by
  simp [c_list_foldl,c_list_foldl_aux2]

  suffices ∀ n,
  (evalp O cf.c_list_foldl_aux)^[n] ⟪init, lN⟫
    =
  Nat.pair (((n2l lN).take n).foldl (fun a b => evalp O cf ⟪a,b⟫) init) (l2n ((n2l lN).drop n)) by
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
      have fixedp : evalp O cf.c_list_foldl_aux ⟪init, 0⟫ = ⟪init, 0⟫ := by simp
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

-- @[simp] theorem c_list_foldl_ev : eval O (c_list_foldl cf) ⟪init, lN⟫ =
--   (
--     List.foldl
--     (fun a b => evalp O cf ⟪a,b⟫)
--     (init)
--     (n2l lN)
--   ) := by rw [← evalp_eq_eval c_list_foldl_prim]; simp only [c_list_foldl_evp]
end Computability.Code
end list_foldl

-- reverse = foldl (flip (:)) []
section list_reverse
namespace Computability.Code
def c_list_reverse := (c_list_foldl (c_list_cons.comp c_flip)).comp₂ c_list_nil c_id
@[cp] theorem c_list_reverse_prim : code_prim c_list_reverse := by unfold c_list_reverse; apply_cp
@[simp] theorem c_list_reverse_evp : evalp O c_list_reverse lN =  l2n (List.reverse (n2l lN)) := by
  simp only [c_list_reverse]
  simp [-encode_list_cons, -encode_list_nil]
  -- -encode_list_cons, -encode_list_nil these are needed!
  have aux : ∀ l r, List.foldl (fun (s : ℕ) (b : ℕ) => l2n (b :: (n2l s))) r l = l2n (List.reverseAux l (n2l r)) := fun l => by
    induction l with
    | nil => simp [*, List.reverseAux]
    | cons head tail ih => simp [*, List.reverseAux, -encode_list_cons]
  rw [aux (n2l lN) (l2n [])]
  simp
@[simp] theorem c_list_reverse_ev : eval O c_list_reverse lN =  l2n (List.reverse (n2l lN)) := by simp [← evalp_eq_eval c_list_reverse_prim]
end Computability.Code
end list_reverse

/-
`foldr :: (a -> b -> b) -> b -> [a] -> b`
`foldr fn acc [] = acc`
`foldr fn acc (x:xs) = fn x (foldr fn acc xs)`
-/
section list_foldr
namespace Computability.Code
def c_list_foldr (cf:Code) := (c_list_foldl (cf.comp c_flip)).comp₂ left (c_list_reverse.comp right)
@[cp] theorem c_list_foldr_prim(hcf:code_prim cf) : code_prim (c_list_foldr cf) := by unfold c_list_foldr; apply_cp
@[simp] theorem c_list_foldr_evp : evalp O (c_list_foldr cf) ⟪init, lN⟫ =
  (
    List.foldr
    (fun a b => evalp O cf ⟪a,b⟫)
    (init)
    (n2l lN)
  )
  := by simp [c_list_foldr]
-- @[simp] theorem c_list_foldr_ev : eval O (c_list_foldr cf) ⟪init, lN⟫ =
--   (
--     List.list_foldr
--     (fun a b => evalp O cf ⟪a,b⟫)
--     (init)
--     (n2l lN)
--   ) := by rw [← evalp_eq_eval c_list_foldr_prim]; simp only [c_list_foldr_evp]
end Computability.Code
end list_foldr

-- https://hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Data.Foldable.html#length
section list_length
namespace Computability.Code
def c_list_length := (c_list_foldl (succ.comp left)).comp₂ zero c_id
@[cp] theorem c_list_length_prim : code_prim c_list_length := by unfold c_list_length; apply_cp
@[simp] theorem c_list_length_evp : evalp O c_list_length lN = List.length (n2l lN) := by simp [c_list_length]
@[simp] theorem c_list_length_ev : eval O c_list_length lN = List.length (n2l lN) := by simp [← evalp_eq_eval c_list_length_prim]
end Computability.Code
end list_length

section list_getLast?
namespace Computability.Code
def c_list_getLast? := c_list_getElem?.comp₂ c_id (c_pred.comp $ c_list_length.comp c_id)
@[cp] theorem c_list_getLast?_prim : code_prim c_list_getLast? := by unfold c_list_getLast?; apply_cp
@[simp] theorem c_list_getLast?_evp : evalp O c_list_getLast? lN = o2n (List.getLast? (n2l lN)) := by
  simp [c_list_getLast?]
  exact Eq.symm List.getLast?_eq_getElem?
@[simp] theorem c_list_getLast?_ev:eval O c_list_getLast? lN = o2n (List.getLast? (n2l lN)) := by simp [← evalp_eq_eval c_list_getLast?_prim]
end Computability.Code
end list_getLast?

section list_getLastI
namespace Computability.Code
def c_list_getLastI := c_opt_iget.comp c_list_getLast?
@[cp] theorem c_list_getLastI_prim : code_prim c_list_getLastI := by unfold c_list_getLastI; apply_cp
@[simp] theorem c_list_getLastI_evp : evalp O c_list_getLastI lN = List.getLastI (n2l lN) := by
  simp [c_list_getLastI]
  exact Eq.symm (List.getLastI_eq_getLast? (n2l lN))
@[simp] theorem c_list_getLastI_ev:eval O c_list_getLastI lN = List.getLastI (n2l lN) := by simp [← evalp_eq_eval c_list_getLastI_prim]
end Computability.Code
end list_getLastI

/-
(++) []     ys = ys
(++) (x:xs) ys = x : xs ++ ys
-/
section list_append
namespace Computability.Code
def c_list_append := (c_list_foldr (c_list_cons)).comp c_flip
@[cp] theorem c_list_append_prim : code_prim c_list_append := by unfold c_list_append; apply_cp
@[simp] theorem c_list_append_evp : evalp O c_list_append ⟪l1N, l2N⟫ = l2n ((n2l l1N) ++ (n2l l2N)) := by
  simp [c_list_append, -encode_list_cons, -encode_list_nil]
  induction (n2l l1N) with
  | nil => simp
  | cons head tail ih => simp [ih, -encode_list_cons, -encode_list_nil]
@[simp] theorem c_list_append_ev : eval O c_list_append ⟪l1N, l2N⟫ = l2n ((n2l l1N) ++ (n2l l2N)) := by simp [← evalp_eq_eval c_list_append_prim]
end Computability.Code
end list_append

section list_singleton
namespace Computability.Code
def c_list_singleton (cf:Code) := c_list_cons.comp₂ cf c_list_nil
@[cp] theorem c_list_singleton_prim (hcf:code_prim cf) : code_prim (c_list_singleton cf) := by unfold c_list_singleton; apply_cp
@[simp] theorem c_list_singleton_evp : evalp O (c_list_singleton cf) x = l2n ([evalp O cf x]) := by
  simp [c_list_singleton]
-- @[simp] theorem c_list_singleton_ev : eval O (c_list_singleton cf) x = l2n ([evalp O cf x]) := by simp [← evalp_eq_eval c_list_singleton_prim]
end Computability.Code
end list_singleton

section list_concat
namespace Computability.Code
def c_list_concat := c_list_append.comp₂ left (c_list_singleton right)
@[cp] theorem c_list_concat_prim : code_prim c_list_concat := by unfold c_list_concat; apply_cp
@[simp] theorem c_list_concat_evp : evalp O c_list_concat ⟪lN, i⟫ = l2n ((n2l lN)++[i]) := by
  simp [c_list_concat, -encode_list_cons, -encode_list_nil]
@[simp] theorem c_list_concat_ev : eval O c_list_concat ⟪lN, i⟫ = l2n ((n2l lN)++[i]) := by simp [← evalp_eq_eval c_list_concat_prim]
end Computability.Code
end list_concat

-- https://hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Base.html#map
section list_map
namespace Computability.Code
def c_list_map (cf:Code) := (c_list_foldr (c_list_cons.comp₂ (cf.comp left) right)).comp₂ (c_list_nil) (c_id)
@[cp] theorem c_list_map_prim (hcf:code_prim cf) : code_prim (c_list_map cf) := by unfold c_list_map; apply_cp
@[simp] theorem c_list_map_evp : evalp O (c_list_map cf) lN = l2n ((n2l lN).map (evalp O cf)) := by
  simp [c_list_map, -encode_list_cons, -encode_list_nil]
  induction (n2l lN) with
  | nil => simp
  | cons head tail ih => simp [ih, -encode_list_cons, -encode_list_nil]
-- @[simp] theorem c_list_map_ev : eval O (c_list_map cf) lN = l2n ((n2l lN).map (evalp O cf)) := by simp [← evalp_eq_eval c_list_map_prim]
end Computability.Code
end list_map

section list_zipWith
namespace Computability.Code
/-
zipL :: [a] -> [b] -> [(a,b)]
zipL xs ys = reverse $ fst $ foldl step ([], ys) xs
  where
    step (acc, y:ys') x = ((x,y) : acc, ys')
    step (acc, [])    _ = (acc, [])
-/
def c_list_zipWith_aux (cf : Code) :=
  let yys' := right.comp left
  let ys'  := c_list_tail.comp  yys'
  let y    := c_list_headI.comp yys'
  let x    := right
  let acc  := left.comp left

  let step :=
    c_list_casesOn'
    yys'
    left
    (pair (c_list_cons.comp₂ (cf.comp₂ x y) acc) ys')

  (c_list_foldl step).comp₂ (pair c_list_nil right) left
def c_list_zipWith (cf:Code) := c_list_reverse.comp $ left.comp (c_list_zipWith_aux cf)

@[cp] theorem c_list_zipWith_aux_prim (hcf:code_prim cf) : code_prim (c_list_zipWith_aux cf) := by unfold c_list_zipWith_aux; apply_cp
@[cp] theorem c_list_zipWith_prim (hcf:code_prim cf) : code_prim (c_list_zipWith cf) := by unfold c_list_zipWith; apply_cp
theorem c_list_zipWith_evp_aux_2 {a b : List ℕ} {f:ℕ→ℕ→ℕ} (h:a.length≤b.length) : List.zipWith f (b++c) a = List.zipWith f b a := by
  -- rw `b` => `take a.length b ++ drop a.length b`
  rewrite [(take_append_drop a.length b).symm]
  -- rw `take a.length b ++ drop a.length b ++ c` => `take a.length b ++ (drop a.length b ++ c)`
  rewrite [append_assoc (take a.length b) (drop a.length b) c]
  have aux7 : (take a.length b).length = a.length := by exact length_take_of_le h
  have aux6 := @zipWith_append ℕ ℕ ℕ f (take a.length b) (drop a.length b ++ c) a [] aux7
  have aux8 := @zipWith_append ℕ ℕ ℕ f (take a.length b) (drop a.length b) a [] aux7
  simp at aux6 aux8
  simp [aux6, aux8]
theorem zipWith_flip : List.zipWith f a b = List.zipWith (flip f) b a := by
  induction a generalizing b with
  | nil => simp
  | cons _ _ xih =>
    induction b with
    | nil => simp
    | cons _ _ yih => simp [xih, flip]

theorem c_list_zipWith_evp_aux_1 {a b : List ℕ} {f:ℕ→ℕ→ℕ} (h:a.length≤b.length) : List.zipWith f a (b++c) = List.zipWith f a b := by
  rw [zipWith_flip]
  rw (config:={occs:=.pos [2]}) [zipWith_flip]
  exact c_list_zipWith_evp_aux_2 h

theorem c_list_zipWith_evp_aux_3 {f:ℕ→ℕ→ℕ} {head} {tail : List ℕ} (hh:tail.length < (n2l l2N).length) (hl2 : drop tail.length (n2l l2N) = head2 :: list2) : (f head (head2 :: list2).headI :: (zipWith f tail.reverse (n2l l2N)).reverse) = (zipWith f (tail.reverse ++ [head]) (n2l l2N)).reverse := by
  simp
  have aux5 : (n2l l2N) = (take tail.length (n2l l2N)) ++ [head2] ++ list2 := by
    -- rw `(n2l l2N)` => `(take tail.length (n2l l2N)) ++ drop tail.length (n2l l2N)`
    rw (config:={occs:=.pos [1]}) [Eq.symm (take_append_drop tail.length (n2l l2N))]
    rw [append_assoc, hl2]
    simp
  have aux7 :
    let l₁  := tail.reverse ++ [head]
    let l₂  := take tail.length (n2l l2N) ++ [head2] ++ list2
    let l₁' := zipWith f (tail.reverse) (take tail.length (n2l l2N))
    let l₂' : List ℕ := [f head head2]
    ∃ ws xs ys zs, ws.length = ys.length ∧ l₁ = ws ++ xs ∧ l₂ = ys ++ zs ∧ l₁' = zipWith f ws ys ∧ l₂' = zipWith f xs zs := by
      let ws := tail.reverse
      let ys := take tail.length (n2l l2N)
      let xs := [head]
      let zs := [head2] ++ list2
      use ws,xs,ys,zs
      constructor
      · simp [ws,ys]
        exact le_of_succ_le hh
      · exact ⟨rfl, append_assoc (take tail.length (n2l l2N)) [head2] list2, rfl, rfl⟩
  have aux9 : tail.reverse.length ≤ (take tail.length (n2l l2N)).length := by
    simp only [length_reverse, length_take, le_inf_iff, le_refl, true_and]
    exact le_of_succ_le hh
  rw (config:={occs:=.pos [2]}) [aux5]
  rw [zipWith_eq_append_iff.mpr aux7]
  rw (config:={occs:=.pos [1]}) [aux5]
  rw [append_assoc (take tail.length (n2l l2N)) [head2] list2]
  simp
  exact c_list_zipWith_evp_aux_1 aux9
theorem c_list_zipWith_aux_evp :
  evalp O (c_list_zipWith_aux cf) ⟪l1N, l2N⟫
    =
  Nat.pair ((List.zipWith (fun x y => evalp O cf ⟪x,y⟫) l1N l2N).reverse) (drop (n2l l1N).length (n2l l2N)) := by

  let f := fun x y => evalp O cf ⟪x,y⟫

  simp [c_list_zipWith_aux, -encode_list_cons, -encode_list_nil]
  induction h:(n2l l1N).reverse generalizing l1N with
  | nil => simp_all
  | cons head tail ih =>
    have asd2 : (n2l l1N) = (tail.reverse).concat head := by
      rw [concat_eq_append]
      rw [←reverse_reverse (n2l l1N)]
      rw [h]
      exact reverse_cons
    rw [asd2]

    simp [-encode_list_cons, -encode_list_nil] at ih
    simp [-encode_list_cons, -encode_list_nil, -foldl_reverse]
    have asdd : (n2l (l2n tail.reverse)).reverse = tail := by simp
    have lolz := ih asdd
    simp [-encode_list_cons, -encode_list_nil, -foldl_reverse] at lolz
    rw [lolz]
    simp [-encode_list_cons, -encode_list_nil, -foldl_reverse]
    clear ih lolz asdd asd2

    by_cases hh : drop tail.length (n2l l2N) = ([]:List ℕ)
    · simp only [hh]
      rw [show drop (tail.length + 1) (n2l l2N) = [] from by simp at hh ⊢; omega]
      have aux4 := List.drop_eq_nil_iff.mp hh
      rw [show tail.length = tail.reverse.length from length_reverse.symm] at aux4
      simp [c_list_zipWith_evp_aux_2 aux4]
    · -- this is the case where l2N is longer than l1N.
      rcases ne_nil_iff_exists_cons.mp hh with ⟨head2, list2, hl2⟩
      -- now we have `drop tail.length (n2l l2N) = head2::list2`
      simp only [hl2]
      simp only [drop_eq_nil_iff, not_le] at hh
      have main : (f head (head2 :: list2).headI :: (zipWith f tail.reverse (n2l l2N)).reverse) = (zipWith f (tail.reverse ++ [head]) (n2l l2N)).reverse := c_list_zipWith_evp_aux_3 hh hl2
      rw [main]

@[simp] theorem c_list_zipWith_evp :
  evalp O (c_list_zipWith cf) ⟪l1N, l2N⟫
    =
  List.zipWith (fun x y => evalp O cf ⟪x,y⟫) l1N l2N := by
    simp [c_list_zipWith, c_list_zipWith_aux_evp]
-- @[simp] theorem c_list_zipWith_ev : eval O (c_list_zipWith_aux cf) lN = l2n ((n2l lN).map (evalp O cf)) := by simp [← evalp_eq_eval c_list_zipWith_prim]
end Computability.Code
end list_zipWith

section list_range
namespace Computability.Code
def c_list_range :=
  let prev_list := right.comp right
  let i := (left.comp right)
  (prec
  (c_list_nil)
  (c_list_concat.comp₂ prev_list i)).comp₂ zero c_id
@[cp] theorem c_list_range_prim : code_prim c_list_range := by unfold c_list_range; apply_cp
@[simp] theorem c_list_range_evp : evalp O c_list_range n = l2n (List.range n) := by
  simp [c_list_range, -encode_list_cons, -encode_list_nil]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [-encode_list_cons, -encode_list_nil, ih]
    exact Eq.symm List.range_succ
@[simp] theorem c_list_range_ev : eval O c_list_range n = l2n (List.range n) := by simp [← evalp_eq_eval c_list_range_prim]
end Computability.Code
end list_range

section list_replicate
namespace Computability.Code
def c_list_replicate :=
  let prev_list := right.comp right
  let x := left
  (prec
  (c_list_nil)
  (c_list_concat.comp₂ prev_list x)).comp c_flip
@[cp] theorem c_list_replicate_prim : code_prim c_list_replicate := by unfold c_list_replicate; apply_cp
@[simp] theorem c_list_replicate_evp : evalp O c_list_replicate ⟪n,x⟫ = l2n (List.replicate n x) := by
  simp [c_list_replicate, -encode_list_cons, -encode_list_nil]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [-encode_list_cons, -encode_list_nil, ih]
    exact Eq.symm replicate_succ'
@[simp] theorem c_list_replicate_ev : eval O c_list_replicate ⟪n,x⟫ = l2n (List.replicate n x) := by simp [← evalp_eq_eval c_list_replicate_prim]
end Computability.Code
end list_replicate

section list_map'
namespace Computability.Code
/--
`evalp O (c_list_map' cf) ⟪lN, aux⟫ = ((n2l lN).map (fun ele => evalp O cf (Nat.pair ele aux)))`
-/
def c_list_map' (cf:Code) :=
  let lN  := left
  let aux := right
  (c_list_map cf).comp ((c_list_zipWith c_id).comp₂ lN (c_list_replicate.comp₂ (c_list_length.comp lN) aux))
@[cp] theorem c_list_map'_prim (hcf:code_prim cf) : code_prim (c_list_map' cf) := by unfold c_list_map'; apply_cp
@[simp] theorem c_list_map'_evp :
  evalp O (c_list_map' cf) ⟪lN, aux⟫
    =
  ((n2l lN).map (fun ele => evalp O cf (Nat.pair ele aux))) := by
  simp [c_list_map', -encode_list_cons, -encode_list_nil]
  induction (n2l lN) with
  | nil => simp [Nat.pair]
  | cons head tail ih => simp [replicate_succ]; exact ih
-- @[simp] theorem c_list_map'_ev : eval O (c_list_map' cf) lN = l2n ((n2l lN).map (evalp O cf)) := by simp [← evalp_eq_eval c_list_map'_prim]
end Computability.Code
end list_map'

@[simp] theorem getLastI_append {y:ℕ}: (x++[y]).getLastI = y := by
  rw [getLastI_eq_getLast?]
  simp
