import Computability.Constructions

open Nat
open Denumerable
open Encodable

-- variable {ℕ : Type*} {β : Type*} {σ : Type*} [Denumerable ℕ] [Denumerable β] [Denumerable σ]
private abbrev n2l := @ofNat (List ℕ) _
private abbrev l2n := @encode (List ℕ) _
private abbrev o2n := @encode (Option ℕ) _


section cons
namespace Nat.RecursiveIn.Code
def c_cons := succ
@[simp] theorem c_cons_ev_pr:code_prim c_cons := by unfold c_cons; repeat (first|assumption|simp|constructor)
@[simp] theorem c_cons_evp :eval_prim O c_cons (Nat.pair a lN)= l2n (List.cons a (n2l lN)) := by simp [c_cons]
@[simp] theorem c_cons_ev :eval O c_cons (Nat.pair a lN)= l2n (List.cons a (n2l lN)) := by simp [←eval_prim_eq_eval c_cons_ev_pr]
end Nat.RecursiveIn.Code
end cons

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
@[simp] theorem c_list_head?_evp : eval_prim O c_list_head? lN = o2n (List.head? (n2l lN))
  := by
  simp [c_list_head?]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
@[simp] theorem c_list_head?_ev:eval O c_list_head? lN = o2n (List.head? (n2l lN)) := by simp [← eval_prim_eq_eval c_list_head?_ev_pr]
end Nat.RecursiveIn.Code
end list_head?

section list_casesOn
namespace Nat.RecursiveIn.Code
def c_list_casesOn (cf cg:Code) :=
  let x := left.comp c_pred
  let xs := right.comp c_pred
  c_if_eq_te.comp₄ c_id (c_const 0) cf (cg.comp₂ x xs)
@[simp] theorem c_list_casesOn_ev_pr (hcf:code_prim cf) (hcg:code_prim cg):code_prim (c_list_casesOn cf cg) := by unfold c_list_casesOn; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_casesOn_evp {O} : eval_prim O (c_list_casesOn cf cg) lN =
  List.casesOn
  (n2l lN)
  (eval_prim O cf lN)
  (fun x xs => eval_prim O cg (Nat.pair (@encode ℕ _ x) (l2n xs)))
  := by
  simp [c_list_casesOn]
  by_cases hl:lN=0
  · simp [hl]
  · rw [←(exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl)).choose_spec]; simp
-- @[simp] theorem c_list_casesOn_ev :eval O (c_list_casesOn cf cg) lN =
--   List.casesOn
--   (n2l lN)
--   (eval_prim O cf lN)
--   (fun x xs => eval_prim O cg (Nat.pair (@encode ℕ _ x) (l2n xs))) := by
--     simp [← eval_prim_eq_eval c_list_casesOn_ev_pr]
end Nat.RecursiveIn.Code
end list_casesOn

section list_drop
namespace Nat.RecursiveIn.Code
def c_list_drop := (
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
@[simp] theorem c_list_getElem?_evp {O} : eval_prim O c_list_getElem? (Nat.pair lN i) = o2n (n2l lN)[i]? := by simp [c_list_getElem?]
@[simp] theorem c_list_getElem?_ev : eval O c_list_getElem? (Nat.pair lN i) = o2n (n2l lN)[i]? := by simp [← eval_prim_eq_eval c_list_getElem?_ev_pr]
end Nat.RecursiveIn.Code
end list_getElem?

/-
`foldl :: (a -> b -> a) -> a -> [b] -> a`
`foldl fn acc [] = acc`
`foldl fn acc (x:xs) = foldl fn (fn acc x) xs`
-/
section foldl
namespace Nat.RecursiveIn.Code
def c_foldl (cf:Code) (init:ℕ) := c_list_casesOn (c_const init) (cf)
@[simp] theorem c_foldl_ev_pr:code_prim c_foldl := by unfold c_foldl; repeat (first|assumption|simp|constructor)
@[simp] theorem c_foldl_evp {O}   : eval_prim O (c_foldl cf init) l =
  -- @encode ℕ _
  (
    (@List.foldl ℕ β)
    (fun a b => eval_prim O cf (Nat.pair a (@encode β _ b)))
    (init)
    (@ofNat (List β) _ l)
  )
  := by
  unfold c_foldl
  simp
  unfold l_to_n
  simp [Encodable.encode]
  simp [Encodable.encodeList]

  unfold n_to_l
  rw [show (@Encodable.encodeList ℕ _) = (@Encodable.encode (List ℕ) _) from rfl]
  simp
-- @[simp] theorem c_foldl_ev : eval O c_foldl (Nat.pair a l)= l_to_n ((@List.foldl ℕ) a (n_to_l l)) := by rw [← eval_prim_eq_eval c_foldl_ev_pr]; simp only [c_foldl_evp]
end Nat.RecursiveIn.Code
end foldl




#check @List.length
-- #check @Encodable.encode (List ℕ) 
#check (@Encodable.decode (List ℕ))
#eval (@Encodable.decode (List ℕ)) 7
#eval (@Denumerable.ofNat (List ℕ)) 7
