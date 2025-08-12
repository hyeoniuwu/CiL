import Computability.Constructions

open Nat
open Denumerable
open Encodable

variable {α : Type*} {β : Type*} {σ : Type*} [Denumerable α] [Denumerable β] [Denumerable σ]
-- def n_to_l := @ofNat (List α) _
-- def l_to_n := @encode (List α) _

section cons
namespace Nat.RecursiveIn.Code
def c_cons := succ
@[simp] theorem c_cons_ev_pr:code_prim c_cons := by unfold c_cons; repeat (first|assumption|simp|constructor)
@[simp] theorem c_cons_evp {O} {a l:ℕ} :eval_prim O c_cons (Nat.pair a l)= @encode (List α) _ ((@List.cons α) ((@ofNat α) a) (@ofNat (List α) _ l)) := by
  unfold c_cons
  simp
  -- unfold l_to_n
  -- simp [Encodable.encode]
  -- simp [Encodable.encodeList]

  -- unfold n_to_l
  -- rw [show (@Encodable.encodeList α _) = (@Encodable.encode (List α) _) from rfl]
  -- simp
-- @[simp] theorem c_cons_ev {l:ℕ}:eval O c_cons (Nat.pair a l)= l_to_n ((@List.cons ℕ) a (n_to_l l)) := by rw [← eval_prim_eq_eval c_cons_ev_pr]; simp only [c_cons_evp]
end Nat.RecursiveIn.Code
end cons

theorem test2 (h:¬la=0) : la≥1 := by exact one_le_iff_ne_zero.mpr h
theorem test (h:la≥1) : ∃x,succ x=la := by exact exists_add_one_eq.mpr h

#eval @encode (List (List ℕ)) _ List.nil
section list_casesOn
namespace Nat.RecursiveIn.Code
def c_list_casesOn (cf cg:Code) :=
  let x := left.comp c_pred
  let xs := right.comp c_pred
  c_if_eq_te.comp₄ c_id (c_const 0)
  cf $
  cg.comp₂ x xs
-- @[simp] theorem c_list_casesOn_ev_pr:code_prim c_list_casesOn := by unfold c_list_casesOn; repeat (first|assumption|simp|constructor)
@[simp] theorem c_list_casesOn_evp {O} {l:ℕ} : eval_prim O (c_list_casesOn cf cg) l =

  List.casesOn
  (@ofNat (List α) _ l)
  (eval_prim O cf l)
  (fun x xs => eval_prim O cg (Nat.pair (@encode α _ x) (@encode (List α) _ xs)))
  
  := by
  
  unfold c_list_casesOn
  simp
  by_cases hl:l=0
  · simp [hl]
  · rcases exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr hl) with ⟨lP1,hlP1⟩
    rw [←hlP1]
    simp
    
-- @[simp] theorem c_list_casesOn_ev {l:ℕ}:eval O c_list_casesOn (Nat.pair a l)= l_to_n ((@List.list_casesOn ℕ) a (n_to_l l)) := by rw [← eval_prim_eq_eval c_list_casesOn_ev_pr]; simp only [c_list_casesOn_evp]
end Nat.RecursiveIn.Code
end list_casesOn

section foldl
namespace Nat.RecursiveIn.Code
def c_foldl (cf:Code) (init:ℕ) := succ
@[simp] theorem c_foldl_ev_pr:code_prim c_foldl := by unfold c_foldl; repeat (first|assumption|simp|constructor)
@[simp] theorem c_foldl_evp {O} {l:ℕ} :eval_prim O (c_foldl cf init) l =
  @encode α _
  (
    (@List.foldl α β)
    (fun a b => @ofNat α _ $ eval_prim O cf (Nat.pair (@encode α _ a) (@encode β _ b)))
    (@ofNat α _ init)
    (@ofNat (List β) _ l)
  )
  := by
  unfold c_foldl
  simp
  unfold l_to_n
  simp [Encodable.encode]
  simp [Encodable.encodeList]

  unfold n_to_l
  rw [show (@Encodable.encodeList α _) = (@Encodable.encode (List α) _) from rfl]
  simp
-- @[simp] theorem c_foldl_ev {l:ℕ}:eval O c_foldl (Nat.pair a l)= l_to_n ((@List.foldl ℕ) a (n_to_l l)) := by rw [← eval_prim_eq_eval c_foldl_ev_pr]; simp only [c_foldl_evp]
end Nat.RecursiveIn.Code
end foldl




#check @List.length
-- #check @Encodable.encode (List ℕ) 
#check (@Encodable.decode (List ℕ))
#eval (@Encodable.decode (List ℕ)) 7
#eval (@Denumerable.ofNat (List ℕ)) 7
