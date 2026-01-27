import Computability.Basic

namespace Computability.Code
open Classical Nat Part

-- @[simp] theorem total_of_prec_right {O} (h:code_total O (prec cf cg)) : code_total O cf := by
--   intro x
--   unfold code_total at h
--   simp [eval] at h
--   have hx := h (Nat.pair x 0)
--   simp at hx
--   exact hx

  -- exact?
  -- exact fun x ↦ Part.right_dom_of_div_dom (h x)
-- def eval_total (O:ℕ→ℕ) (c:Code) {h:code_total O c}:ℕ→ℕ := fun x => (eval O c x).get (h x)
def evalt (O:ℕ→ℕ) (c:Code) (h:code_total O c) : ℕ→ℕ := λ x ↦ (eval O c x).get (h x)
-- def eval_total (O:ℕ→ℕ) (c:Code) (h:code_total O c) : ℕ→ℕ := match c with
-- | zero       => λ _ ↦ 0
-- | succ       => Nat.succ
-- | left       => Nat.l
-- | right      => Nat.r
-- | oracle     => O
-- | pair cf cg => fun n => Nat.pair (eval_total O cf (total_of_pair_left h) n) (eval_total O cg (total_of_pair_right
--   h) n)
-- | comp cf cg => fun x => (eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).get (total_of_comp_right h x)
-- | prec cf cg => fun x => (x.r).rec (eval_total O cf (total_of_prec_left h) x.l) fun y IH => (eval_total O cg (sorry)) <| Nat.pair x.l <| Nat.pair y IH
-- | rfind' _ => 0
noncomputable def Part.getD (p:Part ℕ) : ℕ := if h:p.Dom then p.get h else 0
noncomputable def eval_total (O:ℕ→ℕ) (c:Code) : ℕ→ℕ := match c with
| zero       => λ _ ↦ 0
| succ       => Nat.succ
| left       => Nat.l
| right      => Nat.r
| oracle     => O
| pair cf cg => fun x => Nat.pair (eval_total O cf x) (eval_total O cg x)
| comp cf cg => fun x => eval_total O cf (eval_total O cg x)
| prec cf cg => unpaired fun z n => n.rec (eval_total O cf z) fun y IH => (eval_total O cg) <| Nat.pair z <| Nat.pair y IH
| rfind' cf =>  Nat.unpaired fun a m => ((Nat.rfind fun n => (fun x => x = 0) <$> eval_total O cf (Nat.pair a (n + m))).map (· + m)).getD

-- theorem eval_total_eq_eval (h:code_total O c):eval_total O c = eval O c := by
--   sorry
  -- induction c generalizing h with
  -- | zero => exact rfl
  -- | succ => exact rfl
  -- | left => exact rfl
  -- | right => exact rfl
  -- | oracle => exact rfl
  -- | pair ha hb ha_ih hb_ih =>
  --   unfold eval
  --   rw [← ha_ih (total_of_pair_left h)]
  --   rw [← hb_ih (total_of_pair_right h)]
  --   exact pair' (eval_total O ha) (eval_total O hb)
  -- | comp ha hb ha_ih hb_ih =>
  --   unfold eval_total
  --   simp [eval]
  --   funext xs
  --   simp
  --   expose_names
  --   simp only [show eval O b xs = Part.some (eval_total O b xs) from by exact congrFun (_root_.id (Eq.symm hb_ih)) xs]
  --   simp
  --   simp only [show eval O a (eval_total O b xs) = Part.some (eval_total O a (eval_total O b xs)) from by exact congrFun (_root_.id (Eq.symm ha_ih)) (eval_total O b xs)]
  -- | prec ha hb ha_ih hb_ih =>
  --   unfold eval
  --   unfold eval_total
  --   have := ha_ih ?_
  --   rotate_left
  --   exact total_of_prec_left h
  --   rw [← this]

  --   simp
  --   funext xs
  --   simp

  --   induction xs.r with
  --   | zero => simp
  --   | succ n ih =>
  --     simp
  --     rw [← ih]
  --     simp [Part.bind_some]

  --     sorry

  --   have := hb_ih ?_
  --   rotate_left

  -- | rfind' cf hcf =>
  --   sorry
