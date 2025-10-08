import Computability.Encoding
import Computability.Label
import Computability.Basic
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Dist

open Classical
open Computability.Code
open Nat


-- general helper functions
theorem pair_nonzero_right_pos_aux : ¬ (Nat.pair x (s+1)=0) := by
  rw  [show 0=Nat.pair 0 0 from rfl]
  rw [pair_eq_pair]
  intro h
  have hr := h.right
  contradiction
@[simp] theorem pair_nonzero_right_pos : (Nat.pair x (s+1))>0 := by
  exact zero_lt_of_ne_zero pair_nonzero_right_pos_aux
@[simp] theorem map_getI : (List.map (f) (List.range (s + 1))).getI x = if x<s+1 then f x else 0 := by
  unfold List.getI
  cases Classical.em (x<s+1) with
  | inl h => simp [h]
  | inr h => simp [h]
theorem pair_r_gt0 {x} : x>0→(Nat.pair y x)>0 := by
  contrapose
  simp
  intro h
  rw [show x=(Nat.pair y x).unpair.2 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
theorem pair_l_gt0 {x} : x>0→(Nat.pair x y)>0 := by
  contrapose
  simp
  intro h
  rw [show x=(Nat.pair x y).unpair.1 from by simp [unpair_pair]]
  rw [h]
  simp [unpair_zero]
-- general lemmas for later theorems
protected theorem isSome.bind {o : Option α} (h : o.isSome) (f : α → Option β) : o.bind f = f (o.get h) := by
  have : o = some (o.get h) := by exact Option.eq_some_of_isSome h
  ext b
  constructor
  intro h2
  rw [this] at h2
  simp only [Option.bind_some] at h2
  exact h2

  intro h2
  rw [this]
  simp only [Option.bind_some]
  exact h2
theorem listrwgen (n): (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
  simp
  exact List.range_succ
theorem ne_of_mem_imp_not_mem {y:Part ℕ} (h:x∈y) (h2:x≠z) : z∉y := by
  have aux: y=Part.some x := by exact Part.eq_some_iff.mpr h
  rw [aux]
  aesop? says
    subst aux
    simp_all only [ne_eq, Part.mem_some_iff]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [not_true_eq_false]
theorem opt_ne_of_mem_imp_not_mem {y:Option ℕ} (h:x∈y) (h2:x≠z) : z∉y := by
  aesop
lemma forall_mem_part {y:Part ℕ} (h1:y.Dom) (h2:∀ x ∈ y, x = c) : c∈y := by
  contrapose h2
  simp
  use y.get h1
  constructor
  exact Part.get_mem h1
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  have : y.get h1 ∈ y := by exact Part.get_mem h1
  contradiction
lemma forall_mem_option {y:Option ℕ} (h1:y.isSome) (h2:∀ x ∈ y, x = c) : c∈y := by
  contrapose h2
  simp
  use y.get h1
  constructor
  exact Option.eq_some_of_isSome h1
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  have : y.get h1 ∈ y := by exact Option.eq_some_of_isSome h1
  contradiction
-- helper functions for Part/Option
theorem Part.eq_some_imp_dom {p:Part ℕ} : p=Part.some x → p.Dom := by
  intro a
  subst a
  exact trivial
theorem Part.mem_imp_dom {p:Part ℕ} : x∈p → p.Dom := λ h ↦ Part.eq_some_imp_dom (Part.eq_some_iff.mpr h)
theorem Part.dom_imp_some {x:Part ℕ} (h:x.Dom) : x=Part.some (x.get h) := by
  exact Part.get_eq_iff_eq_some.mp rfl
theorem Option.dom_imp_some {x:Option ℕ} (h:x.isSome) : x=some (x.get h) := by
  exact Option.eq_some_of_isSome h
theorem Option.isSome_iff_mem {o:Option β}: o.isSome ↔ (∃z,z∈o) := by
  have h1 := @Option.isSome_iff_exists β o
  simp [h1]
lemma isSome_iff_not_none : (¬o=Option.none)↔(o.isSome) := by
  apply Iff.intro
  · intro a
    simp [Option.eq_none_iff_forall_ne_some] at a
    rcases a with ⟨h1,h2⟩
    exact Option.isSome_of_mem h2
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [Option.isSome_none, Bool.false_eq_true]
lemma Part.eq_none_iff_forall_ne_some : o = Part.none ↔ ∀ a, o ≠ Part.some a := by
  have := (@Part.ne_none_iff _ o).not
  simp at this
  exact this
  -- cases o <;> simp
lemma Part.not_none_iff_dom : (¬o=Part.none)↔(o.Dom) := by
  apply Iff.intro
  · intro a
    simp [Part.eq_none_iff_forall_ne_some] at a
    rcases a with ⟨h1,h2⟩
    rw [h2]
    exact trivial
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    exact a
lemma Part.ne_of_get_ne {p1 p2:Part ℕ} {h1:p1.Dom} {h2:p2.Dom} (h:p1.get h1≠p2.get h2) : (p1≠p2) := by aesop
lemma Part.ne_of_get_ne' {p1:Part ℕ} {h1:p1.Dom} (h:p1.get h1≠x) : (p1≠Part.some x) := by aesop

variable {α:Type*} {β:Type*} {σ:Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

-- @[simp] abbrev Nat.l (n:ℕ) := n.unpair.1
-- @[simp] abbrev Nat.r (n:ℕ) := n.unpair.2
def Nat.l (n:ℕ) := n.unpair.1
def Nat.r (n:ℕ) := n.unpair.2
@[simp] theorem pair_l : (Nat.pair x y).l = x := by simp [Nat.l]
@[simp] theorem pair_r : (Nat.pair x y).r = y := by simp [Nat.r]
@[simp] theorem pair_lr : (Nat.pair x.l x.r) = x := by simp [Nat.r, Nat.l]
@[simp] theorem unpair1_to_l {n:ℕ} : (n.unpair.1) = n.l := by simp [Nat.l]
@[simp] theorem unpair2_to_r {n:ℕ} : (n.unpair.2) = n.r := by simp [Nat.r]
@[simp, reducible]
def Nat.unpaired2 {α} (f : ℕ → ℕ → α) (n : ℕ) : α := f n.l n.r
-- @[simp, reducible]
-- def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α := f n.unpair.1 n.unpair.2
@[simp] abbrev Nat.fzero:ℕ→ℕ:=λ_↦0

def n2b (n:ℕ) : Bool := if n=0 then false else true
def b2n (b:Bool) : ℕ := if b then 1 else 0
def n2b' (n:ℕ) : Bool := if n=0 then true else false
def b'2n (b:Bool) : ℕ := if b then 0 else 1
open Denumerable
open Encodable
abbrev n2o := @ofNat (Option ℕ) _
abbrev o2n := @encode (Option ℕ) _

-- TODO: maybe delete the below?
namespace Computability.Code.nc_to_nn
@[coe] protected def lift (f:ℕ→Code) : ℕ→ℕ := fun x => c2n (f x)
instance : Coe (ℕ→Code) (ℕ→ℕ) := ⟨Computability.Code.nc_to_nn.lift⟩
end Computability.Code.nc_to_nn
-- namespace Computability.Code.cn_to_nn
-- @[coe] protected def lift (f:Code→ℕ) : ℕ→ℕ := fun x => (f x)
-- instance coe : Coe (Code→ℕ) (ℕ→ℕ) := ⟨Computability.Code.cn_to_nn.lift⟩
-- end Computability.Code.cn_to_nn
namespace Computability.Code.cc_to_nn
@[coe] protected def lift (f:Code→Code) : ℕ→ℕ := c2n ∘ f ∘ n2c
instance : Coe (Code→Code) (ℕ→ℕ) := ⟨Computability.Code.cc_to_nn.lift⟩
end Computability.Code.cc_to_nn

-- conversions between oracle and non-oracle versions
lemma PrimrecIn.PrimrecIn_Empty (h:Nat.PrimrecIn (λ _ ↦ 0) f):Nat.Primrec f := by
  induction' h with g hg g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g _ ih
  repeat {constructor}
  · (expose_names; exact Nat.Primrec.pair a_ih a_ih_1)
  repeat {constructor; assumption; try assumption}
  (expose_names; exact Nat.Primrec.prec a_ih a_ih_1)
lemma PrimrecIn.PrimrecIn₂_Empty {f:α→β→σ} (h:PrimrecIn₂ (λ _ ↦ 0) f):Primrec₂ f := by
  unfold PrimrecIn₂ at h
  unfold Primrec₂
  apply PrimrecIn.PrimrecIn_Empty
  exact h
theorem Primrec.to_PrimrecIn₂ {f:α→β→σ} (h:Primrec₂ f):PrimrecIn₂ O f := by
  unfold Primrec₂ at h
  unfold PrimrecIn₂
  apply Primrec.to_PrimrecIn
  exact h
theorem PrimrecIn.PrimrecIn₂_iff_Primrec₂ {f:α→β→σ}:(∀O,PrimrecIn₂ O f) ↔ Primrec₂ f := by
  constructor
  · exact fun a ↦ PrimrecIn₂_Empty (a fun x ↦ 0)
  · exact fun a O ↦ Primrec.to_PrimrecIn₂ a
theorem PrimrecIn.PrimrecIn_iff_Primrec:(∀O,Nat.PrimrecIn O f) ↔ Nat.Primrec f := by
  constructor
  · exact fun a ↦ PrimrecIn.PrimrecIn_Empty (a fun x ↦ 0)
  · exact fun a O ↦ Nat.Primrec.to_PrimrecIn a

-- templates for primrec constructions as codes
namespace Computability.Code
@[aesop safe, cp] inductive code_prim:Code → Prop
| zero:code_prim zero
| succ:code_prim succ
| left:code_prim left
| right:code_prim right
| oracle:code_prim oracle
| pair {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (pair a b)
| comp {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (comp a b)
| prec {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (prec a b)
@[cp] theorem zero_ev_pr : code_prim zero := code_prim.zero
@[cp] theorem succ_ev_pr : code_prim succ := code_prim.succ
@[cp] theorem left_ev_pr : code_prim left := code_prim.left
@[cp] theorem right_ev_pr : code_prim right := code_prim.right
@[cp] theorem oracle_ev_pr : code_prim oracle := code_prim.oracle
@[cp] theorem pair_ev_pr (ha:code_prim a) (hb:code_prim b) : code_prim (pair a b) := code_prim.pair ha hb
@[cp] theorem comp_ev_pr (ha:code_prim a) (hb:code_prim b) : code_prim (comp a b) := code_prim.comp ha hb
@[cp] theorem prec_ev_pr (ha:code_prim a) (hb:code_prim b) : code_prim (prec a b) := code_prim.prec ha hb
def code_total (O) (c:Code) := ∀x, (eval O c x).Dom
@[simp] theorem zero_total {O} : code_total O zero := λ _ ↦ trivial
@[simp] theorem left_total {O} : code_total O left := λ _ ↦ trivial
@[simp] theorem right_total {O} : code_total O right := λ _ ↦ trivial
@[simp] theorem succ_total {O} : code_total O succ := λ _ ↦ trivial
@[simp] theorem oracle_total {O} : code_total O oracle := λ _ ↦ trivial
theorem total_pair_iff : (code_total O cf) ∧ (code_total O cg) ↔ (code_total O (pair cf cg)) :=
  ⟨
    λ h x ↦ ⟨h.left x, h.right x⟩
  ,
    λ h ↦ ⟨λ x ↦ Part.left_dom_of_sub_dom (h x) , λ x ↦ Part.right_dom_of_div_dom (h x)⟩
  ⟩
@[simp] theorem total_pair_of (hcf : code_total O cf) (hcg : code_total O cg) : (code_total O (pair cf cg)) := total_pair_iff.mp ⟨hcf,hcg⟩
theorem total_comp_of (hcf : code_total O cf) (hcg : code_total O cg) : (code_total O (comp cf cg)) := by
  intro x
  simp [eval]
  use hcg x
  exact hcf ((eval O cg x).get (hcg x))
@[simp] theorem total_of_pair_left {O} (h:code_total O (pair cf cg)) : code_total O cf :=
  (total_pair_iff.mpr h).left
@[simp] theorem total_of_pair_right {O} (h:code_total O (pair cf cg)) : code_total O cg :=
  (total_pair_iff.mpr h).right
@[simp] theorem total_of_comp_left {O} (h:code_total O (comp cf cg)) : code_total O cg := by
  intro h2
  exact Part.Dom.of_bind (h h2)
@[simp] theorem total_of_comp_right {O} (h:code_total O (comp cf cg)) : ∀x, (eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).Dom := by
  exact fun x ↦ Part.right_dom_of_div_dom (h x)
@[simp] theorem total_of_prec_left {O} (h:code_total O (prec cf cg)) : code_total O cf := by
  intro x
  unfold code_total at h
  simp [eval] at h
  have hx := h (Nat.pair x 0)
  simp at hx
  exact hx
-- @[simp] theorem total_of_prec_right {O} (h:code_total O (prec cf cg)) : code_total O cf := by
--   intro x
--   unfold code_total at h
--   simp [eval] at h
--   have hx := h (Nat.pair x 0)
--   simp at hx
--   exact hx

  -- exact?
  -- exact fun x ↦ Part.right_dom_of_div_dom (h x)

theorem prim_total (h:code_prim c): code_total O c := by
  unfold code_total
  induction h with
  | zero                   => simp [eval];
  | succ                   => simp [eval];
  | left                   => simp [eval];
  | right                  => simp [eval];
  | oracle                 => simp [eval];
  | pair ha hb ha_ih hb_ih => simp [eval, Seq.seq]; exact fun x ↦ ⟨ha_ih x, hb_ih x⟩
  | comp ha hb ha_ih hb_ih =>
    simp [eval]
    intro x
    use hb_ih x
    (expose_names; exact ha_ih ((eval O b x).get (hb_ih x)))
  | prec ha hb ha_ih hb_ih =>
    expose_names
    simp [eval]
    intro x
    induction x.r with
    | zero => exact ha_ih x.l
    | succ y' IH' =>

      simp
      expose_names;
      use IH'
      apply hb_ih
-- def eval_total (O:ℕ→ℕ) (c:Code) {h:code_total O c}:ℕ→ℕ := fun x => (eval O c x).get (h x)
theorem eval_total_comp (h:code_total O (comp cf cg)) :
  eval O (comp cf cg) x = Part.some ((eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).get (total_of_comp_right h x)) := by
    simp
    simp [eval]
    exact Part.Dom.bind (Part.Dom.of_bind (h x)) (eval O cf)
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
@[simp] def eval_prim (O:ℕ→ℕ):Code→ℕ→ℕ
| zero       => λ _ ↦ 0
| succ       => Nat.succ
| left       => Nat.l
| right      => Nat.r
| oracle     => O
| pair cf cg => fun x => Nat.pair (eval_prim O cf x) (eval_prim O cg x)
| comp cf cg => fun x => eval_prim O cf (eval_prim O cg x)
| prec cf cg => unpaired fun z n => n.rec (eval_prim O cf z) fun y IH => (eval_prim O cg) <| Nat.pair z <| Nat.pair y IH
| rfind' _ => λ _ ↦ 0

theorem eval_prim_eq_eval (h:code_prim c):eval_prim O c = eval O c := by
  induction h with
  | zero => exact rfl
  | succ => exact rfl
  | left => exact rfl
  | right => exact rfl
  | oracle => exact rfl
  | pair ha hb ha_ih hb_ih =>
    unfold eval_prim
    simp [eval]
    funext xs
    simp [Seq.seq]
    expose_names
    simp only [show eval O a xs = Part.some (eval_prim O a xs) from by exact congrFun (_root_.id (Eq.symm ha_ih)) xs]
    simp only [show eval O b xs = Part.some (eval_prim O b xs) from by exact congrFun (_root_.id (Eq.symm hb_ih)) xs]
    simp
  | comp ha hb ha_ih hb_ih =>
    unfold eval_prim
    simp [eval]
    funext xs
    simp
    expose_names
    simp only [show eval O b xs = Part.some (eval_prim O b xs) from by exact congrFun (_root_.id (Eq.symm hb_ih)) xs]
    simp
    simp only [show eval O a (eval_prim O b xs) = Part.some (eval_prim O a (eval_prim O b xs)) from by exact congrFun (_root_.id (Eq.symm ha_ih)) (eval_prim O b xs)]
  | prec ha hb ha_ih hb_ih =>
    unfold eval_prim
    simp [eval]
    funext xs
    simp
    expose_names
    induction xs.r with
    | zero =>
      simp
      simp only [show eval O a xs.l = Part.some (eval_prim O a xs.l) from by exact congrFun (_root_.id (Eq.symm ha_ih)) xs.l]
    | succ y' IH' =>
      have h0:@Nat.rec (fun x ↦ Part ℕ) (eval O a xs.l) (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair xs.l (Nat.pair y i))) (y'+1) = ((@Nat.rec (fun x ↦ Part ℕ) (eval O a xs.l)
  (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair xs.l (Nat.pair y i))) y').bind fun i ↦ eval O b (Nat.pair xs.l (Nat.pair y' i))) := by
        exact rfl
      rw [h0]
      rw [←IH']
      rw [Part.bind_some]
      simp
      rw [show eval O b ((Nat.pair xs.l (Nat.pair y' (Nat.rec (eval_prim O a xs.l) (fun y IH ↦ eval_prim O b (Nat.pair xs.l (Nat.pair y IH))) y')))) = Part.some (eval_prim O b ((Nat.pair xs.l (Nat.pair y' (Nat.rec (eval_prim O a xs.l) (fun y IH ↦ eval_prim O b (Nat.pair xs.l (Nat.pair y IH))) y'))))) from by exact congrFun (_root_.id (Eq.symm hb_ih)) ((Nat.pair xs.l (Nat.pair y' (Nat.rec (eval_prim O a xs.l) (fun y IH ↦ eval_prim O b (Nat.pair xs.l (Nat.pair y IH))) y'))))]
theorem eval_prim_eq_eval_ext (h:code_prim c): eval O c x = eval_prim O c x := congrFun (_root_.id (Eq.symm (@eval_prim_eq_eval c O h))) x
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
@[simp 1000] theorem code_prim_prop : Nat.PrimrecIn O (eval_prim O c) := by
  induction c with
  | zero => exact Nat.PrimrecIn.zero
  | succ => exact Nat.PrimrecIn.succ
  | left => exact Nat.PrimrecIn.left
  | right => exact Nat.PrimrecIn.right
  | oracle => exact Nat.PrimrecIn.oracle
  | pair ha hb ha_ih hb_ih => unfold eval_prim; exact Nat.PrimrecIn.pair (ha_ih) (hb_ih)
  | comp ha hb ha_ih hb_ih => unfold eval_prim; exact Nat.PrimrecIn.comp (ha_ih) (hb_ih)
  | prec ha hb ha_ih hb_ih => unfold eval_prim; exact Nat.PrimrecIn.prec (ha_ih) (hb_ih)
  | rfind' ha ha_ih => exact Nat.PrimrecIn.zero
theorem code_prim_of_primrecIn (h:Nat.PrimrecIn O f) : ∃ c, code_prim c ∧ f=eval_prim O c := by
  induction h with
  | zero => use Code.zero; exact ⟨code_prim.zero,rfl⟩
  | succ => use Code.succ; exact ⟨code_prim.succ,rfl⟩
  | left => use Code.left; exact ⟨code_prim.left,rfl⟩
  | right => use Code.right; exact ⟨code_prim.right,rfl⟩
  | oracle => use Code.oracle; exact ⟨code_prim.oracle,rfl⟩
  | pair pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.pair cf cg;
    constructor
    · exact code_prim.pair hcf.left hcg.left
    · simp only [eval_prim]; rw [hcf.right, hcg.right]
  | comp pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.comp cf cg;
    constructor
    · exact code_prim.comp hcf.left hcg.left
    · simp only [eval_prim]; rw [hcf.right, hcg.right]
  | prec pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.prec cf cg;
    constructor
    · exact code_prim.prec hcf.left hcg.left
    · simp only [eval_prim]; rw [hcf.right, hcg.right]

end Computability.Code



theorem Primrec.projection {f:α → β → σ} {a:α} (h:Primrec₂ f):Primrec (f a) := by
  refine Primrec₂.comp h ?_ ?_
  · exact const a
  · exact Primrec.id
theorem PrimrecIn.projection {f:α → β → σ} {a:α} (h:PrimrecIn₂ O f):PrimrecIn O (f a) := by
  refine PrimrecIn₂.comp h ?_ ?_
  · exact const a
  · exact PrimrecIn.id
lemma Nat.Primrec.pair_proj:Nat.Primrec (Nat.pair x) := by
  refine Primrec.nat_iff.mp ?_
  apply Primrec.projection
  exact Primrec₂.natPair
