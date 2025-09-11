import Computability.Encoding
import Computability.Basic
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Dist

open Classical
open Nat.RecursiveIn.Code


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

namespace Nat.RecursiveIn.Code.nc_to_nn
@[coe] protected def lift (f:ℕ→Code) : ℕ→ℕ := fun x => encodeCode (f x)
instance : Coe (ℕ→Code) (ℕ→ℕ) := ⟨Nat.RecursiveIn.Code.nc_to_nn.lift⟩
end Nat.RecursiveIn.Code.nc_to_nn
-- namespace Nat.RecursiveIn.Code.cn_to_nn
-- @[coe] protected def lift (f:Code→ℕ) : ℕ→ℕ := fun x => (f x)
-- instance coe : Coe (Code→ℕ) (ℕ→ℕ) := ⟨Nat.RecursiveIn.Code.cn_to_nn.lift⟩
-- end Nat.RecursiveIn.Code.cn_to_nn
namespace Nat.RecursiveIn.Code.cc_to_nn
@[coe] protected def lift (f:Code→Code) : ℕ→ℕ := encodeCode ∘ f ∘ decodeCode
instance : Coe (Code→Code) (ℕ→ℕ) := ⟨Nat.RecursiveIn.Code.cc_to_nn.lift⟩
end Nat.RecursiveIn.Code.cc_to_nn

-- conversions between oracle and non-oracle versions
lemma PrimrecIn.PrimrecIn_Empty (h:Nat.PrimrecIn (fun _=>0) f):Nat.Primrec f := by
  induction' h with g hg g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g _ ih
  repeat {constructor}
  · (expose_names; exact Nat.Primrec.pair a_ih a_ih_1)
  repeat {constructor; assumption; try assumption}
  (expose_names; exact Nat.Primrec.prec a_ih a_ih_1)
lemma PrimrecIn.PrimrecIn₂_Empty {f:α→β→σ} (h:PrimrecIn₂ (fun _=>0) f):Primrec₂ f := by
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
namespace Nat.RecursiveIn.Code
@[aesop safe] inductive code_prim:Code → Prop
| zero:code_prim zero
| succ:code_prim succ
| left:code_prim left
| right:code_prim right
| oracle:code_prim oracle
| pair {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (pair a b)
| comp {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (comp a b)
| prec {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (prec a b)
def code_total (O) (c:Code) := ∀x, (eval O c x).Dom
@[simp] theorem zero_total {O} : code_total O zero := λ _ ↦ trivial
@[simp] theorem left_total {O} : code_total O left := λ _ ↦ trivial
@[simp] theorem right_total {O} : code_total O right := λ _ ↦ trivial
@[simp] theorem succ_total {O} : code_total O succ := λ _ ↦ trivial
@[simp] theorem oracle_total {O} : code_total O oracle := λ _ ↦ trivial
@[simp] theorem total_of_pair_left {O} (h:code_total O (pair cf cg)) : code_total O cf := by
  intro h2
  exact Part.left_dom_of_sub_dom (h h2)
@[simp] theorem total_of_pair_right {O} (h:code_total O (pair cf cg)) : code_total O cg := by
  intro h2
  exact Part.right_dom_of_div_dom (h h2)
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
  | zero                   => simp [eval]; exact fun x ↦ trivial
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
def eval_total (O:ℕ→ℕ) (c:Code) (h:code_total O c) : ℕ→ℕ := match c with
| zero       => fun _=>0
| succ       => Nat.succ
| left       => Nat.l
| right      => Nat.r
| oracle     => O
| pair cf cg => fun n => Nat.pair (eval_total O cf (total_of_pair_left h) n) (eval_total O cg (total_of_pair_right
  h) n)
| comp cf cg => fun x => (eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).get (total_of_comp_right h x)
| prec cf cg => fun x => (x.r).rec (eval_total O cf (total_of_prec_left h) x.l) fun y IH => (eval_total O cg (sorry)) <| Nat.pair x.l <| Nat.pair y IH
| rfind' _ => 0
@[simp] def eval_prim (O:ℕ→ℕ):Code→ℕ→ℕ
| zero       => fun _=>0
| succ       => Nat.succ
| left       => Nat.l
| right      => Nat.r
| oracle     => O
| pair cf cg => fun n => Nat.pair (eval_prim O cf n) (eval_prim O cg n)
| comp cf cg => fun n => eval_prim O cf (eval_prim O cg n)
| prec cf cg => unpaired fun z n => n.rec (eval_prim O cf z) fun y IH => (eval_prim O cg) <| Nat.pair z <| Nat.pair y IH
| rfind' _ => 0

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
theorem eval_total_eq_eval (h:code_total O c):eval_total O c h = eval O c := by sorry
theorem code_prim_prop (h:code_prim c):∀ O, Nat.PrimrecIn O (eval_prim O c) := by
  induction h with
  | zero => unfold eval_prim; exact fun O ↦ PrimrecIn.zero
  | succ => unfold eval_prim; exact fun O ↦ PrimrecIn.succ
  | left => unfold eval_prim; exact fun O ↦ PrimrecIn.left
  | right => unfold eval_prim; exact fun O ↦ PrimrecIn.right
  | oracle => unfold eval_prim; exact fun O ↦ PrimrecIn.oracle
  | pair ha hb ha_ih hb_ih => unfold eval_prim; exact fun O ↦ PrimrecIn.pair (ha_ih O) (hb_ih O)
  | comp ha hb ha_ih hb_ih => unfold eval_prim; exact fun O ↦ PrimrecIn.comp (ha_ih O) (hb_ih O)
  | prec ha hb ha_ih hb_ih => unfold eval_prim; exact fun O ↦ PrimrecIn.prec (ha_ih O) (hb_ih O)
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

end Nat.RecursiveIn.Code

/-
When registering a function as being primrec:
define:
c_f : the code of f
c_f_ev : proof that eval c_f = f
c_f_ev_pr : proof that eval c_f is prim

When registering a function on codes (g):
c_g : the function g from codes to codes
c_g_ev : proof that eval (c_g asd) has the intended behaviour
c_g_pr : proof that g itself is primrec
-/

namespace Nat.RecursiveIn.Code
/-- c_evconst takes as input a natural `(e,x)`, and returns an index to a program which calculates `[e](x)` regardless of its input. -/
def c_evconst (ex:ℕ) : ℕ  := comp ex.unpair.1 (Code.const ex.unpair.2)
@[simp] theorem c_evconst_ev : eval O (c_evconst (Nat.pair e x)) _z = eval O e x := by unfold c_evconst; simp [eval]
-- hm, the proof shouldnt be this long?
@[simp] theorem c_evconst_pr : Nat.PrimrecIn O c_evconst := by
  have rwmain : c_evconst = (fun ex:ℕ => (comp ex.unpair.1 ex.unpair.2:ℕ)) ∘ (fun ex:ℕ => Nat.pair ex.unpair.1 (Code.const ex.unpair.2)) := by
    funext xs
    simp only [Function.comp_apply, unpair_pair, decodeCode_encodeCode]
    exact rfl
  rw [rwmain]
  have main2 : Nat.PrimrecIn O fun ex:ℕ => Nat.pair ex.unpair.1 (Code.const ex.unpair.2) := by
    refine PrimrecIn.pair ?_ ?_
    · exact PrimrecIn.left
    · have main3 : (fun ex ↦ ((Code.const (unpair ex).2):ℕ)) = (fun ex => (Code.const ex :ℕ)) ∘ fun exa => (unpair exa).2 := by
        funext xs
        simp only [Function.comp_apply]
      have main4 : Nat.PrimrecIn O fun ex => (Code.const ex:ℕ) := by
        refine PrimrecIn.nat_iff.mp ?_
        apply const_prim
      have main5 : Nat.PrimrecIn O fun exa => (unpair exa).2 := by
        exact PrimrecIn.right
      rw [main3]
      apply Nat.PrimrecIn.comp main4 main5

  apply Nat.PrimrecIn.comp (PrimrecIn.nat_iff.mp (comp_prim)) main2


end Nat.RecursiveIn.Code









-- addednum for existscode in Encoding.lean
namespace Nat.RecursiveIn.Code
theorem exists_code_nat {O:ℕ → ℕ} {f:ℕ →. ℕ}:Nat.RecursiveIn O f ↔ ∃ c:ℕ , eval O c = f := by
  have h {f:ℕ →. ℕ}:Nat.RecursiveIn O f ↔ ∃ c:Nat.RecursiveIn.Code, eval O c = f := by exact
    exists_code
  constructor
  · intro h2
    obtain ⟨c, h3⟩ := h.mp h2
    use c.encodeCode
    simp only [decodeCode_encodeCode]
    exact h3
  · intro h2
    obtain ⟨c, h3⟩ := h2
    have h5: (∃ c:Nat.RecursiveIn.Code, eval O c = f) := by
      use decodeCode c
    exact exists_code.mpr h5
def eval₁ (O:ℕ→ℕ):ℕ→.ℕ := fun ex => eval O ex.unpair.1 ex.unpair.2
def evaln₁ (O:ℕ→ℕ):ℕ→ℕ := fun abc => Encodable.encode (evaln O abc.r.r abc.l abc.r.l)
theorem rec_eval₁:Nat.RecursiveIn O (eval₁ O) := by exact RecursiveIn.nat_iff.mp eval_part
theorem prim_evaln₁:Nat.PrimrecIn O (evaln₁ O) := by
  refine PrimrecIn.nat_iff.mp ?_
  unfold evaln₁
  have h:(fun (abc:ℕ) ↦ evaln O abc.r.r (abc.l) abc.r.l) = (fun (a:(ℕ×Code)×ℕ) ↦ evaln O a.1.1 a.1.2 a.2) ∘ (fun (abc:ℕ) => ((abc.r.r, abc.l), abc.r.l)) := by
    exact rfl
  -- rw [h]
  have h2:PrimrecIn O (fun (abc:ℕ) =>    (((abc.r.r, abc.l), abc.r.l):(ℕ×Code)×ℕ)    ) := by
    refine _root_.PrimrecIn.pair ?_ ?_
    · apply _root_.PrimrecIn.pair (_root_.PrimrecIn.comp (PrimrecIn.nat_iff.mpr PrimrecIn.right) (PrimrecIn.nat_iff.mpr PrimrecIn.right))
      apply _root_.PrimrecIn.comp
      · apply PrimrecIn.ofNat Nat.RecursiveIn.Code
      · exact PrimrecIn.nat_iff.mpr PrimrecIn.left
    · exact _root_.PrimrecIn.comp (PrimrecIn.nat_iff.mpr PrimrecIn.left) (PrimrecIn.nat_iff.mpr PrimrecIn.right)
  apply _root_.PrimrecIn.comp evaln_prim h2


-- theorem exists_code_for_eval₁:∃ c:ℕ, eval O c = eval₁ O := by
--   apply (exists_code_nat.mp)
--   exact rec_eval₁

theorem Nat.RecursiveIn.evalRecInO' {O} {f:ℕ→.ℕ} (h:Nat.RecursiveIn O f):Nat.RecursiveIn O (fun x => (f x) >>= (eval₁ O)) := by
  simp only [Part.bind_eq_bind]
  refine _root_.Nat.RecursiveIn.comp ?_ h
  apply rec_eval₁
theorem Nat.RecursiveIn.eval_K_computable:Nat.RecursiveIn O (fun x ↦ eval O x x) := by
  have h:(fun (x:ℕ) ↦ eval O x x) = (fun (x:ℕ) => eval O x.unpair.1 x.unpair.2) ∘ (fun x=>Nat.pair x x) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [h]
  refine Nat.RecursiveIn.partCompTotal ?_ ?_
  exact rec_eval₁
  exact Nat.RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id)
end Nat.RecursiveIn.Code









































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
