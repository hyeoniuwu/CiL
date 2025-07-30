import Computability.Encoding
import Computability.Basic
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Dist

open Classical
-- open Computability
open Nat.RecursiveIn.Code

variable {α:Type*} {β:Type*} {σ:Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

@[simp] abbrev Nat.l (n:ℕ) := n.unpair.1
@[simp] abbrev Nat.r (n:ℕ) := n.unpair.2

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
inductive code_prim:Code → Prop
| zero:code_prim zero
| succ:code_prim succ
| left:code_prim left
| right:code_prim right
| oracle:code_prim oracle
| pair {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (pair a b)
| comp {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (comp a b)
| prec {a b:Code} (ha:code_prim a) (hb:code_prim b):code_prim (prec a b)
theorem prim_total (h:code_prim c):∀x,(eval O c x).Dom := by
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
    induction (unpair x).2 with
    | zero => exact ha_ih (unpair x).1
    | succ y' IH' =>

      simp
      expose_names;
      use IH'
      apply hb_ih
def eval_total (O:ℕ→ℕ) (c:Code) {h:∀x,(eval O c x).Dom}:ℕ→ℕ := fun x => (eval O c x).get (h x)
def eval_prim (O:ℕ→ℕ):Code→ℕ→ℕ
| zero       => fun x=>0
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
    induction (unpair xs).2 with
    | zero =>
      simp
      simp only [show eval O a (unpair xs).1 = Part.some (eval_prim O a (unpair xs).1) from by exact congrFun (_root_.id (Eq.symm ha_ih)) (unpair xs).1]
    | succ y' IH' =>
      have h0:@Nat.rec (fun x ↦ Part ℕ) (eval O a (unpair xs).1) (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair (unpair xs).1 (Nat.pair y i))) (y'+1) = ((@Nat.rec (fun x ↦ Part ℕ) (eval O a (unpair xs).1)
  (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair (unpair xs).1 (Nat.pair y i))) y').bind fun i ↦ eval O b (Nat.pair (unpair xs).1 (Nat.pair y' i))) := by
        exact rfl
      rw [h0]
      rw [←IH']
      rw [Part.bind_some]
      simp
      rw [show eval O b ((Nat.pair (unpair xs).1 (Nat.pair y' (Nat.rec (eval_prim O a (unpair xs).1) (fun y IH ↦ eval_prim O b (Nat.pair (unpair xs).1 (Nat.pair y IH))) y')))) = Part.some (eval_prim O b ((Nat.pair (unpair xs).1 (Nat.pair y' (Nat.rec (eval_prim O a (unpair xs).1) (fun y IH ↦ eval_prim O b (Nat.pair (unpair xs).1 (Nat.pair y IH))) y'))))) from by exact congrFun (_root_.id (Eq.symm hb_ih)) ((Nat.pair (unpair xs).1 (Nat.pair y' (Nat.rec (eval_prim O a (unpair xs).1) (fun y IH ↦ eval_prim O b (Nat.pair (unpair xs).1 (Nat.pair y IH))) y'))))]

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


theorem exists_code_for_eval₁:∃ c:ℕ, eval O c = eval₁ O := by
  apply (exists_code_nat.mp)
  exact rec_eval₁

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










section id
namespace Nat.RecursiveIn.Code
def c_id := left.pair right
@[simp] theorem c_id_ev_pr:code_prim c_id := by unfold c_id; repeat constructor
@[simp] theorem c_id_evp:eval_prim O c_id n= n := by simp [c_id,eval_prim]
-- @[simp] theorem c_id_ev:eval O c_id n= n := by
  -- #check @eval_prim_eq_eval c_id O c_id_ev_pr
  -- apply (@eval_prim_eq_eval c_id O c_id_ev_pr)
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.id:Nat.PrimrecIn O Nat.id := by ...
-- theorem Nat.Primrec.id:Nat.Primrec Nat.id := by ...
end id
section const
namespace Nat.RecursiveIn.Code
def c_const:ℕ→Code
| 0 => zero
| n+1 => comp succ (c_const n)
@[simp] theorem c_const_ev_pr:code_prim (c_const n) := by
  induction n
  · unfold c_const; exact code_prim.zero
  · unfold c_const
    expose_names
    exact code_prim.comp code_prim.succ h
@[simp] theorem c_const_ev: ∀ n m, eval_prim O (c_const n) m = n
| 0, _ => rfl
| n+1, m => by simp! [c_const_ev n m]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.const:Nat.PrimrecIn O Nat.const := by ...
-- theorem Nat.Primrec.const:Nat.Primrec Nat.const := by ...
end const

section sgsg'
/-- The signum function on naturals.  -/
@[simp] def Nat.sg := fun x => if x=0 then 0 else 1
/-- Maps zero to 1 and non-zero natural numbers to 0. This is the inverse of `Nat.sg` for boolean-like computations. -/
@[simp] def Nat.sg' := fun x => if x=0 then 1 else 0
namespace Nat.RecursiveIn.Code
def c_sg := comp (prec zero (((c_const 1).comp left).comp left)) (pair zero c_id)
@[simp] theorem c_sg_ev_pr:code_prim c_sg := by unfold c_sg; repeat constructor
@[simp] theorem c_sg_evp:eval_prim O c_sg = Nat.sg := by
  simp [c_sg,eval_prim]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp] theorem c_sg_ev : eval O c_sg = Nat.sg := by rw [← eval_prim_eq_eval c_sg_ev_pr]; simp only [c_sg_evp]
def c_sg' := comp (prec (c_const 1) (((zero).comp left).comp left)) (pair zero c_id)
@[simp] theorem c_sg'_ev_pr:code_prim c_sg' := by unfold c_sg'; repeat constructor
@[simp] theorem c_sg'_evp:eval_prim O c_sg' = Nat.sg' := by
  simp [c_sg',eval_prim]
  funext n; induction n with
  | zero => exact rfl
  | succ n _ => simp
@[simp] theorem c_sg'_ev : eval O c_sg' = Nat.sg' := by rw [← eval_prim_eq_eval c_sg'_ev_pr]; simp only [c_sg'_evp]
end Nat.RecursiveIn.Code
theorem Nat.PrimrecIn.sg:Nat.PrimrecIn O Nat.sg := by rw [←c_sg_evp]; apply code_prim_prop c_sg_ev_pr
theorem Nat.PrimrecIn.sg':Nat.PrimrecIn O Nat.sg' := by rw [←c_sg'_evp]; apply code_prim_prop c_sg'_ev_pr
theorem Nat.Primrec.sg:Nat.Primrec Nat.sg := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.sg
theorem Nat.Primrec.sg':Nat.Primrec Nat.sg' := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.sg'
end sgsg'


section add
namespace Nat.RecursiveIn.Code
def c_add := (prec c_id ((succ.comp right).comp right))
@[simp] theorem c_add_ev_pr:code_prim c_add := by unfold c_add; repeat constructor
@[simp] theorem c_add_evp:eval_prim O c_add = unpaired Nat.add := by
  simp [c_add,eval_prim]
  funext n;
  simp [unpaired]
  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h => exact Nat.add_left_inj.mpr h
@[simp] theorem c_add_ev:eval O c_add = unpaired Nat.add := by rw [← eval_prim_eq_eval c_add_ev_pr]; simp only [c_add_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.add:Nat.PrimrecIn O Nat.add := by ...
-- theorem Nat.Primrec.add:Nat.Primrec Nat.add := by ...
end add
section mul
namespace Nat.RecursiveIn.Code
def c_mul := prec zero (c_add.comp (pair left (right.comp right)))
@[simp] theorem c_mul_ev_pr:code_prim c_mul := by unfold c_mul; repeat constructor
@[simp] theorem c_mul_evp:eval_prim O c_mul = unpaired Nat.mul := by
  simp [c_mul,eval_prim]
  funext n;
  simp [unpaired]
  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h =>
    simp [*, mul_succ];
    (expose_names; exact Nat.add_comm (unpair n_1).1 ((unpair n_1).1 * n))
@[simp] theorem c_mul_ev:eval O c_mul = unpaired Nat.mul := by rw [← eval_prim_eq_eval c_mul_ev_pr]; simp only [c_mul_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.mul:Nat.PrimrecIn O Nat.mul := by ...
-- theorem Nat.Primrec.mul:Nat.Primrec Nat.mul := by ...
end mul

section prec1
namespace Nat.RecursiveIn.Code
def c_prec1 (m) (cf:Code) := ((prec (c_const m) (cf.comp right)).comp (zero.pair c_id))
@[simp] theorem c_prec1_ev_pr (hcf:code_prim cf) : code_prim (@c_prec1 m cf) := by
  unfold c_prec1;
  repeat constructor
  simp
  repeat constructor
  exact hcf
  repeat constructor
@[simp] theorem c_prec1_ev : eval_prim O (c_prec1 m cf) = (fun n => n.rec m fun y IH => eval_prim O cf <| Nat.pair y IH) := by simp [c_prec1,eval_prim]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.prec1:Nat.PrimrecIn O Nat.prec1 := by ...
-- theorem Nat.Primrec.prec1:Nat.Primrec Nat.prec1 := by ...
end prec1
section casesOn1
namespace Nat.RecursiveIn.Code
def c_casesOn1 (m) (cf:Code) := @c_prec1 m (cf.comp left)
-- theorem c_casesOn1_ev_pr:code_prim (@c_casesOn1 a b) := by unfold c_casesOn1; repeat constructor;
@[simp] theorem c_casesOn1_ev : eval_prim O (@c_casesOn1 m cf) = (Nat.casesOn · m (eval_prim O cf)) := by simp [c_casesOn1,eval_prim]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.casesOn1:Nat.PrimrecIn O Nat.casesOn1 := by ...
-- theorem Nat.Primrec.casesOn1:Nat.Primrec Nat.casesOn1 := by ...
end casesOn1

section pred
namespace Nat.RecursiveIn.Code
def c_pred := (c_casesOn1 0 c_id)
@[simp] theorem c_pred_ev_pr:code_prim c_pred := by unfold c_pred; repeat constructor
@[simp] theorem c_pred_evp:eval_prim O c_pred = Nat.pred := by
  simp [c_pred,eval_prim]
  funext n;
  cases n <;> simp [*]
@[simp] theorem c_pred_ev:eval O c_pred = Nat.pred := by rw [← eval_prim_eq_eval c_pred_ev_pr]; simp only [c_pred_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.pred:Nat.PrimrecIn O Nat.pred := by ...
-- theorem Nat.Primrec.pred:Nat.Primrec Nat.pred := by ...
end pred
section sub
namespace Nat.RecursiveIn.Code
def c_sub := prec c_id ((c_pred.comp right).comp right)
@[simp] theorem c_sub_ev_pr:code_prim c_sub := by unfold c_sub; repeat constructor
@[simp] theorem c_sub_evp:eval_prim O c_sub = unpaired Nat.sub := by
  simp [c_sub,eval_prim]
  funext n;
  simp [unpaired]
  induction (unpair n).2 with
  | zero => exact rfl
  | succ n h =>
    simp [*, Nat.sub_add_eq];
@[simp] theorem c_sub_ev:eval O c_sub = unpaired Nat.sub := by rw [← eval_prim_eq_eval c_sub_ev_pr]; simp only [c_sub_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.sub:Nat.PrimrecIn O Nat.sub := by ...
-- theorem Nat.Primrec.sub:Nat.Primrec Nat.sub := by ...
end sub
section dist
namespace Nat.RecursiveIn.Code
def c_dist := c_add.comp (pair c_sub (c_sub.comp (pair right left)))
@[simp] theorem c_dist_ev_pr:code_prim c_dist := by unfold c_dist; repeat constructor
@[simp] theorem c_dist_evp:eval_prim O c_dist = unpaired Nat.dist := by simp [c_dist,eval_prim]; exact rfl
@[simp] theorem c_dist_ev:eval O c_dist = unpaired Nat.dist := by rw [← eval_prim_eq_eval c_dist_ev_pr]; simp only [c_dist_evp]
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.dist:Nat.PrimrecIn O Nat.dist := by ...
-- theorem Nat.Primrec.dist:Nat.Primrec Nat.dist := by ...
end dist
@[simp] theorem eq_zero_iff_dist_zero {a b:ℕ} : a.dist b = 0 ↔ a=b := by
  constructor
  · exact fun a_1 ↦ Nat.eq_of_dist_eq_zero a_1
  · exact fun a_1 ↦ Nat.dist_eq_zero a_1
theorem sgdist_eq_ifeq {a b:ℕ} : (if a.dist b = 0 then 0 else 1) = (if a=b then 0 else 1) := by
  simp only [eq_zero_iff_dist_zero]

section if_eq'
namespace Nat.RecursiveIn.Code
def c_if_eq' := c_sg.comp c_dist
@[simp] theorem c_if_eq'_ev_pr:code_prim c_if_eq' := by unfold c_if_eq'; repeat constructor
@[simp] theorem c_if_eq'_evp:eval_prim O c_if_eq' = fun ab => if ab.l=ab.r then 0 else 1 := by simp [c_if_eq',eval_prim];
@[simp] theorem c_if_eq'_ev:eval O c_if_eq' = fun ab => if ab.l=ab.r then 0 else 1 := by rw [← eval_prim_eq_eval c_if_eq'_ev_pr]; simp only [c_if_eq'_evp]; simp; funext xs; exact apply_ite Part.some ((unpair xs).1 = (unpair xs).2) 0 1
end Nat.RecursiveIn.Code
-- theorem Nat.PrimrecIn.if_eq':Nat.PrimrecIn O Nat.if_eq' := by ...
-- theorem Nat.Primrec.if_eq':Nat.Primrec Nat.if_eq' := by ...
end if_eq'





/-- Given a total choice function `c`, returns `a` or `b` conditioning on whether `c x=0`. -/
theorem Nat.RecursiveIn.ifz1 {O:ℕ→ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c): Nat.RecursiveIn O (fun x => if (c x=0) then (a:ℕ) else (b:ℕ):ℕ→ℕ) := by
  let construction := fun x =>
    Nat.add
    (Nat.mul b (Nat.sg (c x)))
    (Nat.mul a (Nat.sg' (c x)))
  have consRecin:Nat.RecursiveIn O construction := by
    simp only [construction]
    apply Nat.RecursiveIn.totalComp₂
    · apply of_primrec Nat.Primrec.add
    · apply Nat.RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const b)
      · apply Nat.RecursiveIn.totalComp'
        · exact of_primrec Nat.Primrec.sg
        · exact hc
    · apply Nat.RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const a)
      · apply Nat.RecursiveIn.totalComp'
        · exact of_primrec Nat.Primrec.sg'
        · exact hc
  have consEq: (fun x => if (c x=0) then (a:ℕ) else (b:ℕ):ℕ→ℕ) = construction := by
    simp [construction]
    funext xs
    cases Classical.em (c xs = 0) with -- do i really need classical.em here?
      | inl h => simp [h]
      | inr h => simp [h]

  rw [consEq]
  exact consRecin





theorem Primrec.projection {f:α → β → σ} {a:α} (h:Primrec₂ f):Primrec (f a) := by
  refine Primrec₂.comp h ?_ ?_
  · exact const a
  · exact Primrec.id
lemma Nat.Primrec.pair_proj:Nat.Primrec (Nat.pair x) := by
  refine Primrec.nat_iff.mp ?_
  apply Primrec.projection
  exact Primrec₂.natPair




theorem Nat.RecursiveIn.ite {O:ℕ→ℕ} {f g:ℕ→.ℕ} {c:ℕ→ℕ} (hc:Nat.RecursiveIn O c) (hf:Nat.RecursiveIn O f) (hg:Nat.RecursiveIn O g):Nat.RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
    have exists_index_for_f:∃ c:ℕ, eval O c = f := by exact exists_code_nat.mp hf
    have exists_index_for_g:∃ c:ℕ, eval O c = g := by exact exists_code_nat.mp hg
    rcases exists_index_for_f with ⟨index_f,index_f_is_f⟩
    rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

    have main2:(fun a => if (c a=0) then (f a) else (g a)) = fun a => Nat.pair (if c a=0 then (index_f) else (index_g)) a >>= eval₁ O := by
      funext xs
      cases Classical.em (c xs = 0) with
      | inl h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval₁, Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_f_is_f)) xs
      | inr h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval₁, Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_g_is_g)) xs
    rw [main2]


    apply Nat.RecursiveIn.evalRecInO'
    apply Nat.RecursiveIn.someTotal

    rw [Nat.RecursiveIn.pair']

    apply Nat.RecursiveIn.pair
    · simp only [Part.coe_some]
      apply Nat.RecursiveIn.ifz1
      exact hc
    exact id

-- for code_ifeq



/--`[code_if_eval_eq c](x)=0 if x.1=x.2 else 1`-/
def code_if_eq:ℕ→ℕ := fun x => 0
theorem code_if_eq_prop:eval O (code_if_eq e) ab = if (Nat.succ ab.l.r=eval O e (Nat.pair ab.l.l ab.r)) then 0 else 1 := by sorry
