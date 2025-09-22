
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
def c_evconst (ex:ℕ) : ℕ := comp ex.unpair.1 (Code.const ex.unpair.2)
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
-- theorem exists_code_nat {O:ℕ → ℕ} {f:ℕ →. ℕ} : Nat.RecursiveIn O f ↔ ∃ c:ℕ , eval O c = f := by
--   rw [@exists_code O f]
--   exact Function.Surjective.exists decodeCode_sur
-- theorem exists_code_total {O:ℕ → ℕ} {f:ℕ → ℕ} : Nat.RecursiveIn O f ↔ ∃ c , eval O c = f ∧ code_total O c := by
--   constructor
--   ·
--     intro h
--     rcases exists_code.mp h with ⟨c,hc⟩
--     use c
--     constructor
--     exact hc
--     intro x
--     rw [hc]
--     exact trivial
--   intro h
--   rcases h with ⟨c,hc,_⟩
--   apply exists_code.mpr ⟨c,hc⟩

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
