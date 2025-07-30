computability in lean

notes:

to register a primrec function, you should:

namespace Nat.RecursiveIn.Code
construct it:
def code_sg := comp (prec zero (((Code.const 1).comp left).comp left)) (pair zero .id) 

show the construction is primitive:
theorem code_sg_prim : code_prim code_sg := by unfold code_sg; repeat constructor

show the construction has some desired behaviour
theorem code_sg_prop : eval_prim O code_sg = Nat.sg := by
  simp [code_sg]
  simp [eval_prim]
  funext n
  induction n with
  | zero => exact rfl
  | succ n _ => simp
end Nat.RecursiveIn.Code

results we want follow:
theorem Nat.PrimrecIn.sg : Nat.PrimrecIn O Nat.sg := by rw [←code_sg_prop]; apply code_prim_prop code_sg_prim
theorem Nat.Primrec.sg : Nat.Primrec Nat.sg := by exact PrimrecIn.PrimrecIn_Empty PrimrecIn.sg
