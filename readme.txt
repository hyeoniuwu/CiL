computability in lean

Structure of project:

Oracle.lean
Relativises parts of Mathlib/Computability/Partrec.lean. The two main predicates defined are `PrimrecIn` and `RecursiveIn`, from which we develop the rest of the theory.

Order.lean:
Defines the Turing degrees, but with oracles as total functions.

Encoding.lean:
Defines codes and the specification of `eval` and `evaln`.
Relativised from Mathlib/Computability/PartrecCode.lean.

Label.lean: just for defining a label for the cp (code_prim) attribute

Basic.lean: Helper functions/theorems, notation

Constructions/Primitive.lean: Constructs a plethora of primitive recursive functions.
Constructions/Option.lean: Constructs primitive recursive functions that deal with option types.
Constructions/List.lean: Constructs primitive recursive functions that deal with list types.
Constructions/CovRec.lean: Defines framework for primitive recursive constructions that involve course-of-values recursion.
Constructions/Eval_Aux.lean: Auxiliary constructions for `eval`, mostly to do with rfind.
Constructions/Eval.lean: Construction of `eval`.
Constructions/Basic.lean: Basic code constructions that require `eval`, or are not primitive recursive.

Jump.lean: Defines the jump and basic results, such as K≡K_0.
Rin.lean: Defines theorems in the form "Nat.RecursiveIn f", which are used in SetOracles.lean to prove e.g. K≡K_0.
SetOracles.lean: Sets up sets as oracles, and several basic degree theory results.

Constructions/Dovetail.lean: Construction of the dovetail operator.

Use.lean
Constructions/Use.lean
	Specification and construction of the use function.

EvalString.lean
Constructions/EvalString.lean
	Specification and construction of evaluation with finite strings as oracles.

KP54.lean
Constructions/KP54.lean
	Specification and construction of the KP54 construction procedure, along with a proof of KP54.

Simple.lean
	Specification and construction of simple sets.