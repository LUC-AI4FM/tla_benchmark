---------------------------- MODULE GrowingSets ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS A, B

ASSUME ConstAssump == A \in Nat /\ B \in Nat

ASSUME SetupMsg == Print(<<"GrowingSets: model setup with A, B =", A, B>>, TRUE)

VARIABLES x, y

vars == <<x, y>>

TypeOK == /\ x \in SUBSET Nat
          /\ y \in SUBSET Nat

-------------------------------------------------------------------------------
(* User-defined prefix and postfix operators *)

-. S == {} \ S

S ^+ == S \cup {0}

S ^# == S \cap {A, B}

(* Higher-order operators that take operators as first-class parameters *)

ApplyBin(Op(_, _), S, T) == Op(S, T)

ApplyUn(Op(_), S) == Op(S)

ApplyTwice(Op(_), S) == Op(Op(S))

-------------------------------------------------------------------------------
Init == /\ x = {A}
        /\ y = {B}

Next == /\ x' = x \cup {A}
        /\ y' = y \cup {B}

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------------
(* Safety and liveness properties *)

EnabledInv == ENABLED Next

StepFacts == /\ UNCHANGED x
             /\ (x \cup y)' = x \cup y

SafetyProp == [][StepFacts]_vars

NextPreservesStepFacts == Next => StepFacts

GrowthInv == A \in x /\ B \in y

EnabledLiveness == []<>(ENABLED Next)

-------------------------------------------------------------------------------
(* Assertions checking operator application with various operator arguments *)

OperatorChecks ==
  /\ ApplyBin(\cup, x, y) = x \cup y
  /\ ApplyBin(\cap, x, y) = x \cap y
  /\ ApplyBin(\, x, y) = x \ y
  /\ ApplyBin(LAMBDA S, T : S \cup T, x, y) = ApplyBin(\cup, y, x)
  /\ ApplyUn(LAMBDA S : -. S, x) = {}
  /\ ApplyUn(LAMBDA S : S ^+, x) = x \cup {0}
  /\ ApplyUn(LAMBDA S : S ^#, x \cup y) = (x \cup y) \cap {A, B}
  /\ ApplyTwice(LAMBDA S : S ^+, x) = x ^+
  /\ ApplyUn(LAMBDA f : DOMAIN f, [e \in x |-> e]) = x
  /\ ApplyUn(LAMBDA S : SUBSET S, x) = SUBSET x
  /\ ApplyUn(LAMBDA S : UNION {S}, y) = y
  /\ ApplyUn(LAMBDA S : Cardinality(S), x) = 1

-------------------------------------------------------------------------------
THEOREM TypeCorrect == Spec => []TypeOK
THEOREM EnabledAlways == Spec => []EnabledInv
THEOREM Safety == Spec => SafetyProp
THEOREM ActionImplication == Next => StepFacts
THEOREM Growth == Spec => []GrowthInv
THEOREM OpsHold == Spec => []OperatorChecks
THEOREM Liveness == Spec => EnabledLiveness
===============================================================================