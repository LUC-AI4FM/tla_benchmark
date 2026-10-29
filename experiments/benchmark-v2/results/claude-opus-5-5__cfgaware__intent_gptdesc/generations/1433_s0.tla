---- MODULE InitGenerator ----
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Finite domain of candidate values for the single integer state var.     *)
(***************************************************************************)
Domain == 0..4

(***************************************************************************)
(* Abstract syntax of initialization predicates.                           *)
(*   EqVar(k)      :  stateVar = k                                         *)
(*   EqConst(a,b)  :  a = b   (constant equality, tautology/contradiction) *)
(*   TrueF/FalseF  :  constant TRUE / FALSE                                *)
(*   And(f,g), Or(f,g)                                                     *)
(***************************************************************************)
EqVar(k)      == [kind |-> "eqv", k |-> k]
EqConst(a, b) == [kind |-> "eqc", a |-> a, b |-> b]
TrueF         == [kind |-> "true"]
FalseF        == [kind |-> "false"]
And(f, g)     == [kind |-> "and", l |-> f, r |-> g]
Or(f, g)      == [kind |-> "or",  l |-> f, r |-> g]

(***************************************************************************)
(* Semantic evaluation: depends only on the value v, never on the order    *)
(* in which subexpressions are evaluated (pure Boolean semantics).         *)
(***************************************************************************)
RECURSIVE Eval(_, _)
Eval(f, v) ==
    IF f.kind = "eqv" THEN v = f.k
    ELSE IF f.kind = "eqc" THEN f.a = f.b
    ELSE IF f.kind = "true" THEN TRUE
    ELSE IF f.kind = "false" THEN FALSE
    ELSE IF f.kind = "and" THEN (Eval(f.l, v) /\ Eval(f.r, v))
    ELSE (Eval(f.l, v) \/ Eval(f.r, v))

(***************************************************************************)
(* A fixed, finite list of initialization predicates, including           *)
(* tautologies and contradictions.                                         *)
(***************************************************************************)
Preds ==
    << Or(EqVar(1), EqVar(3)),
       And(EqVar(3), EqConst(2, 2)),
       And(EqVar(2), FalseF),
       Or(EqConst(1, 2), EqVar(0)),
       And(Or(EqVar(1), EqVar(4)), Or(EqVar(4), TrueF)),
       And(EqConst(5, 5), EqVar(1)) >>

Satisfies(v) == \E i \in 1..Len(Preds) : Eval(Preds[i], v)

Expected == { v \in Domain : Satisfies(v) }

VARIABLES x,          \* the integer state variable (current candidate)
          produced,   \* set of produced initial states
          out,        \* sequence of produced states, in emission order
          remaining   \* candidate values not yet examined

vars == << x, produced, out, remaining >>

Init ==
    /\ x = 0
    /\ produced = {}
    /\ out = << >>
    /\ remaining = Domain

Examine(v) ==
    /\ v \in remaining
    /\ remaining' = remaining \ {v}
    /\ x' = v
    /\ IF Satisfies(v) /\ v \notin produced
          THEN /\ produced' = produced \cup {v}
               /\ out' = Append(out, v)
          ELSE UNCHANGED << produced, out >>

Done ==
    /\ remaining = {}
    /\ UNCHANGED vars

Next ==
    \/ \E v \in remaining : Examine(v)
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E v \in remaining : Examine(v))

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
    /\ x \in Int
    /\ produced \subseteq Domain
    /\ remaining \subseteq Domain
    /\ out \in Seq(Domain)

Soundness == produced \subseteq Expected

NoDuplicates ==
    \A i, j \in 1..Len(out) : i # j => out[i] # out[j]

OutMatchesSet == { out[i] : i \in 1..Len(out) } = produced

ProgressInvariant == produced = Expected \cap (Domain \ remaining)

FinalCorrectness == (remaining = {}) => (produced = Expected)

Safety ==
    /\ TypeOK
    /\ Soundness
    /\ NoDuplicates
    /\ OutMatchesSet
    /\ ProgressInvariant
    /\ FinalCorrectness

(***************************************************************************)
(* Liveness: every legal value is eventually enumerated.                   *)
(***************************************************************************)
EventuallyAllEnumerated == <>(produced = Expected)

EachEventuallyProduced == \A v \in Expected : <>(v \in produced)

====