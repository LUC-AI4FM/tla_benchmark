---------------------------- MODULE OperatorArgStateMachine ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

ElemX == 1
ElemY == 2

(* Diagnostic message emitted at model setup time *)
ASSUME Print("Setting up OperatorArgStateMachine model", TRUE)

(* User-defined postfix and prefix operator-like constructs *)
a ^# == {a}
-. a == 0 - a

PostfixWrap(a) == a ^#
PrefixWrap(a)  == -. a

(* Operator abstraction: operators passed as first-class parameters *)
ApplyBin(Op(_, _), a, b) == Op(a, b)
ApplyUn(Op(_), a)         == Op(a)

MyUnion(a, b) == a \cup b
Dom(f)        == DOMAIN f

ASSUME ApplyBin(\cup, {1}, {2}) = {1, 2}
ASSUME ApplyBin(\cap, {1, 2}, {2, 3}) = {2}
ASSUME ApplyBin(\, {1, 2}, {2}) = {1}
ASSUME ApplyBin(\in, 1, {1, 2})
ASSUME ApplyBin(\subseteq, {1}, {1, 2})
ASSUME ApplyBin(MyUnion, {3}, {4}) = {3, 4}
ASSUME ApplyUn(SUBSET, {1}) = {{}, {1}}
ASSUME ApplyUn(UNION, {{1}, {2}}) = {1, 2}
ASSUME ApplyUn(Dom, [i \in {1, 2} |-> i]) = {1, 2}
ASSUME ApplyUn(PostfixWrap, 5) = {5}
ASSUME ApplyUn(PrefixWrap, 3) = 0 - 3
ASSUME Print(<<"Operator argument checks passed", ApplyBin(\cup, {1}, {2})>>, TRUE)

Init == /\ x = {ElemX}
        /\ y = {ElemY}

Next == /\ x' = ApplyBin(\cup, x, {ElemX})
        /\ y' = ApplyBin(\cup, y, {ElemY})

Spec == Init /\ [][Next]_vars

(* Invariant: some action is enabled in every reachable state *)
Inv == ENABLED Next

(* Safety: x is unchanged and the primed value of a state expression equals the unprimed one *)
StepFact == /\ UNCHANGED x
            /\ (y \cup {ElemY})' = y \cup {ElemY}

Property == [][StepFact]_vars

THEOREM Spec => []Inv
THEOREM Spec => Property
=========================================================================================