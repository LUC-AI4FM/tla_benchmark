----------------------------- MODULE RingTerminationDetection -----------------------------

EXTENDS Naturals, TLC

CONSTANTS
    N,
    MaxMsg

ASSUME N \in Nat \ {0}
ASSUME MaxMsg \in Nat

VARIABLES
    active,   \* [Nodes -> BOOLEAN]
    pending,  \* [Nodes -> 0..MaxMsg]
    token,    \* current token position in ring
    flag      \* TRUE iff termination has been detected

Nodes == 1..N
MsgVals == 0..MaxMsg

NextNode(i) == IF i < N THEN i + 1 ELSE 1

vars == <<active, pending, token, flag>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> MsgVals]
    /\ token \in Nodes
    /\ flag \in BOOLEAN

AllInactive == \A i \in Nodes: ~active[i]
NoPending  == \A i \in Nodes: pending[i] = 0
Terminated == AllInactive /\ NoPending

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [i \in Nodes |-> 0]
    /\ token \in Nodes
    /\ IF AllInactive
          THEN flag \in {FALSE, TRUE}
          ELSE flag = FALSE

Deactivate ==
    \E i \in Nodes:
        /\ active[i]
        /\ active' = [active EXCEPT ![i] = FALSE]
        /\ UNCHANGED <<pending, token, flag>>

Send ==
    \E i \in Nodes:
      \E j \in Nodes:
        /\ i # j
        /\ active[i]
        /\ pending[j] < MaxMsg
        /\ pending' = [pending EXCEPT ![j] = @ + 1]
        /\ UNCHANGED <<active, token, flag>>

Deliver ==
    \E j \in Nodes:
        /\ pending[j] > 0
        /\ pending' = [pending EXCEPT ![j] = @ - 1]
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ UNCHANGED <<token, flag>>

TokenStep ==
    IF Terminated /\ ~flag THEN
        /\ flag' = TRUE
        /\ UNCHANGED <<active, pending, token>>
    ELSE
        /\ token' = NextNode(token)
        /\ UNCHANGED <<active, pending, flag>>

Next == Deactivate \/ Send \/ Deliver \/ TokenStep

Spec == Init /\ [][Next]_vars /\ WF_vars(TokenStep)

Inv == TypeOK

Soundness == [] (flag => Terminated)

Quiescence == [] (Terminated => [] Terminated)

LiveDetect == [] (Terminated => <> flag)

=============================================================================