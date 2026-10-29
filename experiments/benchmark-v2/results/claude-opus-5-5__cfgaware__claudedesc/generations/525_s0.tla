------------------------------ MODULE MCSession11projspec ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue

vars == << AVar, BVar, NewValQueue >>

ConstData == {"d1", "d2", "d3"}

Bits == {0, 1}

Msgs == [data : Data, bit : Bits]

---------------------------------------------------------------------------------------
(* Alternating Bit Protocol with an environment component                            *)

Init ==
    /\ AVar \in Msgs
    /\ AVar.bit = 0
    /\ BVar = AVar
    /\ NewValQueue = << >>

\* The environment proposes a new value by appending it to the queue.
EnvPropose(d) ==
    /\ NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED << AVar, BVar >>

\* A sends a new value once B has acknowledged the previous one (bits agree).
A ==
    /\ AVar.bit = BVar.bit
    /\ NewValQueue # << >>
    /\ AVar' = [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
    /\ NewValQueue' = Tail(NewValQueue)
    /\ UNCHANGED BVar

\* B synchronizes with A when the bits differ.
B ==
    /\ AVar.bit # BVar.bit
    /\ BVar' = AVar
    /\ UNCHANGED << AVar, NewValQueue >>

Next ==
    \/ \E d \in Data : EnvPropose(d)
    \/ A
    \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

---------------------------------------------------------------------------------------
(* Model-checking constraint and properties                                          *)

StateConstraint == Len(NewValQueue) <= 3

ABESpec_TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ NewValQueue \in Seq(Data)

\* ABESpec_Inv: when the bits match, the full variables must be equal.
\* This may be violated if the environment proposes values faster than
\* B can synchronize (not checked).
ABESpec_Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

\* Temporal properties (defined but not checked).
InfinitelyAlternating ==
    /\ []<>(AVar = BVar)
    /\ []<>(AVar # BVar)

Liveness == (AVar # BVar) ~> (AVar = BVar)

=======================================================================================