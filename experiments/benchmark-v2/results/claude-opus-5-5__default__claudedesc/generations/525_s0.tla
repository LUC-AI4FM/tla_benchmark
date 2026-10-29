--------------------------- MODULE ABESpec ---------------------------
(***************************************************************************)
(* A variant of the Alternating Bit Protocol with an environment that      *)
(* proposes new data values through a queue. This module is self-contained *)
(* and inlines the definitions of the base spec Session11projspec.         *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data   \* e.g. instantiated with {d1, d2, d3} as model values

VARIABLES AVar, BVar, NewValQueue

vars == << AVar, BVar, NewValQueue >>

Bits == {0, 1}

Messages == [data : Data, bit : Bits]

---------------------------------------------------------------------------
(* Base specification (Session11projspec)                                  *)
---------------------------------------------------------------------------

Init ==
    /\ AVar \in Messages
    /\ BVar = AVar
    /\ NewValQueue = << >>

\* The environment proposes a new data value.
EnvPropose ==
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED << AVar, BVar >>

\* A takes the next value from the queue once B has acknowledged
\* the current one (bits match), flipping the bit.
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

Next == EnvPropose \/ A \/ B

Fairness == WF_vars(A) /\ WF_vars(B)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* ABESpec model-checking definitions                                      *)
---------------------------------------------------------------------------

\* State constraint: keep the queue at most three elements long.
QueueConstraint == Len(NewValQueue) <= 3

ABESpec_TypeOK ==
    /\ AVar \in Messages
    /\ BVar \in Messages
    /\ NewValQueue \in Seq(Data)

\* NOT CHECKED: when the bits match, the full variables should be equal.
\* Note: may be violated when the environment proposes values faster
\* than B can synchronize.
ABESpec_Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

\* NOT CHECKED: the variables become equal and unequal infinitely often.
InfinitelyAlternating ==
    /\ []<>(AVar = BVar)
    /\ []<>(AVar # BVar)

\* NOT CHECKED: disagreement eventually leads to agreement.
Liveness == (AVar # BVar) ~> (AVar = BVar)

\* Only the type invariant is checked.
THEOREM Spec => []ABESpec_TypeOK
=============================================================================