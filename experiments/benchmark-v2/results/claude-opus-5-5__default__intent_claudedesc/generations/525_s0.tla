------------------------------ MODULE ABProposals ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data,          \* set of data values the environment may propose
          QLen,          \* bound on the length of the proposal queue
          RapidAccept    \* TRUE: sender may accept proposals while unsynchronized

ASSUME /\ Data # {}
       /\ QLen \in Nat \ {0}
       /\ RapidAccept \in BOOLEAN

VARIABLES AVar,   \* sender's message  <<data, bit>>
          BVar,   \* receiver's message <<data, bit>>
          queue   \* pending value proposals from the environment

vars == <<AVar, BVar, queue>>

Bits == {0, 1}
Msgs == Data \X Bits

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ queue \in Seq(Data)
          /\ Len(queue) <= QLen

Init == \E d \in Data :
          /\ AVar = <<d, 1>>
          /\ BVar = AVar
          /\ queue = << >>

Synced == AVar[2] = BVar[2]

\* The environment proposes a new value, buffered in the bounded queue.
Propose(d) == /\ Len(queue) < QLen
              /\ queue' = Append(queue, d)
              /\ UNCHANGED <<AVar, BVar>>

\* The sender accepts the oldest proposal and flips its bit.
\* Without RapidAccept, it only does so once the receiver has synchronized.
A == /\ queue # << >>
     /\ RapidAccept \/ Synced
     /\ AVar' = <<Head(queue), 1 - AVar[2]>>
     /\ queue' = Tail(queue)
     /\ UNCHANGED BVar

\* The receiver synchronizes with the sender's current message.
B == /\ ~Synced
     /\ BVar' = AVar
     /\ UNCHANGED <<AVar, queue>>

Next == \/ \E d \in Data : Propose(d)
        \/ A
        \/ B

Fairness == /\ WF_vars(\E d \in Data : Propose(d))
            /\ WF_vars(A)
            /\ SF_vars(B)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety

Inv == (AVar[2] = BVar[2]) => (AVar = BVar)   \* may fail when RapidAccept = TRUE

\* Liveness

EventualSync == ~Synced ~> Synced

ContinuousProgress == []<>Synced /\ []<>~Synced

THEOREM Spec => [](TypeOK)
THEOREM Spec => EventualSync /\ ContinuousProgress
=============================================================================