---------------------------- MODULE ABEnvironment ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

ConstData == {"d1", "d2"}

QueueBound == 2

VARIABLES AVar, BVar, msgQ

vars == <<AVar, BVar, msgQ>>

Message == Data \X {0, 1}

-----------------------------------------------------------------------------
ABESpec_TypeOK ==
    /\ AVar \in Message
    /\ BVar \in Message
    /\ msgQ \in Seq(Data)

Init ==
    /\ \E d \in Data : /\ AVar = <<d, 1>>
                       /\ BVar = AVar
    /\ msgQ = << >>

\* Environment proposes a new value; it is buffered in the queue
Propose(d) ==
    /\ Len(msgQ) < QueueBound
    /\ msgQ' = Append(msgQ, d)
    /\ UNCHANGED <<AVar, BVar>>

\* Sender accepts the next proposed value and flips its bit.
\* It may do so even before the receiver has synchronized, which can
\* break Consistency when proposals are accepted faster than B syncs.
AAccept ==
    /\ msgQ /= << >>
    /\ AVar' = <<Head(msgQ), 1 - AVar[2]>>
    /\ msgQ' = Tail(msgQ)
    /\ UNCHANGED BVar

\* Receiver synchronizes with the sender when their bits differ
BSync ==
    /\ AVar[2] /= BVar[2]
    /\ BVar' = AVar
    /\ UNCHANGED <<AVar, msgQ>>

Next ==
    \/ \E d \in Data : Propose(d)
    \/ AAccept
    \/ BSync

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E d \in Data : Propose(d))
    /\ WF_vars(AAccept)
    /\ WF_vars(BSync)

-----------------------------------------------------------------------------
StateConstraint == Len(msgQ) <= QueueBound

Consistency ==
    (AVar[2] = BVar[2]) => (AVar[1] = BVar[1])

EventualSync ==
    \A b \in {0, 1} :
        (AVar[2] = b /\ BVar[2] /= b) ~> (BVar[2] = b)

ProgressSynced == []<>(AVar[2] = BVar[2])

ProgressUnsynced == []<>(AVar[2] /= BVar[2])

Liveness == EventualSync /\ ProgressSynced /\ ProgressUnsynced

THEOREM Spec => []ABESpec_TypeOK
=============================================================================