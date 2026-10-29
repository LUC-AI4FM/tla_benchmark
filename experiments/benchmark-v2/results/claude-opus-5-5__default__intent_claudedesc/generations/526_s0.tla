------------------------------- MODULE ABSpec -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar,       \* sender state: <<data, bit>>
          BVar,       \* receiver state: <<data, bit>>
          queue,      \* pending input values not yet taken by the sender
          inputs,     \* history: every value the environment has supplied (ghost)
          delivered   \* history: every value the receiver has accepted (ghost)

vars == <<AVar, BVar, queue, inputs, delivered>>

Bits == {0, 1}

-----------------------------------------------------------------------------
TypeOK ==
    /\ AVar \in Data \X Bits
    /\ BVar \in Data \X Bits
    /\ queue \in Seq(Data)
    /\ inputs \in Seq(Data)
    /\ delivered \in Seq(Data)

-----------------------------------------------------------------------------
Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ queue = << >>
    /\ inputs = << >>
    /\ delivered = << >>

\* The environment supplies a new value. It may do so only when sender and
\* receiver are synchronized (the previous transfer has completed).
EnvInput ==
    /\ AVar = BVar
    /\ \E d \in Data :
         /\ queue' = Append(queue, d)
         /\ inputs' = Append(inputs, d)
    /\ UNCHANGED <<AVar, BVar, delivered>>

\* The sender takes the next queued value and toggles its bit.
Send ==
    /\ AVar = BVar
    /\ queue # << >>
    /\ AVar' = <<Head(queue), 1 - AVar[2]>>
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<BVar, inputs, delivered>>

\* The receiver accepts the sender's value when it sees the bit has changed.
Rcv ==
    /\ AVar # BVar
    /\ BVar' = AVar
    /\ delivered' = Append(delivered, AVar[1])
    /\ UNCHANGED <<AVar, queue, inputs>>

Next == EnvInput \/ Send \/ Rcv

Spec == Init /\ [][Next]_vars

\* Sender and receiver are weakly fair; the environment is not.
FairSpec == Spec /\ WF_vars(Send) /\ WF_vars(Rcv)

-----------------------------------------------------------------------------
\* Safety properties

IsPrefix(s, t) ==
    /\ Len(s) =< Len(t)
    /\ \A i \in 1..Len(s) : s[i] = t[i]

\* Values are received in the order in which they were supplied, with no
\* loss, duplication, or corruption.
InOrderDelivery == IsPrefix(delivered, inputs)

\* Every supplied value is accounted for: delivered, in flight, or queued.
Conservation ==
    inputs = delivered
             \o (IF AVar # BVar THEN <<AVar[1]>> ELSE << >>)
             \o queue

\* When synchronized, sender and receiver agree on the data value.
\* The bits differ only while a transfer is in progress.
BitAlternation ==
    \/ AVar = BVar
    \/ AVar[2] = 1 - BVar[2]

Invariants == TypeOK /\ InOrderDelivery /\ Conservation /\ BitAlternation

-----------------------------------------------------------------------------
\* Liveness properties (under FairSpec)

\* Every in-progress transfer eventually completes.
TransferCompletes == (AVar # BVar) ~> (AVar = BVar)

\* Pending queued data is eventually taken up by the sender.
QueueProcessed == (queue # << >>) ~> (AVar # BVar)

\* Every value supplied by the environment is eventually delivered.
EventualDelivery ==
    \A n \in Nat : (Len(inputs) >= n) ~> (Len(delivered) >= n)

THEOREM FairSpec => [](Invariants)
THEOREM FairSpec => TransferCompletes /\ QueueProcessed /\ EventualDelivery
=============================================================================