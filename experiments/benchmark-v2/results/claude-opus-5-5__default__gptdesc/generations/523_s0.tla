------------------------------ MODULE MCSession11projimpl ------------------------------
(***************************************************************************)
(* Model-checking module for an alternating-bit style session protocol.    *)
(* Sender A transmits values, taken from a queue NewValQueue filled by the *)
(* environment, to receiver B over lossy FIFO channels AtoB and BtoA.      *)
(* The projection variables A and B hold the session-level values of the  *)
(* sender and the receiver.                                                *)
(*                                                                         *)
(* The original module extends Session11projimpl and instantiates          *)
(* Session11projspec. Here the implementation and the abstract spec are    *)
(* written inline so that the module parses on its own.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Data,        \* set of values the environment may propose
          MaxQLen      \* bound on queue lengths, used by the state constraint

ASSUME /\ Data # {}
       /\ MaxQLen \in Nat

(***************************************************************************)
(* Concrete constant values to be substituted for the model.               *)
(***************************************************************************)
MCData    == {"v1", "v2"}
MCMaxQLen == 2

VARIABLES AVar,         \* sender state: [val, bit]
          BVar,         \* receiver state: [val, bit]
          AtoB,         \* data channel from A to B
          BtoA,         \* ack channel from B to A
          NewValQueue,  \* values proposed by the environment, not yet taken by A
          A,            \* session value at the sender (projection)
          B             \* session value at the receiver (projection)

vars == <<AVar, BVar, AtoB, BtoA, NewValQueue, A, B>>

Bits == {0, 1}
Msg  == [val : Data, bit : Bits]

\* Remove the i-th element of sequence s.
RemoveAt(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Implementation (corresponds to Session11projimpl)                       *)
(***************************************************************************)
Init ==
  \E d \in Data :
     /\ AVar = [val |-> d, bit |-> 1]
     /\ BVar = AVar
     /\ AtoB = << >>
     /\ BtoA = << >>
     /\ NewValQueue = << >>
     /\ A = d
     /\ B = d

\* The environment proposes a new value.
EnvPropose ==
  /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
  /\ UNCHANGED <<AVar, BVar, AtoB, BtoA, A, B>>

\* A (re)sends its current message.
ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA, NewValQueue, A, B>>

\* A receives an ack. If the ack matches its bit and a new value is
\* available, it starts sending that value with the flipped bit.
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ IF Head(BtoA) = AVar.bit /\ NewValQueue # << >>
       THEN /\ AVar' = [val |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
            /\ NewValQueue' = Tail(NewValQueue)
            /\ A' = Head(NewValQueue)
       ELSE UNCHANGED <<AVar, NewValQueue, A>>
  /\ UNCHANGED <<BVar, AtoB, B>>

\* B (re)sends an ack carrying its current bit.
BSnd ==
  /\ BtoA' = Append(BtoA, BVar.bit)
  /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue, A, B>>

\* B receives a message. It accepts the message only if the bit is new.
BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ IF Head(AtoB).bit # BVar.bit
       THEN /\ BVar' = Head(AtoB)
            /\ B' = Head(AtoB).val
       ELSE UNCHANGED <<BVar, B>>
  /\ UNCHANGED <<AVar, BtoA, NewValQueue, A>>

\* Either channel may lose a message.
LoseMsg ==
  /\ \/ \E i \in 1..Len(AtoB) :
          /\ AtoB' = RemoveAt(i, AtoB)
          /\ BtoA' = BtoA
     \/ \E i \in 1..Len(BtoA) :
          /\ BtoA' = RemoveAt(i, BtoA)
          /\ AtoB' = AtoB
  /\ UNCHANGED <<AVar, BVar, NewValQueue, A, B>>

Next == EnvPropose \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Fairness ==
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* State constraint: bound the lengths of the queues.                      *)
(***************************************************************************)
StateConstraint ==
  /\ Len(AtoB) <= MaxQLen
  /\ Len(BtoA) <= MaxQLen
  /\ Len(NewValQueue) <= MaxQLen

(***************************************************************************)
(* Type correctness of the implementation state.                           *)
(***************************************************************************)
TypeOK ==
  /\ AVar \in Msg
  /\ BVar \in Msg
  /\ AtoB \in Seq(Msg)
  /\ BtoA \in Seq(Bits)
  /\ NewValQueue \in Seq(Data)
  /\ A \in Data
  /\ B \in Data

(***************************************************************************)
(* When B holds an acknowledgment matching AVar.bit, B has received A's    *)
(* current value. This invariant may fail in variants of the protocol in   *)
(* which the environment proposes values too quickly, i.e. A overwrites    *)
(* its value before B has received the previous one.                       *)
(***************************************************************************)
Inv ==
  (BVar.bit = AVar.bit) => (B = A /\ BVar = AVar)

(***************************************************************************)
(* TwoValsSeq(s): s has at most two distinct values, and they occur as a   *)
(* prefix block followed by a suffix block.                                *)
(***************************************************************************)
TwoValsSeq(s) ==
  \E i \in 0..Len(s) :
     \A j \in 1..Len(s) :
        /\ (j <= i) => (s[j] = s[1])
        /\ (j > i)  => (s[j] = s[Len(s)])

ChannelInv == TwoValsSeq(AtoB) /\ TwoValsSeq(BtoA)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract session specification (corresponds to Session11projspec),      *)
(* written over the projection variables A and B.                          *)
(***************************************************************************)
AbsInit == A \in Data /\ B = A

AbsPropose == /\ A = B
              /\ A' \in Data
              /\ B' = B

AbsDeliver == /\ B' = A
              /\ A' = A

AbsNext == AbsPropose \/ AbsDeliver

AbsSpec == AbsInit /\ [][AbsNext]_<<A, B>>

\* The implementation refines the abstract session spec.
SessionSpecProp == AbsSpec

(***************************************************************************)
(* Liveness: whenever B lags behind A, it eventually catches up.           *)
(***************************************************************************)
Liveness == (BVar.bit # AVar.bit) ~> (BVar.bit = AVar.bit)

THEOREM Spec => [](TypeOK /\ Inv /\ ChannelInv)
THEOREM Spec => SessionSpecProp
=============================================================================