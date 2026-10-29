------------------------------- MODULE MCSession11projimpl -------------------------------
(***************************************************************************)
(* Model-checking module for an alternating-bit style session protocol.    *)
(*                                                                         *)
(* The original module extends Session11projimpl and instantiates          *)
(* Session11projspec. This version is self-contained so that it parses     *)
(* without those modules. The implementation (sender A, receiver B, lossy  *)
(* FIFO channels AtoB and BtoA, and the environment's NewValQueue) and the *)
(* abstract specification property are defined inline.                     *)
(*                                                                         *)
(* The module adds:                                                        *)
(*   - concrete constants for the model,                                   *)
(*   - a state constraint that bounds the queue lengths,                   *)
(*   - a type-correctness predicate,                                       *)
(*   - an invariant relating A and B,                                      *)
(*   - the helper predicate TwoValsSeq,                                    *)
(*   - the abstract specification property that the implementation must    *)
(*     satisfy.                                                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Data,        \* The set of values the environment can propose
          MaxQLen      \* Bound on queue lengths, used by the state constraint

ASSUME /\ Data # {}
       /\ MaxQLen \in Nat

(***************************************************************************)
(* Concrete values to substitute for the constants in a TLC model.         *)
(***************************************************************************)
MCData    == {"d1", "d2"}
MCMaxQLen == 2

VARIABLES AVar,         \* Sender state: [val |-> current value, bit |-> 0/1]
          BVar,         \* Receiver state: last value received, with its bit
          AtoB,         \* Lossy FIFO channel of data messages from A to B
          BtoA,         \* Lossy FIFO channel of acknowledgment bits from B to A
          NewValQueue   \* Values proposed by the environment, waiting for A

vars == <<AVar, BVar, AtoB, BtoA, NewValQueue>>

Msg == [val : Data, bit : {0, 1}]

(***************************************************************************)
(* Type correctness of the implementation state.                           *)
(***************************************************************************)
TypeOK ==
  /\ AVar \in Msg
  /\ BVar \in Msg
  /\ AtoB \in Seq(Msg)
  /\ BtoA \in Seq({0, 1})
  /\ NewValQueue \in Seq(Data)

-----------------------------------------------------------------------------
Init ==
  /\ \E d \in Data : /\ AVar = [val |-> d, bit |-> 0]
                     /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ NewValQueue = << >>

\* The environment proposes a new value for A to send.
EnvPropose ==
  /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
  /\ UNCHANGED <<AVar, BVar, AtoB, BtoA>>

\* A (re)sends its current value and bit.
ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA, NewValQueue>>

\* A receives an acknowledgment. If the ack matches A's bit and a new value
\* is waiting, A takes that value and flips its bit. Otherwise the ack is
\* discarded.
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ IF Head(BtoA) = AVar.bit /\ NewValQueue # << >>
       THEN /\ AVar' = [val |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
            /\ NewValQueue' = Tail(NewValQueue)
       ELSE UNCHANGED <<AVar, NewValQueue>>
  /\ UNCHANGED <<BVar, AtoB>>

\* B (re)sends an acknowledgment carrying its current bit.
BSnd ==
  /\ BtoA' = Append(BtoA, BVar.bit)
  /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue>>

\* B receives a data message. It accepts the message only if the bit is new.
BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ IF Head(AtoB).bit # BVar.bit
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ UNCHANGED <<AVar, BtoA, NewValQueue>>

\* Either channel may lose a message.
RemoveElt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg ==
  \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(AtoB, i)
     /\ UNCHANGED <<AVar, BVar, BtoA, NewValQueue>>
  \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(BtoA, i)
     /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue>>

Next == EnvPropose \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(ASnd) /\ WF_vars(BSnd)
                 /\ SF_vars(ARcv) /\ SF_vars(BRcv)

-----------------------------------------------------------------------------
(***************************************************************************)
(* State constraint that limits the length of the message queues.          *)
(***************************************************************************)
SeqConstraint ==
  /\ Len(AtoB) <= MaxQLen
  /\ Len(BtoA) <= MaxQLen
  /\ Len(NewValQueue) <= MaxQLen

(***************************************************************************)
(* When B holds an acknowledgment bit that matches AVar.bit, B has         *)
(* received A's current value, so the two states are equal.                *)
(*                                                                         *)
(* In variants of the protocol where A takes a newly proposed value        *)
(* without waiting for the acknowledgment, this invariant can fail. That   *)
(* happens if the environment proposes values too quickly: A can move to   *)
(* a new value with the same bit before B catches up.                      *)
(***************************************************************************)
Inv == (BVar.bit = AVar.bit) => (BVar = AVar)

(***************************************************************************)
(* TwoValsSeq(s) is true when s contains at most two distinct values, with *)
(* all copies of the first value coming before all copies of the second.   *)
(* In other words, s is a run of x's followed by a run of y's.             *)
(***************************************************************************)
TwoValsSeq(s) ==
  \E i \in 0..Len(s) :
     /\ \A j, k \in 1..i : s[j] = s[k]
     /\ \A j, k \in (i + 1)..Len(s) : s[j] = s[k]

ChannelInv == TwoValsSeq(AtoB) /\ TwoValsSeq(BtoA)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract specification property. This stands in for the instance of    *)
(* Session11projspec. B's value changes only by becoming A's current       *)
(* value. A changes its value only after B has caught up, that is, when    *)
(* B's bit matches A's bit.                                                *)
(***************************************************************************)
AbsNext ==
  \/ /\ BVar' # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar
  \/ /\ AVar' # AVar
     /\ BVar.bit = AVar.bit
     /\ AVar'.bit = 1 - AVar.bit
     /\ BVar' = BVar

SpecProp ==
  /\ (BVar = AVar)
  /\ [][AbsNext]_<<AVar, BVar>>

\* Liveness: under FairSpec, every value A sends is eventually received by B.
Liveness == \A d \in Data, b \in {0, 1} :
              (AVar = [val |-> d, bit |-> b]) ~> (BVar = [val |-> d, bit |-> b])

THEOREM Spec => [](TypeOK /\ Inv /\ ChannelInv)
THEOREM Spec => SpecProp
THEOREM FairSpec => Liveness
=============================================================================