--------------------------- MODULE MCSession11projimpl ---------------------------
(***************************************************************************)
(* Model-checking module for the alternating-bit style session             *)
(* implementation.  The definitions of the implementation (normally        *)
(* obtained by extending Session11projimpl) and of the abstract session    *)
(* specification (normally instantiated from Session11projspec) are        *)
(* written inline so that this module is self-contained.                   *)
(*                                                                         *)
(* It adds concrete bounds, a state constraint on the lengths of the       *)
(* queues AtoB, BtoA and NewValQueue, a type-correctness predicate, an     *)
(* invariant relating A and B, the helper predicate TwoValsSeq, and the    *)
(* abstract specification property.                                        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Data

ASSUME Data # {}

VARIABLES AVar,        \* A's current value and bit
          BVar,        \* B's current value and bit
          AtoB,        \* message queue from A to B
          BtoA,        \* acknowledgment queue from B to A
          NewValQueue  \* values proposed by the environment, not yet taken by A

vars == <<AVar, BVar, AtoB, BtoA, NewValQueue>>

(***************************************************************************)
(* Concrete bounds used for model checking.                                *)
(***************************************************************************)
MaxAtoBLen   == 3
MaxBtoALen   == 3
MaxNewValLen == 2

Bits == {0, 1}
Msgs == [val : Data, bit : Bits]

-----------------------------------------------------------------------------
(***************************************************************************)
(* The implementation.                                                     *)
(***************************************************************************)
Init ==
  /\ \E d \in Data : AVar = [val |-> d, bit |-> 0]
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

\* A receives an acknowledgment.  If it acknowledges A's current bit and
\* a new value is available, A takes the new value and flips its bit.
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ IF Head(BtoA) = AVar.bit /\ NewValQueue # << >>
       THEN /\ AVar' = [val |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
            /\ NewValQueue' = Tail(NewValQueue)
       ELSE UNCHANGED <<AVar, NewValQueue>>
  /\ UNCHANGED <<BVar, AtoB>>

\* B (re)sends an acknowledgment of its current bit.
BSnd ==
  /\ BtoA' = Append(BtoA, BVar.bit)
  /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue>>

\* B receives a message; if it carries a new bit, B adopts it.
BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ IF Head(AtoB).bit # BVar.bit
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ UNCHANGED <<AVar, BtoA, NewValQueue>>

RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

\* Messages on either channel may be lost.
LoseMsg ==
  /\ \/ /\ AtoB # << >>
        /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
        /\ UNCHANGED BtoA
     \/ /\ BtoA # << >>
        /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
        /\ UNCHANGED AtoB
  /\ UNCHANGED <<AVar, BVar, NewValQueue>>

Next == EnvPropose \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(ASnd) /\ WF_vars(BSnd)
        /\ WF_vars(ARcv) /\ WF_vars(BRcv)

-----------------------------------------------------------------------------
(***************************************************************************)
(* State constraint bounding the lengths of the queues.                    *)
(***************************************************************************)
StateConstraint ==
  /\ Len(AtoB) <= MaxAtoBLen
  /\ Len(BtoA) <= MaxBtoALen
  /\ Len(NewValQueue) <= MaxNewValLen

(***************************************************************************)
(* Type correctness of the implementation state.                           *)
(***************************************************************************)
TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq(Bits)
  /\ NewValQueue \in Seq(Data)

(***************************************************************************)
(* When B holds an acknowledgment bit matching AVar.bit, B should hold     *)
(* A's current value.  This invariant may FAIL when the environment        *)
(* proposes values too quickly: stale acknowledgments still in BtoA can    *)
(* cause A to flip its bit twice before B receives the intermediate        *)
(* value, so B's bit matches AVar.bit while its value is out of date.      *)
(***************************************************************************)
Inv == (BVar.bit = AVar.bit) => (BVar = AVar)

(***************************************************************************)
(* TwoValsSeq(s) asserts that s consists of a (possibly empty) block of    *)
(* equal elements followed by a (possibly empty) block of equal elements   *)
(* all different from the first block -- i.e., s contains at most two     *)
(* values, arranged in two contiguous runs.                                *)
(***************************************************************************)
TwoValsSeq(s) ==
  \E j \in 0..Len(s) :
     /\ \A i \in 1..j : s[i] = s[1]
     /\ \A i, k \in (j + 1)..Len(s) : s[i] = s[k]
     /\ \A i \in (j + 1)..Len(s) : j > 0 => s[i] # s[1]

ChannelInv ==
  /\ TwoValsSeq([i \in 1..Len(AtoB) |-> AtoB[i].bit])
  /\ TwoValsSeq(BtoA)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The abstract session specification (Session11projspec), under the      *)
(* refinement mapping that projects the implementation onto A's and B's    *)
(* current values.  B is either up to date with A, or one step behind, in  *)
(* which case B catches up before A may move on.                           *)
(***************************************************************************)
AbsInit == AVar = BVar /\ AVar \in Msgs

AbsNext ==
  \/ /\ AVar = BVar
     /\ AVar' \in Msgs
     /\ AVar'.bit = 1 - AVar.bit
     /\ BVar' = BVar
  \/ /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

SessionSpec == AbsInit /\ [][AbsNext]_<<AVar, BVar>>

THEOREM Spec => [](TypeOK)
THEOREM Spec => SessionSpec
=============================================================================