---------------------------- MODULE AlternatingBit ----------------------------
(***************************************************************************)
(* The Alternating Bit Protocol.  A sender (process A) transmits data to   *)
(* a receiver (process B) over two unidirectional, lossy FIFO channels:    *)
(* AtoB carries data messages and BtoA carries acknowledgments.  A         *)
(* separate process, LoseMsgs, models message loss by nondeterministically *)
(* removing any message from either channel.                               *)
(*                                                                         *)
(* Liveness is explicitly omitted: Spec has no fairness conditions, so it  *)
(* specifies only safety.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar,   \* Sender's current message: << data, bit >>
          BVar,   \* Receiver's last accepted message: << data, bit >>
          AtoB,   \* Channel from A to B (sequence of messages)
          BtoA    \* Channel from B to A (sequence of bits)

vars == << AVar, BVar, AtoB, BtoA >>

Bits == {0, 1}

Messages == Data \X Bits

TypeOK ==
  /\ AVar \in Messages
  /\ BVar \in Messages
  /\ AtoB \in Seq(Messages)
  /\ BtoA \in Seq(Bits)

(***************************************************************************)
(* Remove the i-th element of sequence s.                                  *)
(***************************************************************************)
RemoveIth(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>

(***************************************************************************)
(* Process A                                                               *)
(***************************************************************************)
ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED << AVar, BVar, BtoA >>

ARcv ==
  /\ BtoA # << >>
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = << d, 1 - AVar[2] >>
       ELSE AVar' = AVar
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED << BVar, AtoB >>

A == ASnd \/ ARcv

(***************************************************************************)
(* Process B                                                               *)
(***************************************************************************)
BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED << AVar, BVar, AtoB >>

BRcv ==
  /\ AtoB # << >>
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE BVar' = BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED << AVar, BtoA >>

B == BSnd \/ BRcv

(***************************************************************************)
(* Message loss                                                            *)
(***************************************************************************)
LoseMsgs ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
        /\ AtoB' = AtoB
  /\ UNCHANGED << AVar, BVar >>

-----------------------------------------------------------------------------

Next == A \/ B \/ LoseMsgs

(***************************************************************************)
(* No fairness conditions: liveness properties are omitted.                *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK
=============================================================================