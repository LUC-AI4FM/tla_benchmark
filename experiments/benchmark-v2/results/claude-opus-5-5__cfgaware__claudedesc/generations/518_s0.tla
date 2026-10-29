---------------------------- MODULE AB ----------------------------
(***************************************************************************)
(* The Alternating Bit Protocol.  A sender (process A) transmits data to   *)
(* a receiver (process B) over the channel AtoB, and B returns            *)
(* acknowledgments over the channel BtoA.  Both channels may lose          *)
(* messages, which is modeled by the separate process LoseMsgs.            *)
(*                                                                         *)
(* This specification has no fairness conditions.  Liveness properties    *)
(* are therefore omitted and only safety properties can be checked.       *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Msgs == Data \X {0, 1}

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

(***************************************************************************)
(* Remove(i, seq) is seq with its i-th element removed.                    *)
(***************************************************************************)
Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j]
                                                        ELSE seq[j + 1]]

(***************************************************************************)
(* Process A: the sender.                                                  *)
(***************************************************************************)
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, BtoA>>

ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<BVar, AtoB>>

A == ASnd \/ ARcv

(***************************************************************************)
(* Process B: the receiver.                                                *)
(***************************************************************************)
BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

B == BSnd \/ BRcv

(***************************************************************************)
(* Process LoseMsgs: removes an arbitrary message from either channel.     *)
(***************************************************************************)
LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED <<AVar, BVar>>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars

=============================================================================