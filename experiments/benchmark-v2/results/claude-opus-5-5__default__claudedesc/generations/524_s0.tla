---------------------------- MODULE ABAlg ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue, AtoB, BtoA

vars == << AVar, BVar, NewValQueue, AtoB, BtoA >>

Msgs == [data : Data, bit : {0, 1}]

RemoveElt(i, seq) ==
    [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ NewValQueue \in Seq(Data)
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq({0, 1})

Init ==
    /\ AVar \in [data : Data, bit : {1}]
    /\ BVar = AVar
    /\ NewValQueue = << >>
    /\ AtoB = << >>
    /\ BtoA = << >>

(* Process ASend: repeatedly send the current AVar message to B *)
ASend ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED << AVar, BVar, NewValQueue, BtoA >>

(* Process ARecv: receive acknowledgments from B *)
ARecv ==
    /\ BtoA # << >>
    /\ \/ /\ Head(BtoA) = AVar.bit
          /\ NewValQueue # << >>
          /\ AVar' = [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
          /\ NewValQueue' = Tail(NewValQueue)
       \/ /\ Head(BtoA) # AVar.bit
          /\ UNCHANGED << AVar, NewValQueue >>
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED << BVar, AtoB >>

(* Process BSend: repeatedly send acknowledgment bit to A *)
BSend ==
    /\ BtoA' = Append(BtoA, BVar.bit)
    /\ UNCHANGED << AVar, BVar, NewValQueue, AtoB >>

(* Process BRecv: receive messages from A *)
BRecv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB).bit # BVar.bit
         THEN BVar' = Head(AtoB)
         ELSE UNCHANGED BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED << AVar, NewValQueue, BtoA >>

(* Process LoseMsgs: nondeterministically lose a message from either channel *)
LoseMsgs ==
    \/ /\ AtoB # << >>
       /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
       /\ UNCHANGED << AVar, BVar, NewValQueue, BtoA >>
    \/ /\ BtoA # << >>
       /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
       /\ UNCHANGED << AVar, BVar, NewValQueue, AtoB >>

(* Process E: environment enqueues new data when A and B are synchronized *)
E ==
    /\ AVar = BVar
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

Next ==
    \/ ASend
    \/ ARecv
    \/ BSend
    \/ BRecv
    \/ LoseMsgs
    \/ E

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ASend)
    /\ WF_vars(BSend)
    /\ SF_vars(ARecv)
    /\ SF_vars(BRecv)

=============================================================================