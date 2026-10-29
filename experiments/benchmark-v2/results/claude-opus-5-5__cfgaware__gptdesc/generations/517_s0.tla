---------------------------- MODULE MC_Session11b ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

-----------------------------------------------------------------------------
(* Concrete finite data set used for model checking *)
ConstData == {"d1", "d2"}

(* Bound the channels to keep the state space finite *)
StateConstraint == /\ Len(AtoB) <= 3
                   /\ Len(BtoA) <= 3

-----------------------------------------------------------------------------
(* Alternating bit protocol with lossy FIFO channels (Session11b) *)

Messages == Data \X {0, 1}

RemoveAt(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BtoA, BVar>>

ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<AtoB, BVar>>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* High-level specification (Session11a) used as a property *)

ABS_Init == /\ AVar \in Data \X {1}
            /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         /\ BVar' = BVar

ABS_B == /\ AVar # BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABS_Next == ABS_A \/ ABS_B

ABSpecProperty == ABS_Init /\ [][ABS_Next]_<<AVar, BVar>>

-----------------------------------------------------------------------------
(* State predicates *)

AB_TypeOK == /\ AVar \in Messages
             /\ BVar \in Messages
             /\ AtoB \in Seq(Messages)
             /\ BtoA \in Seq({0, 1})

IsTwoValSeq(s) ==
    \E k \in 0..Len(s) :
        \A j \in 1..Len(s) : s[j] = IF j <= k THEN s[1] ELSE s[Len(s)]

AB_TwoValsSeq == /\ IsTwoValSeq(AtoB)
                 /\ IsTwoValSeq(BtoA)

AB_Inv == /\ AB_TypeOK
          /\ (AVar[2] = BVar[2]) => (AVar = BVar)
          /\ \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}
          /\ AB_TwoValsSeq
=============================================================================