------------------------------ MODULE AlternatingBit ------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar,   \* sender's current message: <<data, bit>>
          BVar,   \* receiver's last accepted message: <<data, bit>>
          AtoB,   \* channel from sender to receiver (messages)
          BtoA    \* channel from receiver to sender (ack bits)

vars == <<AVar, BVar, AtoB, BtoA>>

ConstData == {"d1", "d2"}

-----------------------------------------------------------------------------
(* Helper operators *)

Remove(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

TwoValsSeq(s) ==
    \E i \in 0..Len(s) :
        \A j \in 1..Len(s) :
            s[j] = IF j <= i THEN s[1] ELSE s[Len(s)]

-----------------------------------------------------------------------------
(* Protocol *)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

\* Sender (re)transmits its current message
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, BtoA>>

\* Sender receives an ack; advances if the ack carries its current bit
ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<BVar, AtoB>>

\* Receiver (re)sends ack carrying the bit of the last accepted message
BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

\* Receiver receives a message; accepts it only if it carries the expected bit
BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

\* The channels may lose messages
LoseMsg == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
              /\ UNCHANGED <<AVar, BVar, BtoA>>
           \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
              /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ SF_vars(ARcv) /\ SF_vars(BRcv)
                 /\ WF_vars(ASnd) /\ WF_vars(BSnd)

-----------------------------------------------------------------------------
(* Correctness properties *)

AB_TypeOK == /\ AVar \in Data \X {0, 1}
             /\ BVar \in Data \X {0, 1}
             /\ AtoB \in Seq(Data \X {0, 1})
             /\ BtoA \in Seq({0, 1})

AB_Inv == /\ (\E i \in 1..Len(BtoA) : BtoA[i] = AVar[2]) => (BVar = AVar)
          /\ (BVar[2] = AVar[2]) => (BVar = AVar)

AB_TwoValsSeq == /\ TwoValsSeq(AtoB)
                 /\ TwoValsSeq(BtoA)

StateConstraint == /\ Len(AtoB) <= 3
                   /\ Len(BtoA) <= 3

-----------------------------------------------------------------------------
(* High-level specification: reliable transfer from sender to receiver *)

ABS_Init == /\ AVar \in Data \X {1}
            /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         /\ BVar' = BVar

ABS_B == /\ AVar # BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABS_Next == ABS_A \/ ABS_B

ABS_Spec == ABS_Init /\ [][ABS_Next]_<<AVar, BVar>>

ABSpecProperty == ABS_Spec

=============================================================================