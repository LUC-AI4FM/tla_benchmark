---------------------------- MODULE MCSession11afair ----------------------------
EXTENDS Integers, Sequences

(***************************************************************************)
(* Concrete constant data used for model checking.                         *)
(***************************************************************************)
const_Data == {"d1", "d2"}

Data == const_Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

(***************************************************************************)
(* Helper operators                                                         *)
(***************************************************************************)
Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

\* A sequence of bits that switches value at most once.
AtMostOneSwitch(s) ==
    \A i \in 1..Len(s) : \A j \in i..Len(s) :
        (s[i] # s[j]) => \A k \in j..Len(s) : s[k] = s[j]

\* The bits carried by the messages in AtoB.
AtoBBits == [i \in 1..Len(AtoB) |-> AtoB[i][2]]

(***************************************************************************)
(* The alternating-bit protocol over lossy FIFO channels.                  *)
(***************************************************************************)
TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA >>

ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = << d, 1 - AVar[2] >>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB >>

BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED << AVar, BVar >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(ASnd)
        /\ WF_vars(BSnd)
        /\ SF_vars(ARcv)
        /\ SF_vars(BRcv)

(***************************************************************************)
(* State constraint bounding the channel lengths for model checking.       *)
(***************************************************************************)
SeqConstraint == /\ Len(AtoB) \leq 3
                 /\ Len(BtoA) \leq 3

(***************************************************************************)
(* Derived predicates about the variables and channels.                    *)
(***************************************************************************)
ChannelsTypeOK == /\ AtoB \in Seq(Data \X {0, 1})
                  /\ BtoA \in Seq({0, 1})

AtoBStructure ==
    /\ AtMostOneSwitch(AtoBBits)
    /\ \A i \in 1..Len(AtoB) : (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)

BtoAStructure ==
    /\ AtMostOneSwitch(BtoA)
    /\ (AVar # BVar) => \A i \in 1..Len(BtoA) : BtoA[i] = BVar[2]

Inv == /\ TypeOK
       /\ AtoBStructure
       /\ BtoAStructure

(***************************************************************************)
(* The fair high-level specification (as in Session11afair), whose Spec    *)
(* is exposed as ABSpecProperty.                                            *)
(***************************************************************************)
ABS_Init == /\ AVar \in Data \X {1}
            /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = << d, 1 - AVar[2] >>
         /\ BVar' = BVar

ABS_B == /\ AVar # BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABS_Next == ABS_A \/ ABS_B

ABS_vars == << AVar, BVar >>

ABS_Spec == ABS_Init /\ [][ABS_Next]_ABS_vars /\ WF_ABS_vars(ABS_Next)

ABSpecProperty == ABS_Spec

(***************************************************************************)
(* Liveness: every value sent by A is eventually received by B.            *)
(***************************************************************************)
Liveness == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

THEOREM Spec => []Inv
THEOREM Spec => ABSpecProperty
=============================================================================