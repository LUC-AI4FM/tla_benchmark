---------------------------- MODULE MCSession11afair ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a two-party (alternating-bit style) session. *)
(* Sender A holds AVar = <<data, bit>>, receiver B holds BVar.             *)
(* AtoB carries data messages, BtoA carries acknowledgement bits.          *)
(* Messages may be lost. The module supplies concrete constant data, a     *)
(* state constraint bounding the queue lengths, typing and structural      *)
(* invariants, and the high-level fair spec exposed as ABSpecProperty.     *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS d1, d2

\* Concrete constant data for model checking
const_Data == {d1, d2}
Data == const_Data

MaxQueueLen == 3

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

-----------------------------------------------------------------------------
(* Helper operators *)

RemoveIth(s, i) ==
    [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

\* Number of positions where consecutive elements differ
NumChanges(s) ==
    Cardinality({i \in 1..(Len(s) - 1) : s[i] # s[i + 1]})

Cardinality(S) ==
    LET CS[T \in SUBSET S] ==
            IF T = {} THEN 0
            ELSE LET x == CHOOSE y \in T : TRUE
                 IN 1 + CS[T \ {x}]
    IN CS[S]

BitsOf(s) == [i \in 1..Len(s) |-> s[i][2]]

-----------------------------------------------------------------------------
(* Low-level protocol *)

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

ASnd ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

ARcv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar[2]
         THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<BVar, AtoB>>

BSnd ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB)[2] # BVar[2]
         THEN BVar' = Head(AtoB)
         ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA>>

LoseMsg ==
    /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
          /\ BtoA' = BtoA
       \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
          /\ AtoB' = AtoB
    /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ SF_vars(ARcv) /\ SF_vars(BRcv)
    /\ WF_vars(ASnd) /\ WF_vars(BSnd)

-----------------------------------------------------------------------------
(* State constraint for model checking *)

SeqConstraint ==
    /\ Len(AtoB) \leq MaxQueueLen
    /\ Len(BtoA) \leq MaxQueueLen

-----------------------------------------------------------------------------
(* Derived predicates on the communication variables and channels *)

Messages == Data \X {0, 1}

TypeOK ==
    /\ AVar \in Messages
    /\ BVar \in Messages
    /\ AtoB \in Seq(Messages)
    /\ BtoA \in Seq({0, 1})

\* Every message in AtoB carrying A's current bit equals AVar; every
\* message carrying the other bit equals BVar.
AtoBStructure ==
    \A i \in 1..Len(AtoB) :
        IF AtoB[i][2] = AVar[2] THEN AtoB[i] = AVar ELSE AtoB[i] = BVar

\* The bits along each channel (prefixed by the current endpoint value)
\* change at most once.
ChannelBitsMonotone ==
    /\ NumChanges(<<BVar[2]>> \o BitsOf(AtoB) \o <<AVar[2]>>) \leq 1
    /\ NumChanges(<<AVar[2]>> \o BtoA \o <<BVar[2]>>) \leq 1

\* If both parties agree on the bit they agree on the data.
SameBitSameData == (AVar[2] = BVar[2]) => (AVar = BVar)

Inv ==
    /\ TypeOK
    /\ AtoBStructure
    /\ ChannelBitsMonotone
    /\ SameBitSameData

-----------------------------------------------------------------------------
(* High-level fair specification (Session11afair's Spec) over AVar, BVar *)

HInit ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar

HA ==
    /\ AVar = BVar
    /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
    /\ BVar' = BVar

HB ==
    /\ AVar # BVar
    /\ BVar' = AVar
    /\ AVar' = AVar

HNext == HA \/ HB

HSpec == HInit /\ [][HNext]_<<AVar, BVar>> /\ WF_<<AVar, BVar>>(HNext)

ABSpecProperty == HSpec

=============================================================================