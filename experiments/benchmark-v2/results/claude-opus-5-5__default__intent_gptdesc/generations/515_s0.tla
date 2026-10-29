------------------------------ MODULE AlternatingBitExchange ------------------------------
(***************************************************************************)
(* Two processes A and B exchange messages over unreliable FIFO channels   *)
(* (alternating bit protocol). Each process holds a single message value   *)
(* of the form <<data, bit>>. Channels may lose messages arbitrarily, and  *)
(* no two processes update atomically together. The protocol coordinates  *)
(* agreement using the parity (alternating) bit.                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data            \* The fixed set of possible message data values

ASSUME Data # {}

Bits == {0, 1}
Msgs == Data \X Bits     \* The set of all valid full messages

VARIABLES
    AVar,   \* Process A's local message value <<data, bit>>
    BVar,   \* Process B's local message value <<data, bit>>
    AtoB,   \* Unreliable channel from A to B (carries full messages)
    BtoA    \* Unreliable channel from B to A (carries acknowledgment bits)

vars == <<AVar, BVar, AtoB, BtoA>>

---------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq(Bits)

\* Whenever the two processes show the same bit, the full messages agree.
BitImpliesEqual == (AVar[2] = BVar[2]) => (AVar = BVar)

Inv == TypeOK /\ BitImpliesEqual

---------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

---------------------------------------------------------------------------
(* Actions *)

\* A (re)sends its current message on the unreliable channel.
ASnd ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

\* A receives an acknowledgment bit. If it acknowledges A's current bit,
\* A nondeterministically chooses a new message and flips its bit.
ARcv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar[2]
         THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<BVar, AtoB>>

\* B (re)sends an acknowledgment carrying its current bit.
BSnd ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, AtoB>>

\* B receives a message. If it carries a new bit, B adopts the message.
BRcv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB)[2] # BVar[2]
         THEN BVar' = Head(AtoB)
         ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA>>

\* Remove the i-th element of a sequence.
Remove(i, seq) == [j \in 1..(Len(seq) - 1) |->
                      IF j < i THEN seq[j] ELSE seq[j + 1]]

\* The channels are unreliable: any message in transit may be lost.
LoseMsg ==
    /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
          /\ BtoA' = BtoA
       \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
          /\ AtoB' = AtoB
    /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

---------------------------------------------------------------------------
(* Fairness: senders keep retransmitting; receivers that are repeatedly   *)
(* enabled (despite losses) must eventually receive.                       *)

Fairness ==
    /\ WF_vars(ASnd)
    /\ WF_vars(BSnd)
    /\ SF_vars(ARcv)
    /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Liveness properties *)

\* Infinitely often equal and infinitely often unequal.
InfinitelyOftenEqual   == []<>(AVar = BVar)
InfinitelyOftenUnequal == []<>(AVar # BVar)
Alternation == InfinitelyOftenEqual /\ InfinitelyOftenUnequal

\* From an unequal state, equality is eventually reached.
EventuallyEqual == (AVar # BVar) ~> (AVar = BVar)

---------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ BitImpliesEqual)
THEOREM Spec => Alternation /\ EventuallyEqual
===========================================================================================