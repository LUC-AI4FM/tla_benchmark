---------------------------- MODULE AlternatingBit ----------------------------
(***************************************************************************)
(* Alternating-bit-style protocol between two endpoints A and B that      *)
(* communicate over lossy, FIFO, unidirectional channels AtoB and BtoA.   *)
(* Every message is a pair <<payload, bit>> with payload \in Data and     *)
(* bit \in {0,1}.  Messages are sent and received atomically; a channel   *)
(* may lose whole messages at any time but never corrupts them.           *)
(*                                                                         *)
(* A is the data source: it repeatedly sends its current <<data, bit>>.   *)
(* B accepts a message only if its bit differs from B's current bit.      *)
(* When it accepts, B stores the payload and flips its bit.               *)
(* Otherwise B treats the message as a duplicate and ignores it.          *)
(* B repeatedly sends back its current <<data, bit>> as acknowledgement.  *)
(* An acknowledgement whose bit equals A's bit tells A that B has caught  *)
(* up.  A then picks a fresh payload and flips its bit.  A ignores any    *)
(* stale acknowledgement, and it never uses B's payload.                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

ASSUME Data # {}

VARIABLES AVar,  \* A's current <<payload, bit>>
          BVar,  \* B's current <<payload, bit>>
          AtoB,  \* lossy FIFO channel from A to B
          BtoA   \* lossy FIFO channel from B to A

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}
Msgs == Data \X Bits

\* Remove the i-th element of sequence s (models loss of a whole message).
RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq(Msgs)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

-----------------------------------------------------------------------------
(* A sends its full payload together with its current bit. *)
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, BtoA>>

(* A receives an acknowledgement.  A matching bit means B accepted A's   *)
(* current message, so A chooses new data and flips its bit.  Any other  *)
(* acknowledgement is stale and is ignored.                               *)
ARcv == /\ BtoA # << >>
        /\ BtoA' = Tail(BtoA)
        /\ IF Head(BtoA)[2] = AVar[2]
              THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
              ELSE AVar' = AVar
        /\ UNCHANGED <<BVar, AtoB>>

(* B sends its full payload together with its current bit. *)
BSnd == /\ BtoA' = Append(BtoA, BVar)
        /\ UNCHANGED <<AVar, BVar, AtoB>>

(* B receives a data message.  B accepts it only if the bit differs from *)
(* B's bit.  When it accepts, B stores the payload and flips its bit.     *)
(* Otherwise the message is a duplicate and its payload is ignored.       *)
BRcv == /\ AtoB # << >>
        /\ AtoB' = Tail(AtoB)
        /\ IF Head(AtoB)[2] # BVar[2]
              THEN BVar' = <<Head(AtoB)[1], 1 - BVar[2]>>
              ELSE BVar' = BVar
        /\ UNCHANGED <<AVar, BtoA>>

(* Nondeterministic loss of any single whole message from a channel. *)
LoseAtoB == /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
            /\ UNCHANGED <<AVar, BVar, BtoA>>

LoseBtoA == /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
            /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == \/ ASnd \/ ARcv
        \/ BSnd \/ BRcv
        \/ LoseAtoB \/ LoseBtoA

Fairness == /\ WF_vars(ASnd)
            /\ WF_vars(BSnd)
            /\ SF_vars(ARcv)
            /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Message atomicity: every queued message is a well-formed, intact pair.
MessageAtomicity == /\ \A i \in 1..Len(AtoB) : AtoB[i] \in Msgs
                    /\ \A i \in 1..Len(BtoA) : BtoA[i] \in Msgs

\* If the bits agree, B holds exactly A's current payload.
Consistency == (AVar[2] = BVar[2]) => (AVar = BVar)

\* Any in-flight message carrying the sender's current bit is an intact
\* copy of the sender's current state.
ChannelConsistency ==
    /\ \A i \in 1..Len(AtoB) : (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)
    /\ \A i \in 1..Len(BtoA) : (BtoA[i][2] = BVar[2]) => (BtoA[i] = BVar)

Inv == TypeOK /\ MessageAtomicity /\ Consistency /\ ChannelConsistency

\* B changes its state only by accepting the head message, and only when
\* that message's bit differs from B's bit.  It then flips its bit.
BAcceptRule ==
    [][ BVar' # BVar =>
          /\ AtoB # << >>
          /\ Head(AtoB)[2] # BVar[2]
          /\ BVar' = <<Head(AtoB)[1], 1 - BVar[2]>> ]_vars

\* A changes its state only after receiving an acknowledgement that
\* matches its bit, and it always flips its bit when it does.
AUpdateRule ==
    [][ AVar' # AVar =>
          /\ BtoA # << >>
          /\ Head(BtoA)[2] = AVar[2]
          /\ AVar'[2] = 1 - AVar[2] ]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Every payload/bit pair that A sends is eventually accepted by B.
Delivery == \A m \in Msgs : (AVar = m) ~> (BVar = m)

\* The protocol keeps making progress: A's bit alternates forever.
Progress == \A b \in Bits : []<>(AVar[2] = b)

\* B keeps accepting new payloads forever.
BProgress == \A b \in Bits : []<>(BVar[2] = b)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => BAcceptRule /\ AUpdateRule
THEOREM Spec => Delivery /\ Progress /\ BProgress
=============================================================================