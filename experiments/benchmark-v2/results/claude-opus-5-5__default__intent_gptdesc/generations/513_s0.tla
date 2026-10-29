---------------------------- MODULE OneBitExchange ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Data

ASSUME DataAssump == Data # {} /\ IsFiniteSet(Data)

Bits     == {0, 1}
Messages == Data \X Bits

VARIABLES
    AVar,   \* sender side's current outgoing message
    BVar,   \* receiver side's current (last accepted) incoming message
    AtoB,   \* lossy, unordered medium from A to B (set of in-flight messages)
    BtoA    \* lossy, unordered medium from B to A (set of in-flight tag bits)

vars == <<AVar, BVar, AtoB, BtoA>>

-----------------------------------------------------------------------------
Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ AtoB = {}
    /\ BtoA = {}

(* A (re)transmits its current outgoing message.                           *)
SendA ==
    /\ AtoB' = {AVar}
    /\ UNCHANGED <<AVar, BVar, BtoA>>

(* B receives some in-flight message (in any order). If it carries a new  *)
(* tag bit, B adopts it; otherwise it is a duplicate and is suppressed.   *)
RcvB ==
    \E m \in AtoB :
        /\ AtoB' = AtoB \ {m}
        /\ BVar' = IF m[2] # BVar[2] THEN m ELSE BVar
        /\ UNCHANGED <<AVar, BtoA>>

(* B (re)transmits an acknowledgement carrying its current tag bit.        *)
SendB ==
    /\ BtoA' = {BVar[2]}
    /\ UNCHANGED <<AVar, BVar, AtoB>>

(* A receives an acknowledgement. If it acknowledges A's current tag, A    *)
(* may replace its outgoing message with any data value and a flipped bit.*)
RcvA ==
    \E b \in BtoA :
        /\ BtoA' = BtoA \ {b}
        /\ IF b = AVar[2]
              THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
              ELSE AVar' = AVar
        /\ UNCHANGED <<BVar, AtoB>>

(* The medium may nondeterministically lose messages.                      *)
LoseAtoB ==
    \E m \in AtoB :
        /\ AtoB' = AtoB \ {m}
        /\ UNCHANGED <<AVar, BVar, BtoA>>

LoseBtoA ==
    \E b \in BtoA :
        /\ BtoA' = BtoA \ {b}
        /\ UNCHANGED <<AVar, BVar, AtoB>>

Next ==
    \/ SendA
    \/ RcvB
    \/ SendB
    \/ RcvA
    \/ LoseAtoB
    \/ LoseBtoA

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ WF_vars(SendA)
    /\ WF_vars(SendB)
    /\ SF_vars(RcvB)
    /\ SF_vars(RcvA)

-----------------------------------------------------------------------------
(* (1) Type safety                                                         *)
TypeOK ==
    /\ AVar \in Messages
    /\ BVar \in Messages
    /\ AtoB \subseteq Messages
    /\ BtoA \subseteq Bits

(* (2) Agreement of tagged messages                                        *)
Agreement ==
    (AVar[2] = BVar[2]) => (AVar = BVar)

(* (3) Safety of data values                                               *)
DataSafety ==
    /\ AVar[1] \in Data
    /\ BVar[1] \in Data
    /\ \A m \in AtoB : m[1] \in Data

Inv == TypeOK /\ Agreement /\ DataSafety

(* Progress: any value A holds is eventually reflected at B despite loss. *)
Progress ==
    \A d \in Data : \A t \in Bits :
        (AVar = <<d, t>>) ~> (BVar = <<d, t>>)

(* A keeps making progress: its tag bit changes infinitely often.          *)
AlternatesForever ==
    \A t \in Bits : []<>(AVar[2] = t)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM FairSpec => Progress
THEOREM FairSpec => AlternatesForever
=============================================================================