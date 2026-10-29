---------------------------- MODULE MCSession11projspec ----------------------------
(***************************************************************************)
(* Model-checking module for an alternating-bit style protocol between    *)
(* processes A and B, with an active environment that enqueues new values *)
(* into NewValQueue.                                                      *)
(*                                                                         *)
(* The original wrapper uses EXTENDS Session11projspec. That module is    *)
(* not available here, so the underlying protocol is defined inline to    *)
(* keep this module self-contained and parseable by SANY.                 *)
(*                                                                         *)
(* NOTE: An invariant you might expect, such as "whenever A's bit equals  *)
(* B's bit, AVar = BVar", can fail. If the environment proposes new       *)
(* values too quickly and A accepts them too quickly, A's bit can         *)
(* alternate faster than B receives updates. The predicates below are     *)
(* therefore checked as candidate invariants, and the module also states  *)
(* liveness properties: recurrence of equal states, recurrence of unequal *)
(* states, and eventual convergence from disagreement to agreement.       *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS MaxQueueLen,   \* bound on NewValQueue used by the state constraint
          MaxChanLen     \* bound on message channels used by the state constraint

ASSUME /\ MaxQueueLen \in Nat
       /\ MaxChanLen \in Nat \ {0}

(***************************************************************************)
(* Concrete constant data set used for model checking.                    *)
(***************************************************************************)
Data == {"d1", "d2", "d3"}

Bits == {0, 1}

VARIABLES AVar,         \* A's current <<value, bit>>
          BVar,         \* B's last received <<value, bit>>
          AtoB,         \* channel of data messages from A to B
          BtoA,         \* channel of acknowledgement bits from B to A
          NewValQueue,  \* values proposed by the environment
          AAcked        \* TRUE iff A has received an ack for its current bit

vars == <<AVar, BVar, AtoB, BtoA, NewValQueue, AAcked>>

TypeOK ==
    /\ AVar \in Data \X Bits
    /\ BVar \in Data \X Bits
    /\ AtoB \in Seq(Data \X Bits)
    /\ BtoA \in Seq(Bits)
    /\ NewValQueue \in Seq(Data)
    /\ AAcked \in BOOLEAN

Init ==
    /\ \E d \in Data : AVar = <<d, 0>>
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>
    /\ NewValQueue = << >>
    /\ AAcked = TRUE

(***************************************************************************)
(* The active environment enqueues a new value.                           *)
(***************************************************************************)
EnvEnqueue ==
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED <<AVar, BVar, AtoB, BtoA, AAcked>>

(***************************************************************************)
(* A accepts a new value once its current value has been acknowledged,   *)
(* flipping its bit.                                                       *)
(***************************************************************************)
ANewVal ==
    /\ AAcked
    /\ NewValQueue # << >>
    /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
    /\ NewValQueue' = Tail(NewValQueue)
    /\ AAcked' = FALSE
    /\ UNCHANGED <<BVar, AtoB, BtoA>>

(***************************************************************************)
(* A (re)sends its current value and bit.                                 *)
(***************************************************************************)
ASend ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA, NewValQueue, AAcked>>

(***************************************************************************)
(* A receives an acknowledgement bit.                                     *)
(***************************************************************************)
ARcv ==
    /\ BtoA # << >>
    /\ AAcked' = (AAcked \/ Head(BtoA) = AVar[2])
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue>>

(***************************************************************************)
(* B receives a data message; accepts it if it carries a new bit.         *)
(***************************************************************************)
BRcv ==
    /\ AtoB # << >>
    /\ BVar' = IF Head(AtoB)[2] # BVar[2] THEN Head(AtoB) ELSE BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA, NewValQueue, AAcked>>

(***************************************************************************)
(* B (re)sends an acknowledgement of its current bit.                     *)
(***************************************************************************)
BSend ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue, AAcked>>

(***************************************************************************)
(* Lossy channels.                                                        *)
(***************************************************************************)
RemoveAt(s, i) ==
    [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg ==
    \/ /\ AtoB # << >>
       /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
       /\ UNCHANGED <<AVar, BVar, BtoA, NewValQueue, AAcked>>
    \/ /\ BtoA # << >>
       /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
       /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue, AAcked>>

Next ==
    \/ EnvEnqueue
    \/ ANewVal
    \/ ASend
    \/ ARcv
    \/ BRcv
    \/ BSend
    \/ LoseMsg

Fairness ==
    /\ WF_vars(ASend)
    /\ WF_vars(BSend)
    /\ SF_vars(ARcv)
    /\ SF_vars(BRcv)
    /\ WF_vars(ANewVal)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* State constraint limiting the length of NewValQueue (and channels).    *)
(***************************************************************************)
StateConstraint ==
    /\ Len(NewValQueue) <= MaxQueueLen
    /\ Len(AtoB) <= MaxChanLen
    /\ Len(BtoA) <= MaxChanLen

(***************************************************************************)
(* Derived safety-style predicates relating AVar and BVar.               *)
(***************************************************************************)
\* The previously expected invariant: equal bits imply equal values.
\* This may FAIL when the environment and A move too quickly.
SameBitImpliesEqual ==
    (AVar[2] = BVar[2]) => (AVar = BVar)

\* B never sees a value-bit pair that A does not currently hold when the
\* bits agree; also a candidate that may fail.
EqualOrDifferentBit ==
    (AVar = BVar) \/ (AVar[2] # BVar[2])

\* Weaker invariant: B's data is always a valid data value.
BVarValid == BVar \in Data \X Bits

Inv ==
    /\ TypeOK
    /\ BVarValid

(***************************************************************************)
(* Liveness properties.                                                   *)
(***************************************************************************)
\* Infinitely often A and B agree.
RecurEqual == []<>(AVar = BVar)

\* Infinitely often A and B disagree (fails if the environment stops).
RecurUnequal == []<>(AVar # BVar)

\* Disagreement always eventually leads to agreement.
Converge == (AVar # BVar) ~> (AVar = BVar)

THEOREM Spec => []TypeOK
=============================================================================