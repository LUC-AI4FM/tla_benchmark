---------------------------- MODULE Session11projspecMC ----------------------------
(***************************************************************************)
(* Model-checking wrapper for an alternating-bit style protocol between     *)
(* processes A and B, under an active environment that can enqueue new     *)
(* values on NewValQueue.  The underlying protocol is included inline so   *)
(* that this module is self-contained.                                     *)
(*                                                                         *)
(* A previously expected invariant (AVar and BVar never differ by more     *)
(* than one "step") may fail: if the environment proposes new values too   *)
(* quickly and A accepts them too quickly, A's bit can alternate faster    *)
(* than B receives updates.  We therefore examine both safety-style        *)
(* predicates and liveness properties.                                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA, NewValQueue

vars == << AVar, BVar, AtoB, BtoA, NewValQueue >>

-----------------------------------------------------------------------------
(* Concrete data set used for model checking (Data <- ConstData).          *)
ConstData == {"d1", "d2"}

-----------------------------------------------------------------------------
ABESpec_TypeOK ==
    /\ AVar \in Data \X {0, 1}
    /\ BVar \in Data \X {0, 1}
    /\ AtoB \in Seq(Data \X {0, 1})
    /\ BtoA \in Seq({0, 1})
    /\ NewValQueue \in Seq(Data)

Init ==
    /\ AVar \in Data \X {0}
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>
    /\ NewValQueue = << >>

(* The environment proposes a new value. *)
EnvPropose ==
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

(* A (re)sends its current value and bit. *)
ASnd ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED << AVar, BVar, BtoA, NewValQueue >>

(* A receives an acknowledgement bit; if it acknowledges A's current bit   *)
(* and a new value is pending, A accepts it and flips its bit.             *)
ARcv ==
    /\ BtoA # << >>
    /\ BtoA' = Tail(BtoA)
    /\ IF Head(BtoA) = AVar[2] /\ NewValQueue # << >>
          THEN /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
               /\ NewValQueue' = Tail(NewValQueue)
          ELSE UNCHANGED << AVar, NewValQueue >>
    /\ UNCHANGED << BVar, AtoB >>

(* B (re)sends an acknowledgement of its current bit. *)
BSnd ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED << AVar, BVar, AtoB, NewValQueue >>

(* B receives a message; if the bit differs from its own, it is new data. *)
BRcv ==
    /\ AtoB # << >>
    /\ AtoB' = Tail(AtoB)
    /\ IF Head(AtoB)[2] # BVar[2]
          THEN BVar' = Head(AtoB)
          ELSE UNCHANGED BVar
    /\ UNCHANGED << AVar, BtoA, NewValQueue >>

(* Lossy channels. *)
RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg ==
    /\ \/ \E i \in 1..Len(AtoB) :
             /\ AtoB' = RemoveAt(AtoB, i)
             /\ UNCHANGED BtoA
       \/ \E i \in 1..Len(BtoA) :
             /\ BtoA' = RemoveAt(BtoA, i)
             /\ UNCHANGED AtoB
    /\ UNCHANGED << AVar, BVar, NewValQueue >>

Next ==
    \/ EnvPropose
    \/ ASnd
    \/ ARcv
    \/ BSnd
    \/ BRcv
    \/ LoseMsg

Fairness ==
    /\ WF_vars(ASnd)
    /\ WF_vars(BSnd)
    /\ SF_vars(ARcv)
    /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Bound the state space: limit length of NewValQueue (and channels).      *)
StateConstraint ==
    /\ Len(NewValQueue) <= 3
    /\ Len(AtoB) <= 3
    /\ Len(BtoA) <= 3

-----------------------------------------------------------------------------
(* Safety-style predicates.                                                *)

(* Previously expected invariant: whenever bits agree, values agree.       *)
(* This may fail when A alternates its bit twice before B catches up.      *)
SameBitSameVal == (AVar[2] = BVar[2]) => (AVar = BVar)

(* Weaker predicate that holds by construction. *)
BitsWellFormed == AVar[2] \in {0, 1} /\ BVar[2] \in {0, 1}

-----------------------------------------------------------------------------
(* Liveness properties.                                                    *)

(* A and B infinitely often agree. *)
EqualRecurs == []<>(AVar = BVar)

(* A and B infinitely often disagree (not expected in general). *)
UnequalRecurs == []<>(AVar # BVar)

(* Disagreement eventually leads to agreement. *)
Converges == (AVar # BVar) ~> (AVar = BVar)

=============================================================================