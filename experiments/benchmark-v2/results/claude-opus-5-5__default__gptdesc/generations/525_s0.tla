---------------------------- MODULE MCSession11projspec ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the alternating-bit style specification       *)
(* Session11projspec.  The underlying module declares (at least):           *)
(*   CONSTANT  Data                                                         *)
(*   VARIABLES AVar, BVar, NewValQueue, ...                                 *)
(*   Init, Next, Spec                                                       *)
(* where AVar and BVar are pairs <<value, bit>> with value \in Data and     *)
(* bit \in {0,1}, and NewValQueue is a sequence of new values proposed by   *)
(* an active environment and later accepted by process A.                   *)
(***************************************************************************)
EXTENDS Session11projspec, Naturals, Sequences

(***************************************************************************)
(* Concrete model values used to instantiate the constant Data.            *)
(***************************************************************************)
CONSTANTS d1, d2

const_Data == {d1, d2}

(***************************************************************************)
(* Bound on the environment queue so that the state space is finite.       *)
(***************************************************************************)
MaxQueueLen == 2

StateConstraint == Len(NewValQueue) <= MaxQueueLen

(***************************************************************************)
(* Derived predicates relating AVar and BVar.                              *)
(***************************************************************************)
Equal   == AVar = BVar
Unequal == AVar # BVar

SameBit == AVar[2] = BVar[2]

(***************************************************************************)
(* The invariant one might expect for an alternating-bit protocol:         *)
(* whenever A and B agree on the bit, they agree on the value too, and if  *)
(* they disagree on the bit, B is merely one step behind.                  *)
(*                                                                         *)
(* This can FAIL in this model: the environment may propose new values too *)
(* quickly and A may accept them too quickly, so A's bit alternates twice  *)
(* (returning to B's bit) before B has received the intermediate update.   *)
(* Then the bits agree while the values differ.                            *)
(***************************************************************************)
ExpectedInv == SameBit => Equal

(***************************************************************************)
(* A weaker safety-style predicate: values and bits are well-typed.        *)
(***************************************************************************)
PairTypeOK ==
    /\ AVar \in Data \X {0, 1}
    /\ BVar \in Data \X {0, 1}

(***************************************************************************)
(* Liveness properties.                                                    *)
(***************************************************************************)
\* Infinitely often A and B agree.
RecurEqual   == []<>Equal

\* Infinitely often A and B disagree (the environment keeps proposing).
RecurUnequal == []<>Unequal

\* Whenever A and B disagree, they eventually converge to agreement.
Converges    == Unequal ~> Equal

\* The specification checked by the model checker.
MCSpec == Spec

THEOREM MCSpec => [](PairTypeOK)
=============================================================================