------------------------------- MODULE MaxScan -------------------------------
(***************************************************************************)
(* Single-pass scan of a finite, nonempty sequence of natural numbers      *)
(* that computes its maximum.  The candidate starts as a sentinel value    *)
(* that is not a natural number and is smaller than every natural number.  *)
(* At each step the element at the current index is inspected, the         *)
(* candidate is updated if that element is larger, and the index advances. *)
(* The scan terminates when the index reaches Len(Input) + 1, and the      *)
(* candidate is then exposed as the result.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Input

ASSUME InputAssumption ==
    /\ Input \in Seq(Nat)
    /\ Len(Input) > 0

\* The sentinel ("empty") candidate.  It is not in Nat and is smaller than
\* every natural number, so the first inspected element always replaces it.
Sentinel == -1

VARIABLES
    inp,   \* the input sequence (never modified)
    i,     \* index of the next element to inspect
    m      \* current candidate for the maximum

vars == <<inp, i, m>>

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ inp = Input
    /\ i = 1
    /\ m = Sentinel

(* Inspect one element, possibly update the candidate, advance the index. *)
Step ==
    /\ i <= Len(inp)
    /\ m' = IF inp[i] > m THEN inp[i] ELSE m
    /\ i' = i + 1
    /\ UNCHANGED inp

Terminated == i = Len(inp) + 1

(* Once terminated, the system only stutters. *)
Done ==
    /\ Terminated
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(* The computed maximum, exposed upon termination. *)
Result == IF Terminated THEN m ELSE Sentinel

-----------------------------------------------------------------------------
(* Type / domain invariants *)

TypeOK ==
    /\ inp \in Seq(Nat)
    /\ Len(inp) > 0
    /\ inp = Input
    /\ i \in 1..(Len(inp) + 1)
    /\ m \in Nat \cup {Sentinel}

(* Inductive invariant: after inspecting the first i-1 elements, the       *)
(* candidate is at least as large as each of them, it is the sentinel iff  *)
(* nothing has been inspected yet, and otherwise it is one of the          *)
(* inspected elements.                                                     *)
PrefixMax ==
    \A k \in 1..(i - 1) : m >= inp[k]

SentinelIffNoneInspected ==
    (m = Sentinel) <=> (i = 1)

CandidateIsInspected ==
    (i > 1) => \E k \in 1..(i - 1) : m = inp[k]

IndInv ==
    /\ TypeOK
    /\ PrefixMax
    /\ SentinelIffNoneInspected
    /\ CandidateIsInspected

(* Lemmas relating the index at termination to having examined all elements *)
TerminationCoversAll ==
    Terminated => (1..(i - 1) = DOMAIN inp)

NotTerminatedHasNext ==
    ~Terminated => (i \in DOMAIN inp)

(* Postcondition: functional correctness upon termination *)
Postcondition ==
    Terminated =>
        /\ m \in Nat
        /\ \A k \in DOMAIN inp : m >= inp[k]
        /\ \E k \in DOMAIN inp : m = inp[k]
        /\ Result = m

-----------------------------------------------------------------------------
(* Liveness *)

Termination == <>Terminated

StaysTerminated == [](Terminated => []Terminated)

EventuallyCorrect ==
    <>(Terminated /\ \A k \in DOMAIN inp : Result >= inp[k])

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM InitEstablishesInv == Init => IndInv

THEOREM InvInductive == IndInv /\ [Next]_vars => IndInv'

THEOREM InvHolds == Spec => []IndInv

THEOREM LemmaCoverage == Spec => [](TerminationCoversAll /\ NotTerminatedHasNext)

THEOREM Correctness == Spec => []Postcondition

THEOREM Terminates == Spec => Termination

THEOREM TerminationStable == Spec => StaysTerminated

THEOREM TotalCorrectness == Spec => EventuallyCorrect

=============================================================================