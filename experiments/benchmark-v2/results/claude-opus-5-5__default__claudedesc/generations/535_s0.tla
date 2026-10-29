------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Self-contained model-checking configuration for Session5.  The        *)
(* Session5 algorithm is reconstructed here: for a tuple chosen from       *)
(* Tuples, it scans the elements left to right and keeps the largest      *)
(* value seen.  The running maximum starts at the sentinel minValue.       *)
(* The key correctness property is Termination.                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

CONSTANTS minValue, Tuples

(***************************************************************************)
(* Model-checking constant definitions (TLC MC-style overrides).          *)
(* In the TLC configuration file:                                          *)
(*   CONSTANT minValue <- const_minValue                                   *)
(*   CONSTANT Tuples   <- const_Tuples                                     *)
(*   SPECIFICATION Spec                                                    *)
(*   PROPERTY Termination                                                  *)
(***************************************************************************)
const_minValue == -99999

const_Tuples == {<<1, 2, 3>>}

ASSUME minValue \in Int
ASSUME \A t \in Tuples : \A k \in 1..Len(t) : t[k] \in Int /\ t[k] > minValue

VARIABLES tuple, i, max, pc

vars == <<tuple, i, max, pc>>

Init ==
    /\ tuple \in Tuples
    /\ i = 1
    /\ max = minValue
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ IF i <= Len(tuple)
          THEN /\ max' = IF tuple[i] > max THEN tuple[i] ELSE max
               /\ i' = i + 1
               /\ pc' = "Lbl_1"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<i, max>>
    /\ UNCHANGED tuple

\* Allow infinite stuttering in the final state so deadlock is not reported
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ tuple \in Tuples
    /\ i \in 1..(Len(tuple) + 1)
    /\ max \in Int
    /\ pc \in {"Lbl_1", "Done"}

MaxOf(t) == IF Len(t) = 0 THEN minValue
            ELSE CHOOSE m \in {t[k] : k \in 1..Len(t)} :
                     \A k \in 1..Len(t) : t[k] <= m

\* The running max is the maximum of the prefix scanned so far
MaxInvariant ==
    /\ max >= minValue
    /\ \A k \in 1..(i - 1) : tuple[k] <= max
    /\ (i > 1) => \E k \in 1..(i - 1) : tuple[k] = max

\* At termination, max is the maximum element of the tuple
Correctness == (pc = "Done") => (max = MaxOf(tuple))

-------------------------------------------------------------------------------
(* Liveness *)

Termination == <>(pc = "Done")

=============================================================================