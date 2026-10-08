------------------------------ MODULE TokenRing ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, K

VARIABLES val

(* Predicate: process i holds the token *)
HoldsToken(i) ==
    IF i = 0 THEN
        val[0] = val[N-1]
    ELSE
        val[i] != val[i-1]

(* At least one process holds the token *)
SomeoneHoldsToken == ∃ i \in 0..N-1 : HoldsToken(i)

(* Exactly one process holds the token *)
ExactlyOneHoldsToken ==
    ∃ i \in 0..N-1 :
        HoldsToken(i) /\ ∀ j \in 0..N-1 : (j /= i) => ~HoldsToken(j)

(* Initial state: all values are zero *)
Init == 
    val \in [0 .. N-1 -> 0 .. K-1] /\
    ∀ i \in 0..N-1 : val[i] = 0

(* Action of process i *)
Action(i) ==
    IF i = 0 THEN
        /\ val[0] = val[N-1]
        /\ val' = [val EXCEPT ![0] = (val[0] + 1) % K]
    ELSE
        /\ val[i] != val[i-1]
        /\ val' = [val EXCEPT ![i] = val[i-1]]

(* One of the processes acts in each step *)
Next == ∃ i \in 0..N-1 : Action(i)

(* Fairness: every process is weakly fair *)
Fairness == ∀ i \in 0..N-1 : WF_vars(Action(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Liveness property: eventually exactly one holds the token and thereafter it remains so *)
EventuallyJustOneHoldsToken == <> (ExactlyOneHoldsToken /\ [](ExactlyOneHoldsToken))

(* Safety invariant: at least one process always holds the token *)
SafetyInvariant == [] SomeoneHoldsToken
===============================================================================