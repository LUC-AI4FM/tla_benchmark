---- MODULE InPlaceQuicksort ----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES pc, A, S

Init == /\ pc = "qs1"
        /\ A \in [1..N -> 1..N]
        /\ S = {[1,N]}

PivotSelect ==
    \E pivot \in [Fst(HEAD(S))..Lst(HEAD(S))] :
        LET newS == (S \ {HEAD(S)}) \cup
                     IF Fst(HEAD(S)) < pivot-1 THEN {[Fst(HEAD(S)), pivot-1]} ELSE {} \cup
                     IF pivot+1 < Lst(HEAD(S)) THEN {[pivot+1, Lst(HEAD(S))]} ELSE {}
        IN /\ CHOOSE pivot \in [Fst(HEAD(S))..Lst(HEAD(S))]
           /\ S' = newS

Partition ==
    LET pivot == CHOOSE x \in [Fst(HEAD(S))..Lst(HEAD(S))] : TRUE
        permute == PERMUTATIONS([1..N -> 1..N])
        validPermute == {p \in permute :
                           /\ \A i \in Fst(HEAD(S))..pivot-1 : p[i] <= A[pivot]
                           /\ \A i \in pivot+1..Lst(HEAD(S)) : p[i] >= A[pivot]}
    IN  /\ CHOOSE A' \in validPermute : TRUE
        /\ S' = (S \ {HEAD(S)}) \cup
               IF Fst(HEAD(S)) < pivot-1 THEN {[Fst(HEAD(S)), pivot-1]} ELSE {} \cup
               IF pivot+1 < Lst(HEAD(S)) THEN {[pivot+1, Lst(HEAD(S))]} ELSE {}

qs1 ==
    \/ /\ pc = "qs1"
       /\ S /= {}
       /\ PivotSelect
       /\ pc' = "qs1"
    \/ /\ pc = "qs1"
       /\ S = {}
       /\ pc' = "Done"

Next == qs1

Spec == WF_next(SPEC \E pc \in {"qs1", "Done"} : /\ pc = "qs1" => <pc, S> \in [][Next]_<<pc, S>>)
        /\ SpecFair
        /\ \A s \in States : s.pc = "Done" => ~[]<>(s.pc # "Done")

SpecFair == WF_next(SPEC pc = "qs1")

Termination == <>[](pc = "Done")

====