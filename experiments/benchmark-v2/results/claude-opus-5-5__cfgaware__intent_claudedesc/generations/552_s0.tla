------------------------------ MODULE OneBitMutex ------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 0..(N-1)

VARIABLES x, unchecked, other, pc

vars == << x, unchecked, other, pc >>

TypeOK ==
    /\ x \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ other \in [Procs -> Procs]
    /\ pc \in [Procs -> {"ncs", "enter", "e2", "e3", "e4", "e5", "cs", "exit"}]

Init ==
    /\ x = [i \in Procs |-> FALSE]
    /\ unchecked = [i \in Procs |-> {}]
    /\ other \in [Procs -> Procs]
    /\ pc = [i \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED << x, unchecked, other >>

enter(self) ==
    /\ pc[self] = "enter"
    /\ x' = [x EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED other

e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ other' = [other EXCEPT ![self] = i]
                /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                /\ pc' = [pc EXCEPT ![self] = "e3"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED << unchecked, other >>
    /\ UNCHANGED x

e3(self) ==
    /\ pc[self] = "e3"
    /\ IF x[other[self]]
         THEN IF self > other[self]
                THEN /\ x' = [x EXCEPT ![self] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "e4"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "e5"]
                     /\ UNCHANGED x
         ELSE /\ pc' = [pc EXCEPT ![self] = "e2"]
              /\ UNCHANGED x
    /\ UNCHANGED << unchecked, other >>

e4(self) ==
    /\ pc[self] = "e4"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED << x, unchecked, other >>

e5(self) ==
    /\ pc[self] = "e5"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << x, unchecked, other >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << x, unchecked, other >>

exit(self) ==
    /\ pc[self] = "exit"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << unchecked, other >>

P(self) == ncs(self) \/ enter(self) \/ e2(self) \/ e3(self)
              \/ e4(self) \/ e5(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : P(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ P(self))

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

StarvationFree ==
    \A i \in Procs : (pc[i] = "enter") ~> (pc[i] = "cs")

=============================================================================