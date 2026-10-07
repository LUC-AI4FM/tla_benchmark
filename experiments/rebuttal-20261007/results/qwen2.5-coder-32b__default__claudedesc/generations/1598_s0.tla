------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N >= 1

VARIABLES x, y, b, S

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [p \in 1..N -> FALSE]
    /\ S = [p \in 1..N -> {}]

RaiseFlag ==
    /\ \/\< self \in 1..N >
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self

CheckY ==
    /\ \/\< self \in 1..N >
    /\ IF y # 0 THEN
           /\ b' = [b EXCEPT ![self] = FALSE]
       ELSE
           /\ y' = self

WaitForYZero ==
    /\ \/\< self \in 1..N >
    /\ y # 0
    /\ UNCHANGED <<x, b>>

WriteY ==
    /\ \/\< self \in 1..N >
    /\ y = 0
    /\ y' = self

CheckX ==
    /\ \/\< self \in 1..N >
    /\ x # self
    /\ b' = [b EXCEPT ![self] = FALSE]

WaitForOtherFlags ==
    /\ \/\< self \in 1..N >
    /\ x # self
    /\ LET otherProcesses == (1..N) \ {self}
       IN S' = [S EXCEPT ![self] = otherProcesses]
    /\ \A p \in S[self] : b[p] = FALSE

CheckYAgain ==
    /\ \/\< self \in 1..N >
    /\ x # self
    /\ IF y # self THEN
           /\ UNCHANGED <<x, b>>
       ELSE
           /\ y' = 0
           /\ b' = [b EXCEPT ![self] = FALSE]

EnterCS ==
    /\ \/\< self \in 1..N >
    /\ x = self
    /\ y = self

LeaveCS ==
    /\ \/\< self \in 1..N >
    /\ y = self
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]

Next == 
    RaiseFlag \/ CheckY \/ WaitForYZero \/ WriteY \/ CheckX \/ WaitForOtherFlags \/ CheckYAgain \/ EnterCS \/ LeaveCS

Spec == 
    /\ Init
    /\ [][Next]_<<x, y, b, S>>
    /\ WF_<<x, y, b, S>>[RaiseFlag]
    /\ WF_<<x, y, b, S>>[CheckY]
    /\ WF_<<x, y, b, S>>[WaitForYZero]
    /\ WF_<<x, y, b, S>>[WriteY]
    /\ WF_<<x, y, b, S>>[CheckX]
    /\ WF_<<x, y, b, S>>[WaitForOtherFlags]
    /\ WF_<<x, y, b, S>>[CheckYAgain]
    /\ WF_<<x, y, b, S>>[EnterCS]
    /\ WF_<<x, y, b, S>>[LeaveCS]

Invariant == 
    \A p1, p2 \in 1..N : p1 # p2 => \/ ~b[p1] \/ ~b[p2]

Liveness ==
    <>[](\E p \in 1..N : x = p /\ y = p)

=============================================================================