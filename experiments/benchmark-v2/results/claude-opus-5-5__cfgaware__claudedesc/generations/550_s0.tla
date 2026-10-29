--------------------------- MODULE TurnMutex ---------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0..(N-1)

VARIABLES turn, pc

vars == << turn, pc >>

ProcSet == Procs

Init == /\ turn \in Procs
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED turn

enter(self) == /\ pc[self] = "enter"
               /\ turn = self
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED turn

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED turn

exit(self) == /\ pc[self] = "exit"
              /\ turn' = (turn + 1) % N
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

p(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

TypeOK == /\ turn \in Procs
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================