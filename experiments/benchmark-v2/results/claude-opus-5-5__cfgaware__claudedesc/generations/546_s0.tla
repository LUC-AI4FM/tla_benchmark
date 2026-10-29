---------------------------- MODULE TurnMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 0 .. (N - 1)

VARIABLES turn, pc

vars == << turn, pc >>

ProcSet == Procs

Init == /\ turn = 0
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

proc(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars

TypeOK == /\ turn \in Procs
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

=============================================================================