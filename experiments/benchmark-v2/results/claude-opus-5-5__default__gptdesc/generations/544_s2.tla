---------------------------- MODULE SemaphoreIncrement ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NPositive == N \in Nat \ {0}

VARIABLES x, sem, pc, t

vars == << x, sem, pc, t >>

ProcSet == 1..N

Init == /\ x = 0
        /\ sem = 1
        /\ t = [self \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> "lock"]

lock(self) == /\ pc[self] = "lock"
              /\ sem = 1
              /\ sem' = 0
              /\ pc' = [pc EXCEPT ![self] = "p1"]
              /\ UNCHANGED << x, t >>

p1(self) == /\ pc[self] = "p1"
            /\ t' = [t EXCEPT ![self] = x]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << x, sem >>

p2(self) == /\ pc[self] = "p2"
            /\ x' = t[self] + 1
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ UNCHANGED << sem, t >>

unlock(self) == /\ pc[self] = "unlock"
                /\ sem' = 1
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << x, t >>

proc(self) == lock(self) \/ p1(self) \/ p2(self) \/ unlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet : proc(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(proc(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

==================================================================================