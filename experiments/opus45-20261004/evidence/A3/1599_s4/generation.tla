---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

ProcSet == 1..N

Locs == {"ncs", "start", "set_x", "set_b_true", "check_y1", "set_y", 
         "check_x", "check_y2", "wait_b", "cs", "exit1", "exit2"}

TypeOK == /\ x \in (0..N)
          /\ y \in (0..N)
          /\ b \in [1..N -> BOOLEAN]
          /\ pc \in [1..N -> Locs]

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "ncs"]

\* Noncritical section - process does nothing, then proceeds to start
ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED <<x, y, b>>

\* Start: set b[self] to TRUE
start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "set_x"]
               /\ UNCHANGED <<x, y>>

\* Set x to self
set_x(self) == /\ pc[self] = "set_x"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "check_y1"]
               /\ UNCHANGED <<y, b>>

\* Check if y /= 0 (first check)
check_y1(self) == /\ pc[self] = "check_y1"
                  /\ IF y /= 0
                     THEN /\ b' = [b EXCEPT ![self] = FALSE]
                          /\ pc' = [pc EXCEPT ![self] = "wait_b"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "set_y"]
                          /\ b' = b
                  /\ UNCHANGED <<x, y>>

\* Set y to self
set_y(self) == /\ pc[self] = "set_y"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "check_x"]
               /\ UNCHANGED <<x, b>>

\* Check if x = self
check_x(self) == /\ pc[self] = "check_x"
                 /\ IF x /= self
                    THEN /\ b' = [b EXCEPT ![self] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = "check_y2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ b' = b
                 /\ UNCHANGED <<x, y>>

\* Check if y = self (second check, slow path)
check_y2(self) == /\ pc[self] = "check_y2"
                  /\ IF y = self
                     THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "wait_b"]
                  /\ UNCHANGED <<x, y, b>>

\* Wait until b[y] is FALSE (splitter loop on slow path)
wait_b(self) == /\ pc[self] = "wait_b"
                /\ IF y /= 0 /\ b[y] = TRUE
                   THEN /\ pc' = pc
                   ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
                /\ UNCHANGED <<x, y, b>>

\* Critical section - process does nothing, then proceeds to exit
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit1"]
            /\ UNCHANGED <<x, y, b>>

\* Exit: set y to 0
exit1(self) == /\ pc[self] = "exit1"
               /\ y' = 0
               /\ pc' = [pc EXCEPT ![self] = "exit2"]
               /\ UNCHANGED <<x, b>>

\* Exit: set b[self] to FALSE and return to ncs
exit2(self) == /\ pc[self] = "exit2"
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED <<x, y>>

\* Combined action for each process
proc(self) == \/ ncs(self)
              \/ start(self)
              \/ set_x(self)
              \/ check_y1(self)
              \/ set_y(self)
              \/ check_x(self)
              \/ check_y2(self)
              \/ wait_b(self)
              \/ cs(self)
              \/ exit1(self)
              \/ exit2(self)

Next == \E self \in ProcSet: proc(self)

\* Basic specification without fairness
Spec == Init /\ [][Next]_vars

\* Fairness conditions - weak fairness for all actions except ncs and cs
FairSpec == Spec /\ \A self \in ProcSet:
                       /\ WF_vars(start(self))
                       /\ WF_vars(set_x(self))
                       /\ WF_vars(check_y1(self))
                       /\ WF_vars(set_y(self))
                       /\ WF_vars(check_x(self))
                       /\ WF_vars(check_y2(self))
                       /\ WF_vars(wait_b(self))
                       /\ WF_vars(exit1(self))
                       /\ WF_vars(exit2(self))

\* Safety invariant: Mutual exclusion - no two distinct processes in CS
MutualExclusion == \A i, j \in ProcSet: 
                      (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Alternative formulation of mutual exclusion
AtMostOneInCS == Cardinality({i \in ProcSet : pc[i] = "cs"}) <= 1

\* A process trying to enter will eventually enter (liveness)
Liveness == \A self \in ProcSet: 
               (pc[self] = "start") ~> (pc[self] = "cs")

\* Conditional liveness: if a process is trying and others eventually leave,
\* it will enter
ConditionalLiveness == \A self \in ProcSet:
                          (pc[self] \in {"start", "set_x", "check_y1", "set_y", 
                                         "check_x", "check_y2", "wait_b"}) 
                          ~> (pc[self] = "cs")

\* Starvation freedom (under fair scheduling)
StarvationFreedom == \A self \in ProcSet: 
                        (pc[self] = "ncs") ~> (pc[self] = "cs")

\* Invariant that y being non-zero implies some process set it
YInvariant == (y /= 0) => (y \in ProcSet)

\* Invariant that x being non-zero implies some process set it  
XInvariant == (x /= 0) => (x \in ProcSet)

==========================================================================