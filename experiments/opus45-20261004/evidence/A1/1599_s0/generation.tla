---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

ProcSet == 1..N

Locs == {"ncs", "start", "setx", "chky", "sety", "chkx", "wait", "cs", "exit1", "exit2"}

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ pc \in [1..N -> Locs]

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED <<x, y, b>>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "setx"]
               /\ UNCHANGED <<x, y>>

setx(self) == /\ pc[self] = "setx"
              /\ x' = self
              /\ pc' = [pc EXCEPT ![self] = "chky"]
              /\ UNCHANGED <<y, b>>

chky(self) == /\ pc[self] = "chky"
              /\ IF y # 0
                 THEN /\ b' = [b EXCEPT ![self] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "wait"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
                      /\ b' = b
              /\ UNCHANGED <<x, y>>

sety(self) == /\ pc[self] = "sety"
              /\ y' = self
              /\ pc' = [pc EXCEPT ![self] = "chkx"]
              /\ UNCHANGED <<x, b>>

chkx(self) == /\ pc[self] = "chkx"
              /\ IF x # self
                 THEN /\ b' = [b EXCEPT ![self] = FALSE]
                      /\ IF \A j \in 1..N : ~b[j]
                         THEN /\ IF y = self
                                 THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "wait"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "wait"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ b' = b
              /\ UNCHANGED <<x, y>>

wait(self) == /\ pc[self] = "wait"
              /\ y = 0
              /\ pc' = [pc EXCEPT ![self] = "start"]
              /\ UNCHANGED <<x, y, b>>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit1"]
            /\ UNCHANGED <<x, y, b>>

exit1(self) == /\ pc[self] = "exit1"
               /\ y' = 0
               /\ pc' = [pc EXCEPT ![self] = "exit2"]
               /\ UNCHANGED <<x, b>>

exit2(self) == /\ pc[self] = "exit2"
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED <<x, y>>

proc(self) == ncs(self) \/ start(self) \/ setx(self) \/ chky(self) 
              \/ sety(self) \/ chkx(self) \/ wait(self) \/ cs(self) 
              \/ exit1(self) \/ exit2(self)

Next == \E self \in ProcSet : proc(self)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

Liveness == \A self \in ProcSet : pc[self] = "start" ~> pc[self] = "cs"

CondLiveness == (\A self \in ProcSet : WF_vars(proc(self))) => Liveness

FairActions(self) == /\ WF_vars(start(self))
                     /\ WF_vars(setx(self))
                     /\ WF_vars(chky(self))
                     /\ WF_vars(sety(self))
                     /\ WF_vars(chkx(self))
                     /\ WF_vars(wait(self))
                     /\ WF_vars(exit1(self))
                     /\ WF_vars(exit2(self))

Fairness == \A self \in ProcSet : FairActions(self)

FairSpec == Spec /\ Fairness

==========================================================================