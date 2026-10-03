---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Procs == 1..N

Locations == {"ncs", "start", "setx", "checkb", "sety", "checkx", 
              "checky", "wait", "cs", "exit1", "exit2"}

TypeOK == /\ x \in Procs \cup {0}
          /\ y \in Procs \cup {0}
          /\ b \in [Procs -> BOOLEAN]
          /\ pc \in [Procs -> Locations]

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ pc = [i \in Procs |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED <<x, y, b>>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "setx"]
               /\ UNCHANGED <<x, y>>

setx(self) == /\ pc[self] = "setx"
              /\ x' = self
              /\ pc' = [pc EXCEPT ![self] = "checkb"]
              /\ UNCHANGED <<y, b>>

checkb(self) == /\ pc[self] = "checkb"
                /\ IF y # 0
                   THEN /\ b' = [b EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = "checky"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
                        /\ b' = b
                /\ UNCHANGED <<x, y>>

sety(self) == /\ pc[self] = "sety"
              /\ y' = self
              /\ pc' = [pc EXCEPT ![self] = "checkx"]
              /\ UNCHANGED <<x, b>>

checkx(self) == /\ pc[self] = "checkx"
                /\ IF x # self
                   THEN /\ b' = [b EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = "wait"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                        /\ b' = b
                /\ UNCHANGED <<x, y>>

wait(self) == /\ pc[self] = "wait"
              /\ \A j \in Procs \ {self} : ~b[j]
              /\ IF y = self
                 THEN pc' = [pc EXCEPT ![self] = "cs"]
                 ELSE pc' = [pc EXCEPT ![self] = "checky"]
              /\ UNCHANGED <<x, y, b>>

checky(self) == /\ pc[self] = "checky"
                /\ IF y = 0
                   THEN pc' = [pc EXCEPT ![self] = "start"]
                   ELSE pc' = [pc EXCEPT ![self] = "checky"]
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

Step(self) == \/ ncs(self)
              \/ start(self)
              \/ setx(self)
              \/ checkb(self)
              \/ sety(self)
              \/ checkx(self)
              \/ wait(self)
              \/ checky(self)
              \/ cs(self)
              \/ exit1(self)
              \/ exit2(self)

Next == \E self \in Procs : Step(self)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

Liveness == \A self \in Procs : pc[self] = "start" ~> pc[self] = "cs"

CondLiveness == (\A self \in Procs : []<><<Step(self)>>_vars) => Liveness

FairActions(self) == /\ WF_vars(start(self))
                     /\ WF_vars(setx(self))
                     /\ WF_vars(checkb(self))
                     /\ WF_vars(sety(self))
                     /\ WF_vars(checkx(self))
                     /\ WF_vars(wait(self))
                     /\ WF_vars(checky(self))
                     /\ WF_vars(exit1(self))
                     /\ WF_vars(exit2(self))

FairSpec == Spec /\ \A self \in Procs : FairActions(self)

==========================================================================