---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANTS M, N

ASSUME ConstantAssumption == /\ M \in Nat
                             /\ N \in Nat
                             /\ M >= 1
                             /\ N >= M

Procs1 == 1..M
Procs2 == (M+1)..N
Procs == Procs1 \cup Procs2

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ pc = [i \in Procs |-> "ncs"]

\* Actions for processes in Procs1 (1..M)

ncs1(self) == /\ self \in Procs1
              /\ pc[self] = "ncs"
              /\ pc' = [pc EXCEPT ![self] = "start1"]
              /\ UNCHANGED <<x, y, b>>

start1(self) == /\ self \in Procs1
                /\ pc[self] = "start1"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx1"]
                /\ UNCHANGED <<x, y>>

setx1(self) == /\ self \in Procs1
               /\ pc[self] = "setx1"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checky1"]
               /\ UNCHANGED <<y, b>>

checky1(self) == /\ self \in Procs1
                 /\ pc[self] = "checky1"
                 /\ IF y # 0
                    THEN pc' = [pc EXCEPT ![self] = "slowpath1"]
                    ELSE pc' = [pc EXCEPT ![self] = "sety1"]
                 /\ UNCHANGED <<x, y, b>>

slowpath1(self) == /\ self \in Procs1
                   /\ pc[self] = "slowpath1"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "waitfory1"]
                   /\ UNCHANGED <<x, y>>

waitfory1(self) == /\ self \in Procs1
                   /\ pc[self] = "waitfory1"
                   /\ IF y = 0
                      THEN pc' = [pc EXCEPT ![self] = "start1"]
                      ELSE pc' = [pc EXCEPT ![self] = "waitforb1"]
                   /\ UNCHANGED <<x, y, b>>

waitforb1(self) == /\ self \in Procs1
                   /\ pc[self] = "waitforb1"
                   /\ IF b[y] = FALSE
                      THEN pc' = [pc EXCEPT ![self] = "start1"]
                      ELSE pc' = [pc EXCEPT ![self] = "waitforb1"]
                   /\ UNCHANGED <<x, y, b>>

sety1(self) == /\ self \in Procs1
               /\ pc[self] = "sety1"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx1"]
               /\ UNCHANGED <<x, b>>

checkx1(self) == /\ self \in Procs1
                 /\ pc[self] = "checkx1"
                 /\ IF x # self
                    THEN pc' = [pc EXCEPT ![self] = "resetb1"]
                    ELSE pc' = [pc EXCEPT ![self] = "cs"]
                 /\ UNCHANGED <<x, y, b>>

resetb1(self) == /\ self \in Procs1
                 /\ pc[self] = "resetb1"
                 /\ b' = [b EXCEPT ![self] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "waitforall1"]
                 /\ UNCHANGED <<x, y>>

waitforall1(self) == /\ self \in Procs1
                     /\ pc[self] = "waitforall1"
                     /\ IF \A j \in Procs \ {self} : b[j] = FALSE
                        THEN pc' = [pc EXCEPT ![self] = "checkyagain1"]
                        ELSE pc' = [pc EXCEPT ![self] = "waitforall1"]
                     /\ UNCHANGED <<x, y, b>>

checkyagain1(self) == /\ self \in Procs1
                      /\ pc[self] = "checkyagain1"
                      /\ IF y = self
                         THEN pc' = [pc EXCEPT ![self] = "cs"]
                         ELSE pc' = [pc EXCEPT ![self] = "start1"]
                      /\ UNCHANGED <<x, y, b>>

cs1(self) == /\ self \in Procs1
             /\ pc[self] = "cs"
             /\ pc' = [pc EXCEPT ![self] = "exit1"]
             /\ UNCHANGED <<x, y, b>>

exit1(self) == /\ self \in Procs1
               /\ pc[self] = "exit1"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED x

\* Actions for processes in Procs2 (M+1..N)

ncs2(self) == /\ self \in Procs2
              /\ pc[self] = "ncs"
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED <<x, y, b>>

start2(self) == /\ self \in Procs2
                /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "setx2"]
                /\ UNCHANGED <<x, y>>

setx2(self) == /\ self \in Procs2
               /\ pc[self] = "setx2"
               /\ x' = self
               /\ pc' = [pc EXCEPT ![self] = "checky2"]
               /\ UNCHANGED <<y, b>>

checky2(self) == /\ self \in Procs2
                 /\ pc[self] = "checky2"
                 /\ IF y # 0
                    THEN pc' = [pc EXCEPT ![self] = "slowpath2"]
                    ELSE pc' = [pc EXCEPT ![self] = "sety2"]
                 /\ UNCHANGED <<x, y, b>>

slowpath2(self) == /\ self \in Procs2
                   /\ pc[self] = "slowpath2"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "waitfory2"]
                   /\ UNCHANGED <<x, y>>

waitfory2(self) == /\ self \in Procs2
                   /\ pc[self] = "waitfory2"
                   /\ IF y = 0
                      THEN pc' = [pc EXCEPT ![self] = "start2"]
                      ELSE pc' = [pc EXCEPT ![self] = "waitforb2"]
                   /\ UNCHANGED <<x, y, b>>

waitforb2(self) == /\ self \in Procs2
                   /\ pc[self] = "waitforb2"
                   /\ IF b[y] = FALSE
                      THEN pc' = [pc EXCEPT ![self] = "start2"]
                      ELSE pc' = [pc EXCEPT ![self] = "waitforb2"]
                   /\ UNCHANGED <<x, y, b>>

sety2(self) == /\ self \in Procs2
               /\ pc[self] = "sety2"
               /\ y' = self
               /\ pc' = [pc EXCEPT ![self] = "checkx2"]
               /\ UNCHANGED <<x, b>>

checkx2(self) == /\ self \in Procs2
                 /\ pc[self] = "checkx2"
                 /\ IF x # self
                    THEN pc' = [pc EXCEPT ![self] = "resetb2"]
                    ELSE pc' = [pc EXCEPT ![self] = "cs"]
                 /\ UNCHANGED <<x, y, b>>

resetb2(self) == /\ self \in Procs2
                 /\ pc[self] = "resetb2"
                 /\ b' = [b EXCEPT ![self] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "waitforall2"]
                 /\ UNCHANGED <<x, y>>

waitforall2(self) == /\ self \in Procs2
                     /\ pc[self] = "waitforall2"
                     /\ IF \A j \in Procs \ {self} : b[j] = FALSE
                        THEN pc' = [pc EXCEPT ![self] = "checkyagain2"]
                        ELSE pc' = [pc EXCEPT ![self] = "waitforall2"]
                     /\ UNCHANGED <<x, y, b>>

checkyagain2(self) == /\ self \in Procs2
                      /\ pc[self] = "checkyagain2"
                      /\ IF y = self
                         THEN pc' = [pc EXCEPT ![self] = "cs"]
                         ELSE pc' = [pc EXCEPT ![self] = "start2"]
                      /\ UNCHANGED <<x, y, b>>

cs2(self) == /\ self \in Procs2
             /\ pc[self] = "cs"
             /\ pc' = [pc EXCEPT ![self] = "exit2"]
             /\ UNCHANGED <<x, y, b>>

exit2(self) == /\ self \in Procs2
               /\ pc[self] = "exit2"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED x

\* Per-process actions

proc1(self) == \/ ncs1(self)
               \/ start1(self)
               \/ setx1(self)
               \/ checky1(self)
               \/ slowpath1(self)
               \/ waitfory1(self)
               \/ waitforb1(self)
               \/ sety1(self)
               \/ checkx1(self)
               \/ resetb1(self)
               \/ waitforall1(self)
               \/ checkyagain1(self)
               \/ cs1(self)
               \/ exit1(self)

proc2(self) == \/ ncs2(self)
               \/ start2(self)
               \/ setx2(self)
               \/ checky2(self)
               \/ slowpath2(self)
               \/ waitfory2(self)
               \/ waitforb2(self)
               \/ sety2(self)
               \/ checkx2(self)
               \/ resetb2(self)
               \/ waitforall2(self)
               \/ checkyagain2(self)
               \/ cs2(self)
               \/ exit2(self)

\* Next-state relation

Next == \/ \E self \in Procs1 : proc1(self)
        \/ \E self \in Procs2 : proc2(self)

\* Fairness conditions

Fairness1 == \A self \in Procs1 : WF_vars(proc1(self))
Fairness2 == \A self \in Procs2 : WF_vars(proc2(self))

\* Specification

Spec == Init /\ [][Next]_vars /\ Fairness1 /\ Fairness2

\* Safety invariant: Mutual exclusion

InCS(i) == pc[i] = "cs"

MutualExclusion == \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

\* Type invariant

TypeOK == /\ x \in Procs \cup {0}
          /\ y \in Procs \cup {0}
          /\ b \in [Procs -> BOOLEAN]
          /\ pc \in [Procs -> {"ncs", "start1", "setx1", "checky1", "slowpath1", 
                               "waitfory1", "waitforb1", "sety1", "checkx1", 
                               "resetb1", "waitforall1", "checkyagain1", "cs", 
                               "exit1", "start2", "setx2", "checky2", "slowpath2",
                               "waitfory2", "waitforb2", "sety2", "checkx2",
                               "resetb2", "waitforall2", "checkyagain2", "exit2"}]

\* Liveness property: Some process enters CS infinitely often

Liveness == []<>(\E i \in Procs : InCS(i))

==========================================================================