----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Proc == 1..N

VARIABLES x, y, b, pc

Vars == << x, y, b, pc >>

Labels == {"Try","SetX","CheckY","WaitY0","CheckX","WaitAllFalse","CS","Exit2"}

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [p \in Proc |-> FALSE]
  /\ pc = [p \in Proc |-> "Try"]

TypeInv ==
  /\ x \in {0} \cup Proc
  /\ y \in {0} \cup Proc
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> Labels]

NoTwoInCS ==
  \A p \in Proc: \A q \in Proc:
    p # q => ~(pc[p] = "CS" /\ pc[q] = "CS")

MutualExclusion == NoTwoInCS

StepPid(p) ==
  /\ p \in Proc
  /\ \/
     /\ pc[p] = "Try"
     /\ b' = [b EXCEPT ![p] = TRUE]
     /\ pc' = [pc EXCEPT ![p] = "SetX"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[p] = "SetX"
     /\ x' = p
     /\ pc' = [pc EXCEPT ![p] = "CheckY"]
     /\ UNCHANGED << y, b >>
  \/ /\ pc[p] = "CheckY" /\ y # 0
     /\ b' = [b EXCEPT ![p] = FALSE]
     /\ pc' = [pc EXCEPT ![p] = "WaitY0"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[p] = "CheckY" /\ y = 0
     /\ y' = p
     /\ pc' = [pc EXCEPT ![p] = "CheckX"]
     /\ UNCHANGED << x, b >>
  \/ /\ pc[p] = "CheckX" /\ x # p
     /\ b' = [b EXCEPT ![p] = FALSE]
     /\ pc' = [pc EXCEPT ![p] = "WaitAllFalse"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[p] = "CheckX" /\ x = p
     /\ pc' = [pc EXCEPT ![p] = "CS"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[p] = "WaitAllFalse"
     /\ (\A j \in Proc \ {p}: b[j] = FALSE)
     /\ \/
        /\ y = p
        /\ pc' = [pc EXCEPT ![p] = "CS"]
     \/ /\ y # p
        /\ pc' = [pc EXCEPT ![p] = "WaitY0"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[p] = "WaitY0" /\ y = 0
     /\ pc' = [pc EXCEPT ![p] = "Try"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[p] = "CS"
     /\ y' = 0
     /\ pc' = [pc EXCEPT ![p] = "Exit2"]
     /\ UNCHANGED << x, b >>
  \/ /\ pc[p] = "Exit2"
     /\ b' = [b EXCEPT ![p] = FALSE]
     /\ pc' = [pc EXCEPT ![p] = "Try"]
     /\ UNCHANGED << x, y >>

Step1 == StepPid(1)

StepRest(p) == /\ p \in 2..N /\ StepPid(p)

Next ==
  Step1 \/ (\E p \in 2..N: StepRest(p))

Fairness ==
  /\ WF_Vars(Step1)
  /\ \A p \in 2..N: WF_Vars(StepRest(p))

Spec == Init /\ [][Next]_Vars /\ Fairness

LiveSomeProcessInfinitelyOften ==
  \E p \in Proc: []<>(pc[p] = "CS")
============================================================================