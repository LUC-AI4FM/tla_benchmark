------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

Proc == 1..N

VARIABLES
  x,      \* last process to write x, or 0
  y,      \* owner of the slow path, or 0
  b,      \* [Proc -> BOOLEAN] intent flags
  pc,     \* [Proc -> {"try","checkY","waitY0","checkX","scan","afterScan","waitY0b","cs"}]
  j,      \* [Proc -> (Proc \cup {0})] scan index, 0 means done
  failed  \* [Proc -> BOOLEAN] saw a contender while scanning

vars == << x, y, b, pc, j, failed >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "try"]
  /\ j = [i \in Proc |-> 0]
  /\ failed = [i \in Proc |-> FALSE]

ProcStep(self) ==
  \/ /\ pc[self] = "try"
     /\ b' = [b EXCEPT ![self] = TRUE]
     /\ x' = self
     /\ pc' = [pc EXCEPT ![self] = "checkY"]
     /\ UNCHANGED << y, j, failed >>

  \/ /\ pc[self] = "checkY"
     /\ y # 0
     /\ b' = [b EXCEPT ![self] = FALSE]
     /\ pc' = [pc EXCEPT ![self] = "waitY0"]
     /\ UNCHANGED << x, y, j, failed >>

  \/ /\ pc[self] = "checkY"
     /\ y = 0
     /\ y' = self
     /\ pc' = [pc EXCEPT ![self] = "checkX"]
     /\ UNCHANGED << x, b, j, failed >>

  \/ /\ pc[self] = "waitY0"
     /\ y = 0
     /\ pc' = [pc EXCEPT ![self] = "try"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \/ /\ pc[self] = "checkX"
     /\ x # self
     /\ b' = [b EXCEPT ![self] = FALSE]
     /\ j' = [j EXCEPT ![self] = 1]
     /\ failed' = [failed EXCEPT ![self] = FALSE]
     /\ pc' = [pc EXCEPT ![self] = "scan"]
     /\ UNCHANGED << x, y >>

  \/ /\ pc[self] = "checkX"
     /\ x = self
     /\ pc' = [pc EXCEPT ![self] = "cs"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \/ /\ pc[self] = "scan"
     /\ j[self] # 0
     /\ LET jCurr == j[self]
            jNext == IF jCurr = N THEN 0 ELSE jCurr + 1
            failNow == (jCurr \in Proc) /\ (jCurr # self) /\ b[jCurr]
        IN
        /\ failed' = [failed EXCEPT ![self] = failed[self] \/ failNow]
        /\ j' = [j EXCEPT ![self] = jNext]
        /\ pc' = [pc EXCEPT ![self] = IF jNext = 0 THEN "afterScan" ELSE "scan"]
        /\ UNCHANGED << x, y, b >>

  \/ /\ pc[self] = "afterScan"
     /\ y = self
     /\ pc' = [pc EXCEPT ![self] = "cs"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \/ /\ pc[self] = "afterScan"
     /\ y # self
     /\ pc' = [pc EXCEPT ![self] = "waitY0b"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \/ /\ pc[self] = "waitY0b"
     /\ y = 0
     /\ pc' = [pc EXCEPT ![self] = "try"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \/ /\ pc[self] = "cs"
     /\ y' = 0
     /\ b' = [b EXCEPT ![self] = FALSE]
     /\ pc' = [pc EXCEPT ![self] = "try"]
     /\ UNCHANGED << x, j, failed >>

Next ==
  \E self \in Proc : ProcStep(self)

Spec ==
  Init /\ [][Next]_vars /\ (\A i \in Proc : WF_vars(ProcStep(i)))

TypeOK ==
  /\ x \in ({0} \cup Proc)
  /\ y \in ({0} \cup Proc)
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> {"try","checkY","waitY0","checkX","scan","afterScan","waitY0b","cs"}]
  /\ j \in [Proc -> ({0} \cup Proc)]
  /\ failed \in [Proc -> BOOLEAN]

MutualExclusion ==
  \A i, k \in Proc : (i # k) => ~ (pc[i] = "cs" /\ pc[k] = "cs")

InfinitelyOftenCS ==
  []<>(\E i \in Proc : pc[i] = "cs")

=============================================================================