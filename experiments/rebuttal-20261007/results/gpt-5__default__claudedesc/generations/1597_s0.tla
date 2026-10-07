------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES x, y, b,
          pc1, j, failed,
          pc2, j2, failed2

Proc2Range == 2..N
ProcRange == 1..N

PC(i) == IF i = 1 THEN pc1 ELSE pc2[i]

vars == << x, y, b, pc1, j, failed, pc2, j2, failed2 >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcRange |-> FALSE]
  /\ pc1 = "start"
  /\ j = 1
  /\ failed = FALSE
  /\ pc2 = [i \in Proc2Range |-> "start"]
  /\ j2 = [i \in Proc2Range |-> 1]
  /\ failed2 = [i \in Proc2Range |-> FALSE]

Proc1Action ==
  \/ /\ pc1 = "start"
     /\ b' = [b EXCEPT ![1] = TRUE]
     /\ pc1' = "writex"
     /\ UNCHANGED << x, y, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "writex"
     /\ x' = 1
     /\ pc1' = "checkY"
     /\ UNCHANGED << y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "checkY"
     /\ y # 0
     /\ pc1' = "waitY"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "checkY"
     /\ y = 0
     /\ pc1' = "setY"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "waitY"
     /\ y = 0
     /\ pc1' = "start"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "setY"
     /\ y' = 1
     /\ pc1' = "checkX"
     /\ UNCHANGED << x, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "checkX"
     /\ x # 1
     /\ pc1' = "clearB"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "checkX"
     /\ x = 1
     /\ failed' = FALSE
     /\ pc1' = "crit"
     /\ UNCHANGED << x, y, b, j, pc2, j2, failed2 >>
  \/ /\ pc1 = "clearB"
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ pc1' = "setJ"
     /\ UNCHANGED << x, y, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "setJ"
     /\ j' = 1
     /\ pc1' = "awaitB"
     /\ UNCHANGED << x, y, b, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "awaitB"
     /\ j <= N
     /\ (j = 1 \/ ~b[j])
     /\ j' = j + 1
     /\ pc1' = "awaitB"
     /\ UNCHANGED << x, y, b, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "awaitB"
     /\ j > N
     /\ pc1' = "checkOwnY"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "checkOwnY"
     /\ y = 1
     /\ failed' = FALSE
     /\ pc1' = "maybeCS"
     /\ UNCHANGED << x, y, b, j, pc2, j2, failed2 >>
  \/ /\ pc1 = "checkOwnY"
     /\ y # 1
     /\ failed' = TRUE
     /\ pc1' = "maybeCS"
     /\ UNCHANGED << x, y, b, j, pc2, j2, failed2 >>
  \/ /\ pc1 = "maybeCS"
     /\ ~failed
     /\ pc1' = "crit"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "maybeCS"
     /\ failed
     /\ pc1' = "start"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "crit"
     /\ pc1' = "exit"
     /\ UNCHANGED << x, y, b, j, failed, pc2, j2, failed2 >>
  \/ /\ pc1 = "exit"
     /\ y' = 0
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ pc1' = "start"
     /\ UNCHANGED << x, j, failed, pc2, j2, failed2 >>

Proc2Action(i) ==
  \/ /\ pc2[i] = "start"
     /\ b' = [b EXCEPT ![i] = TRUE]
     /\ pc2' = [pc2 EXCEPT ![i] = "writex"]
     /\ UNCHANGED << x, y, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "writex"
     /\ x' = i
     /\ pc2' = [pc2 EXCEPT ![i] = "checkY"]
     /\ UNCHANGED << y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "checkY"
     /\ y # 0
     /\ pc2' = [pc2 EXCEPT ![i] = "waitY"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "checkY"
     /\ y = 0
     /\ pc2' = [pc2 EXCEPT ![i] = "setY"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "waitY"
     /\ y = 0
     /\ pc2' = [pc2 EXCEPT ![i] = "start"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "setY"
     /\ y' = i
     /\ pc2' = [pc2 EXCEPT ![i] = "checkX"]
     /\ UNCHANGED << x, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "checkX"
     /\ x # i
     /\ pc2' = [pc2 EXCEPT ![i] = "clearB"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "checkX"
     /\ x = i
     /\ failed2' = [failed2 EXCEPT ![i] = FALSE]
     /\ pc2' = [pc2 EXCEPT ![i] = "crit"]
     /\ UNCHANGED << x, y, b, pc1, j, j2 >>
  \/ /\ pc2[i] = "clearB"
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc2' = [pc2 EXCEPT ![i] = "setJ"]
     /\ UNCHANGED << x, y, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "setJ"
     /\ j2' = [j2 EXCEPT ![i] = 1]
     /\ pc2' = [pc2 EXCEPT ![i] = "awaitB"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, failed2 >>
  \/ /\ pc2[i] = "awaitB"
     /\ j2[i] <= N
     /\ (j2[i] = i \/ ~b[j2[i]])
     /\ j2' = [j2 EXCEPT ![i] = j2[i] + 1]
     /\ pc2' = [pc2 EXCEPT ![i] = "awaitB"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, failed2 >>
  \/ /\ pc2[i] = "awaitB"
     /\ j2[i] > N
     /\ pc2' = [pc2 EXCEPT ![i] = "checkOwnY"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "checkOwnY"
     /\ y = i
     /\ failed2' = [failed2 EXCEPT ![i] = FALSE]
     /\ pc2' = [pc2 EXCEPT ![i] = "maybeCS"]
     /\ UNCHANGED << x, y, b, pc1, j, j2 >>
  \/ /\ pc2[i] = "checkOwnY"
     /\ y # i
     /\ failed2' = [failed2 EXCEPT ![i] = TRUE]
     /\ pc2' = [pc2 EXCEPT ![i] = "maybeCS"]
     /\ UNCHANGED << x, y, b, pc1, j, j2 >>
  \/ /\ pc2[i] = "maybeCS"
     /\ ~failed2[i]
     /\ pc2' = [pc2 EXCEPT ![i] = "crit"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "maybeCS"
     /\ failed2[i]
     /\ pc2' = [pc2 EXCEPT ![i] = "start"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "crit"
     /\ pc2' = [pc2 EXCEPT ![i] = "exit"]
     /\ UNCHANGED << x, y, b, pc1, j, failed, j2, failed2 >>
  \/ /\ pc2[i] = "exit"
     /\ y' = 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc2' = [pc2 EXCEPT ![i] = "start"]
     /\ UNCHANGED << x, pc1, j, failed, j2, failed2 >>

Next ==
  Proc1Action \/ (\E i \in Proc2Range: Proc2Action(i))

Spec ==
  Init /\ [][Next]_vars /\
  WF_vars(Proc1Action) /\
  (\A i \in Proc2Range: WF_vars(Proc2Action(i)))

Invariant ==
  \A p \in ProcRange: \A q \in ProcRange:
    (p # q) => ~(PC(p) = "crit" /\ PC(q) = "crit")

CritOccur == \E i \in ProcRange: PC(i) = "crit"

Liveness == []<>(CritOccur)

=============================================================================