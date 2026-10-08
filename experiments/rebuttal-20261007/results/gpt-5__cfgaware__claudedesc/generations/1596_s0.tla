------------------------------- MODULE FastMutex2 -------------------------------

EXTENDS Integers, Naturals

CONSTANTS N, M

VARIABLES x, y, b, pc1, pc2, loop1, loop2, fail1, fail2

Proc1 == 1..M
Proc2 == (M + 1)..N
Proc  == Proc1 \cup Proc2

Vars == << x, y, b, pc1, pc2, loop1, loop2, fail1, fail2 >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [ p \in Proc |-> FALSE ]
  /\ pc1 = [ i \in Proc1 |-> "ncs" ]
  /\ pc2 = [ i \in Proc2 |-> "ncs" ]
  /\ loop1 = [ i \in Proc1 |-> 0 ]
  /\ loop2 = [ i \in Proc2 |-> 0 ]
  /\ fail1 = [ i \in Proc1 |-> FALSE ]
  /\ fail2 = [ i \in Proc2 |-> FALSE ]

Proc1Step(i) ==
  i \in Proc1 /\
  (
    /\ pc1[i] = "ncs"
    /\ x' = i
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc1' = [pc1 EXCEPT ![i] = "checkY"]
    /\ UNCHANGED << y, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "checkY" /\ y # 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc1' = [pc1 EXCEPT ![i] = "waitY"]
    /\ UNCHANGED << x, y, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "checkY" /\ y = 0
    /\ y' = i
    /\ pc1' = [pc1 EXCEPT ![i] = "checkX"]
    /\ UNCHANGED << x, b, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "waitY" /\ y = 0
    /\ pc1' = [pc1 EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << x, y, b, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "checkX" /\ x # i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc1' = [pc1 EXCEPT ![i] = "waitB"]
    /\ UNCHANGED << x, y, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "checkX" /\ x = i
    /\ pc1' = [pc1 EXCEPT ![i] = "cs"]
    /\ UNCHANGED << x, y, b, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "waitB" /\ \A j \in Proc: ~b[j]
    /\ pc1' = [pc1 EXCEPT ![i] = "checkY2"]
    /\ UNCHANGED << x, y, b, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "checkY2"
    /\ fail1' = [fail1 EXCEPT ![i] = (y # i)]
    /\ pc1' = [pc1 EXCEPT ![i] = "waitY2"]
    /\ UNCHANGED << x, y, b, pc2, loop1, loop2, fail2 >>
  \/
    /\ pc1[i] = "waitY2" /\ y = 0
    /\ ((~fail1[i] /\ pc1' = [pc1 EXCEPT ![i] = "cs"])
        \/ ( fail1[i] /\ pc1' = [pc1 EXCEPT ![i] = "ncs"]))
    /\ UNCHANGED << x, y, b, pc2, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc1[i] = "cs"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ loop1' = [loop1 EXCEPT ![i] = loop1[i] + 1]
    /\ pc1' = [pc1 EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << x, pc2, loop2, fail1, fail2 >>
  )

Proc2Step(i) ==
  i \in Proc2 /\
  (
    /\ pc2[i] = "ncs"
    /\ x' = i
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc2' = [pc2 EXCEPT ![i] = "checkY"]
    /\ UNCHANGED << y, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "checkY" /\ y # 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc2' = [pc2 EXCEPT ![i] = "waitY"]
    /\ UNCHANGED << x, y, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "checkY" /\ y = 0
    /\ y' = i
    /\ pc2' = [pc2 EXCEPT ![i] = "checkX"]
    /\ UNCHANGED << x, b, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "waitY" /\ y = 0
    /\ pc2' = [pc2 EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << x, y, b, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "checkX" /\ x # i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc2' = [pc2 EXCEPT ![i] = "waitB"]
    /\ UNCHANGED << x, y, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "checkX" /\ x = i
    /\ pc2' = [pc2 EXCEPT ![i] = "cs"]
    /\ UNCHANGED << x, y, b, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "waitB" /\ \A j \in Proc: ~b[j]
    /\ pc2' = [pc2 EXCEPT ![i] = "checkY2"]
    /\ UNCHANGED << x, y, b, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "checkY2"
    /\ fail2' = [fail2 EXCEPT ![i] = (y # i)]
    /\ pc2' = [pc2 EXCEPT ![i] = "waitY2"]
    /\ UNCHANGED << x, y, b, pc1, loop1, loop2, fail1 >>
  \/
    /\ pc2[i] = "waitY2" /\ y = 0
    /\ ((~fail2[i] /\ pc2' = [pc2 EXCEPT ![i] = "cs"])
        \/ ( fail2[i] /\ pc2' = [pc2 EXCEPT ![i] = "ncs"]))
    /\ UNCHANGED << x, y, b, pc1, loop1, loop2, fail1, fail2 >>
  \/
    /\ pc2[i] = "cs"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ loop2' = [loop2 EXCEPT ![i] = loop2[i] + 1]
    /\ pc2' = [pc2 EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << x, pc1, loop1, fail1, fail2 >>
  )

Next ==
  (\E i \in Proc1: Proc1Step(i))
  \/ (\E i \in Proc2: Proc2Step(i))

InCS(p) ==
  (p \in Proc1 /\ pc1[p] = "cs" /\ ~fail1[p])
  \/ (p \in Proc2 /\ pc2[p] = "cs" /\ ~fail2[p])

CS(p) ==
  (p \in Proc1 /\ pc1[p] = "cs")
  \/ (p \in Proc2 /\ pc2[p] = "cs")

Spec ==
  Init
  /\ [][Next]_Vars
  /\ (\A i \in Proc1: WF_Vars(Proc1Step(i)))
  /\ (\A i \in Proc2: WF_Vars(Proc2Step(i)))

Invariant ==
  \A p \in Proc: \A q \in Proc:
    p # q => ~(InCS(p) /\ InCS(q))

Liveness ==
  []<>(\E p \in Proc: CS(p))

=============================================================================