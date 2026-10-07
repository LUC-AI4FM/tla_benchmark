------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

ProcSet == 1..N

VARIABLES x, y, b, S, pc

vars == << x, y, b, S, pc >>

Other(i) == ProcSet \ {i}

Lbls == {"start","writex","checky","checkx","scan","checky2","waity","cs"}

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ S = [i \in ProcSet |-> {}]
  /\ pc = [i \in ProcSet |-> "start"]

Proc(i) ==
  \/ /\ pc[i] = "start"
     /\ b' = [b EXCEPT ![i] = TRUE]
     /\ pc' = [pc EXCEPT ![i] = "writex"]
     /\ UNCHANGED << x, y, S >>
  \/ /\ pc[i] = "writex"
     /\ x' = i
     /\ pc' = [pc EXCEPT ![i] = "checky"]
     /\ UNCHANGED << b, y, S >>
  \/ /\ pc[i] = "checky" /\ y # 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc' = [pc EXCEPT ![i] = "waity"]
     /\ UNCHANGED << x, y, S >>
  \/ /\ pc[i] = "checky" /\ y = 0
     /\ y' = i
     /\ pc' = [pc EXCEPT ![i] = "checkx"]
     /\ UNCHANGED << b, x, S >>
  \/ /\ pc[i] = "checkx" /\ x = i
     /\ pc' = [pc EXCEPT ![i] = "cs"]
     /\ UNCHANGED << x, y, b, S >>
  \/ /\ pc[i] = "checkx" /\ x # i
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ S' = [S EXCEPT ![i] = Other(i)]
     /\ pc' = [pc EXCEPT ![i] = "scan"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[i] = "scan" /\ S[i] # {}
     /\ \E j \in S[i]: ~b[j]
           /\ S' = [S EXCEPT ![i] = S[i] \ {j}]
     /\ UNCHANGED << x, y, b, pc >>
  \/ /\ pc[i] = "scan" /\ S[i] = {}
     /\ pc' = [pc EXCEPT ![i] = "checky2"]
     /\ UNCHANGED << x, y, b, S >>
  \/ /\ pc[i] = "checky2" /\ y = i
     /\ pc' = [pc EXCEPT ![i] = "cs"]
     /\ UNCHANGED << x, y, b, S >>
  \/ /\ pc[i] = "checky2" /\ y # i
     /\ pc' = [pc EXCEPT ![i] = "waity"]
     /\ UNCHANGED << x, y, b, S >>
  \/ /\ pc[i] = "waity" /\ y = 0
     /\ pc' = [pc EXCEPT ![i] = "start"]
     /\ UNCHANGED << x, y, b, S >>
  \/ /\ pc[i] = "cs"
     /\ y' = 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc' = [pc EXCEPT ![i] = "start"]
     /\ UNCHANGED << x, S >>

Next == \E i \in ProcSet: Proc(i)

Spec == Init /\ [][Next]_vars /\ \A i \in ProcSet: WF_vars(Proc(i))

Invariant ==
  \A i, j \in ProcSet: (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness ==
  []<>(\E i \in ProcSet: pc[i] = "cs")

=============================================================================