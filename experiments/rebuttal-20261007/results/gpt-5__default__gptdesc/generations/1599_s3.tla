------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals

CONSTANT N

Proc == 1..N

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

Locs == {"ncs","a1","a2","a2w","a3","a3w1","a3w2","cs","exit"}

TypeOK ==
  /\ x \in Proc \cup {0}
  /\ y \in Proc \cup {0}
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> Locs]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "ncs"]

AllOthersNotTrying(i) == \A j \in Proc: (j = i) \/ ~b[j]

NCS(i) ==
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED << x, y, b >>

A1(i) ==
  /\ pc[i] = "a1"
  /\ b'  = [b EXCEPT ![i] = TRUE]
  /\ x'  = i
  /\ pc' = [pc EXCEPT ![i] = "a2"]
  /\ UNCHANGED y

A2a(i) ==
  /\ pc[i] = "a2"
  /\ y = 0
  /\ y'  = i
  /\ pc' = [pc EXCEPT ![i] = "a3"]
  /\ UNCHANGED << x, b >>

A2b(i) ==
  /\ pc[i] = "a2"
  /\ y # 0
  /\ b'  = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "a2w"]
  /\ UNCHANGED << x, y >>

A2w(i) ==
  /\ pc[i] = "a2w"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED << x, y, b >>

A3a(i) ==
  /\ pc[i] = "a3"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

A3b(i) ==
  /\ pc[i] = "a3"
  /\ x # i
  /\ b'  = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "a3w1"]
  /\ UNCHANGED << x, y >>

A3w1_toCs(i) ==
  /\ pc[i] = "a3w1"
  /\ AllOthersNotTrying(i)
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

A3w1_toYWait(i) ==
  /\ pc[i] = "a3w1"
  /\ AllOthersNotTrying(i)
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "a3w2"]
  /\ UNCHANGED << x, y, b >>

A3w2(i) ==
  /\ pc[i] = "a3w2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED << x, y, b >>

CSskip(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << x, y, b >>

Exit(i) ==
  /\ pc[i] = "exit"
  /\ y'  = 0
  /\ b'  = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED x

ProcStep(i) ==
     NCS(i)
  \/ A1(i)
  \/ A2a(i) \/ A2b(i) \/ A2w(i)
  \/ A3a(i) \/ A3b(i)
  \/ A3w1_toCs(i) \/ A3w1_toYWait(i) \/ A3w2(i)
  \/ CSskip(i) \/ Exit(i)

Next == \E i \in Proc: ProcStep(i)

Spec == Init /\ [][Next]_vars

Fair ==
  /\ \A i \in Proc: WF_vars(A1(i))
  /\ \A i \in Proc: WF_vars(A2a(i))
  /\ \A i \in Proc: WF_vars(A2b(i))
  /\ \A i \in Proc: WF_vars(A2w(i))
  /\ \A i \in Proc: WF_vars(A3a(i))
  /\ \A i \in Proc: WF_vars(A3b(i))
  /\ \A i \in Proc: WF_vars(A3w1_toCs(i))
  /\ \A i \in Proc: WF_vars(A3w1_toYWait(i))
  /\ \A i \in Proc: WF_vars(A3w2(i))
  /\ \A i \in Proc: WF_vars(Exit(i))

FairSpec == Spec /\ Fair

MutualExclusion ==
  \A i, j \in Proc: (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

SafetyInvariant == TypeOK /\ MutualExclusion

Trying(i) == pc[i] \in {"a1","a2","a2w","a3","a3w1","a3w2"}

Liveness ==
  \A i \in Proc: Trying(i) ~> (pc[i] = "cs")

ConditionalLiveness ==
  \A i \in Proc: [] ( (Trying(i) /\ AllOthersNotTrying(i)) => <> (pc[i] = "cs") )
=============================================================================