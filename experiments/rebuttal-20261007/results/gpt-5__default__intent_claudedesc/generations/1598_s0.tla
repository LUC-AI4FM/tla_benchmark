----------------------------- MODULE FastMutex -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Proc == 1..N

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

CS(i) == pc[i] = "cs"

NoOtherFlag(i) == \A j \in Proc : j /= i => ~b[j]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "idle"]

TrySetB(i) ==
  /\ pc[i] = "idle"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![i] = "setX"]

WriteX(i) ==
  /\ pc[i] = "setX"
  /\ x' = i
  /\ UNCHANGED << y, b >>
  /\ pc' = [pc EXCEPT ![i] = "setY"]

WriteY(i) ==
  /\ pc[i] = "setY"
  /\ y' = i
  /\ UNCHANGED << x, b >>
  /\ pc' = [pc EXCEPT ![i] = "checkY"]

CheckY_OK(i) ==
  /\ pc[i] = "checkY"
  /\ y = i
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![i] = "checkX"]

CheckY_Contend(i) ==
  /\ pc[i] = "checkY"
  /\ y /= i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![i] = "waitY"]

CheckX_OK_HoldX(i) ==
  /\ pc[i] = "checkX"
  /\ x = i
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![i] = "cs"]

CheckX_OK_NoOtherFlag(i) ==
  /\ pc[i] = "checkX"
  /\ x /= i
  /\ NoOtherFlag(i)
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![i] = "cs"]

CheckX_Contend(i) ==
  /\ pc[i] = "checkX"
  /\ x /= i
  /\ ~NoOtherFlag(i)
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![i] = "waitY"]

WaitY_Clear(i) ==
  /\ pc[i] = "waitY"
  /\ y = 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![i] = "idle"]

ExitCS(i) ==
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED x
  /\ pc' = [pc EXCEPT ![i] = "idle"]

Step(i) ==
  \/ TrySetB(i)
  \/ WriteX(i)
  \/ WriteY(i)
  \/ CheckY_OK(i)
  \/ CheckY_Contend(i)
  \/ CheckX_OK_HoldX(i)
  \/ CheckX_OK_NoOtherFlag(i)
  \/ CheckX_Contend(i)
  \/ WaitY_Clear(i)
  \/ ExitCS(i)

Next ==
  \E i \in Proc : Step(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(Step(i))

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> {"idle", "setX", "setY", "checkY", "checkX", "waitY", "cs"}]

MutualExclusion ==
  \A i, j \in Proc : i /= j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness ==
  \E i \in Proc : []<> CS(i)

============================================================================