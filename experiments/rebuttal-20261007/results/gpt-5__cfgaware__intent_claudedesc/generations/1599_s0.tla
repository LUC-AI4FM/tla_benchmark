---- MODULE FastMutex ----
EXTENDS Naturals, TLC

CONSTANT N

ProcSet == 1..N

VARIABLES X, Y, flag, pc

vars == << X, Y, flag, pc >>

Init ==
  /\ X = 0
  /\ Y = 0
  /\ flag = [ i \in ProcSet |-> FALSE ]
  /\ pc = [ i \in ProcSet |-> "ncs" ]

Attempting(i) == pc[i] # "ncs"
InCS(i) == pc[i] = "cs"

Want(i) ==
  /\ pc[i] = "ncs"
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "setX"]
  /\ UNCHANGED << X, Y >>

SetX(i) ==
  /\ pc[i] = "setX"
  /\ X' = i
  /\ pc' = [pc EXCEPT ![i] = "checkYbusy"]
  /\ UNCHANGED << Y, flag >>

Busy1(i) ==
  /\ pc[i] = "checkYbusy"
  /\ Y # 0
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0_a"]
  /\ UNCHANGED << X, Y >>

NotBusy1(i) ==
  /\ pc[i] = "checkYbusy"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "setY"]
  /\ UNCHANGED << X, Y, flag >>

WaitY0_a(i) ==
  /\ pc[i] = "waitY0_a"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED << X, Y, flag >>

SetY(i) ==
  /\ pc[i] = "setY"
  /\ Y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkXeq"]
  /\ UNCHANGED << X, flag >>

First(i) ==
  /\ pc[i] = "checkXeq"
  /\ X = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << X, Y, flag >>

NotFirst(i) ==
  /\ pc[i] = "checkXeq"
  /\ X # i
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitAllFalse"]
  /\ UNCHANGED << X, Y >>

AfterAllFalse(i) ==
  /\ pc[i] = "waitAllFalse"
  /\ \A j \in ProcSet: flag[j] = FALSE
  /\ IF Y = i
     THEN /\ pc' = [pc EXCEPT ![i] = "cs"]
          /\ UNCHANGED << X, Y, flag >>
     ELSE /\ pc' = [pc EXCEPT ![i] = "waitY0_b"]
          /\ UNCHANGED << X, Y, flag >>

WaitY0_b(i) ==
  /\ pc[i] = "waitY0_b"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED << X, Y, flag >>

Exit(i) ==
  /\ pc[i] = "cs"
  /\ Y' = 0
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED X

ProcStep(i) ==
  Want(i)
  \/ SetX(i)
  \/ Busy1(i)
  \/ NotBusy1(i)
  \/ WaitY0_a(i)
  \/ SetY(i)
  \/ First(i)
  \/ NotFirst(i)
  \/ AfterAllFalse(i)
  \/ WaitY0_b(i)
  \/ Exit(i)

Next ==
  \E i \in ProcSet: ProcStep(i)

Invariant ==
  \A i, j \in ProcSet: i # j => ~(InCS(i) /\ InCS(j))

CondLiveness ==
  ( \E i \in ProcSet: <>[] Attempting(i) )
  => ([]<> (\E j \in ProcSet: InCS(j)))

FairSpec ==
  Init
  /\ [][Next]_vars
  /\ \A i \in ProcSet:
       /\ WF_vars(Want(i))
       /\ WF_vars(SetX(i))
       /\ WF_vars(Busy1(i))
       /\ WF_vars(NotBusy1(i))
       /\ WF_vars(WaitY0_a(i))
       /\ WF_vars(SetY(i))
       /\ WF_vars(First(i))
       /\ WF_vars(NotFirst(i))
       /\ WF_vars(AfterAllFalse(i))
       /\ WF_vars(WaitY0_b(i))
       /\ WF_vars(Exit(i))

====