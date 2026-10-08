------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES x, y, b, j

DOMAIN == 1 .. N

Init ==
  /\ x = 0
  /\ y = 0
  /\ b \in [DOMAIN -> {TRUE, FALSE}]
  /\ j \in [DOMAIN -> {0,1,2,3,4,5,6}]
  /\ \A i \in DOMAIN : b[i] = FALSE
  /\ \A i \in DOMAIN : j[i] = 0

SetFlagTrue(i) ==
  /\ j[i] = 0
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ UNCHANGED <<x, y>>

WriteX(i) ==
  /\ j[i] = 1
  /\ x' = i
  /\ j' = [j EXCEPT ![i] = 2]
  /\ UNCHANGED <<b, y>>

CheckYProceed(i) ==
  /\ j[i] = 2
  /\ (y = 0 \/ y = i)
  /\ j' = [j EXCEPT ![i] = 4]
  /\ UNCHANGED <<x, b, y>>

CheckYConflict(i) ==
  /\ j[i] = 2
  /\ (y #= 0 /\ y #= i)
  /\ j' = [j EXCEPT ![i] = 3]
  /\ UNCHANGED <<x, b, y>>

SetFlagFalseAndWait(i) ==
  /\ j[i] = 3
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 4]
  /\ UNCHANGED <<x, y>>

WaitForYZero(i) ==
  /\ j[i] = 4
  /\ y #= 0
  /\ UNCHANGED <<x, y, b, j>>

ProceedAfterWait(i) ==
  /\ j[i] = 4
  /\ y = 0
  /\ j' = [j EXCEPT ![i] = 5]
  /\ UNCHANGED <<x, b>>

EnterCritical(i) ==
  /\ j[i] = 5
  /\ y' = i
  /\ j' = [j EXCEPT ![i] = 6]
  /\ UNCHANGED <<x, b>>

InCritical(i) ==
  /\ j[i] = 6
  /\ UNCHANGED <<x, y, b, j>>

ExitCritical(i) ==
  /\ j[i] = 6
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 0]
  /\ UNCHANGED <<x>>

ProcessAction(i) ==
  SetFlagTrue(i) \/ WriteX(i) \/ CheckYProceed(i) \/ CheckYConflict(i)
  \/ SetFlagFalseAndWait(i) \/ WaitForYZero(i) \/ ProceedAfterWait(i)
  \/ EnterCritical(i) \/ ExitCritical(i)

Next == \E i \in DOMAIN : ProcessAction(i)

vars == <<x, y, b, j>>

Spec ==
  Init /\ [][Next]_vars & WF_(\E i \in DOMAIN : ProcessAction(i))

MutualExcl ==
  ~\E i, k \in DOMAIN : i # k /\ (j[i] = 6) /\ (j[k] = 6)

Liveness == \E i \in DOMAIN : InfinitelyOften(j[i] = 6)

SpecWithInvariants == Spec /\ MutualExcl
FinalSpec == SpecWithInvariants /\ Liveness

=============================================================================