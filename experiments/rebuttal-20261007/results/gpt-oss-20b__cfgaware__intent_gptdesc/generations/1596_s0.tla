------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, M \* number of processes, number of shared coordination variables (2)

P == 1 .. N

(* State constants *)
DEFINE
  Idle    == 0
  Announce== 1
  Critical== 2

VARIABLES flags, turn, state

NextProcess(i) == IF i < N THEN i + 1 ELSE 1

Init ==
  /\ flags = [i \in P |-> FALSE]
  /\ turn  = 1
  /\ state = [i \in P |-> Idle]

Attempt(i) ==
  /\ i \in P
  /\ state[i] = Idle
  /\ flags' = [flags EXCEPT ![i] = TRUE]
  /\ state' = [state EXCEPT ![i] = Announce]
  /\ turn'  = turn

WaitAbort(i) ==
  /\ i \in P
  /\ state[i] = Announce
  /\ turn # i
  /\ flags' = [flags EXCEPT ![i] = FALSE]
  /\ state' = [state EXCEPT ![i] = Idle]
  /\ turn'  = turn

EnterCS(i) ==
  /\ i \in P
  /\ state[i] = Announce
  /\ turn = i
  /\ flags' = flags
  /\ state' = [state EXCEPT ![i] = Critical]
  /\ turn'  = turn

Leave(i) ==
  /\ i \in P
  /\ state[i] = Critical
  /\ flags' = [flags EXCEPT ![i] = FALSE]
  /\ state' = [state EXCEPT ![i] = Idle]
  /\ turn'  = NextProcess(i)

Next ==
  \E i \in P :
    Attempt(i) \/ WaitAbort(i) \/ EnterCS(i) \/ Leave(i)

Spec == Init /\ []Next

Invariant ==
  \A i, j \in P : (i # j) => ~(state[i] = Critical /\ state[j] = Critical)

Liveness ==
  []<>(\E i \in P : state[i] = Critical)
  /\ \A i \in P : []<> (state[i] = Idle => <> (state[i] = Critical))

=============================================================================