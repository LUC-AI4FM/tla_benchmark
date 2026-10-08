MODULE FastMutualExclusion
EXTENDS Naturals

CONSTANT N
ASSUME 2 <= N

VARIABLES x, y, b, state

Proc == 1..N

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i ∈ Proc |-> FALSE]
  /\ state = [i ∈ Proc |-> "Idle"]

Next_i(i) ==
  \/ (* SetX step *)
     /\ state[i] = "Idle"
     /\ x' = i
     /\ state' = [state EXCEPT ![i] = "CheckY"]
     /\ UNCHANGED <<y, b>>
  \/ (* CheckY step *)
     /\ state[i] = "CheckY"
     /\ y = 0
     /\ y' = i
     /\ state' = [state EXCEPT ![i] = "CS"]
     /\ UNCHANGED <<x, b>>
  \/ (* EnterCS step *)
     /\ state[i] = "CS"
     /\ b' = [b EXCEPT ![i] = TRUE]
     /\ state' = [state EXCEPT ![i] = "Exit"]
     /\ UNCHANGED <<x, y>>
  \/ (* Exit step *)
     /\ state[i] = "Exit"
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ x' = 0
     /\ y' = 0
     /\ state' = [state EXCEPT ![i] = "Idle"]

Next == ∨ i ∈ Proc : Next_i(i)

MutualExclusion ==
  ∀ i,j ∈ Proc :
    i ≠ j => ~(state[i]="CS" ∧ state[j]="CS")

Liveness ==
  □◇ (∃ i ∈ Proc : state[i]="CS")

Fairness == WF_vars(state)

Spec ==
  Init
  /\ [][Next]_<<x, y, b, state>>
  /\ Fairness
  /\ MutualExclusion
  /\ Liveness

END MODULE