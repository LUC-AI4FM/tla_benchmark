------------------------------ MODULE Fischer ------------------------------
EXTENDS Naturals, Sequences, Temporal, TLC

CONSTANTS N, Delta, Epsilon

VARIABLES x, timers, state

(* State values *)
StateVals == {"a","b","c","d","e","f"}

Init ==
  /\ x = 0
  /\ timers = [i \in 1..N |-> 0]
  /\ state = [i \in 1..N |-> "a"]

A_i_a_c(i) ==
  /\ state[i] = "a"
  /\ state' = [state EXCEPT ![i] = "c"]
  /\ timers' = timers
  /\ x' = x

A_i_c_d(i) ==
  /\ state[i] = "c"
  /\ x = 0
  /\ state' = [state EXCEPT ![i] = "d"]
  /\ timers' = [timers EXCEPT ![i] = Delta]
  /\ x' = i

A_i_d_e(i) ==
  /\ state[i] = "d"
  /\ state' = [state EXCEPT ![i] = "e"]
  /\ timers' = [timers EXCEPT ![i] = Epsilon]
  /\ x' = x

A_i_e_b(i) ==
  /\ state[i] = "e"
  /\ timers[i] = 0
  /\ state' = [state EXCEPT ![i] = "b"]
  /\ timers' = timers
  /\ x' = x

A_i_b_f(i) ==
  /\ state[i] = "b"
  /\ x = i
  /\ state' = [state EXCEPT ![i] = "f"]
  /\ timers' = timers
  /\ x' = x

A_i_b_a(i) ==
  /\ state[i] = "b"
  /\ x # i
  /\ state' = [state EXCEPT ![i] = "a"]
  /\ timers' = timers
  /\ x' = x

A_i_f_a(i) ==
  /\ state[i] = "f"
  /\ state' = [state EXCEPT ![i] = "a"]
  /\ timers' = timers
  /\ x' = 0

Process(i) == 
  A_i_a_c(i) \/ A_i_c_d(i) \/ A_i_d_e(i) \/ A_i_e_b(i) \/
  A_i_b_f(i) \/ A_i_b_a(i) \/ A_i_f_a(i)

Tick ==
  /\ (∀ i \in 1..N : timers[i] > 0)
  /\ state' = state
  /\ timers' = [j \in 1..N |-> timers[j]-1]
  /\ x' = x

Next == 
  \/ ∨ i \in 1..N : Process(i)
  \/ Tick

vars == <<x, timers, state>>

Spec == Init /\ [][Next]_vars /\ (∀ i \in 1..N : WF_vars(Process(i))) /\ WF_vars(Tick)

Invariant ==
  ¬∃ i, j \in 1..N : i # j /\ state[i] = "f" /\ state[j] = "f"

Liveness ==
  ∃ i \in 1..N : [] <> (state[i] = "f")

============================================================================