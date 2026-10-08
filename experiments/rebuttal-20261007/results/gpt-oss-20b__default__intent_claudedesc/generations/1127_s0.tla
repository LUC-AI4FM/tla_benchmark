MODULE AtomicCommit

EXTENDS Naturals

CONSTANTS RMs

VARIABLE state

(* State values *)
Working  == "working"
Prepared == "prepared"
Committed== "committed"
Aborted  == "aborted"

TypeInvariant ==
  \A r \in RMs : state[r] \in {Working, Prepared, Committed, Aborted}

ConsistencyInvariant ==
  \A r1 \in RMs, r2 \in RMs :
    ~(state[r1] = Committed /\ state[r2] = Aborted)

Init ==
  \A r \in RMs : state[r] = Working

Prepare(r) ==
  /\ r \in RMs
  /\ state[r] = Working
  /\ state' = [state EXCEPT ![r] = Prepared]

Abort(r) ==
  /\ r \in RMs
  /\ state[r] # Committed
  /\ state[r] # Aborted
  /\ state' = [state EXCEPT ![r] = Aborted]

Commit(r) ==
  /\ r \in RMs
  /\ state[r] = Prepared
  /\ \A s \in RMs : state[s] \in {Prepared, Committed}
  /\ state' = [state EXCEPT ![r] = Committed]

Next == 
  \E r \in RMs :
    Prepare(r) \/ Abort(r) \/ Commit(r)

Spec == Init /\ [][Next]_state /\ TypeInvariant /\ ConsistencyInvariant

(* Example instance: set RMs to {1,2,3} in the configuration file *)