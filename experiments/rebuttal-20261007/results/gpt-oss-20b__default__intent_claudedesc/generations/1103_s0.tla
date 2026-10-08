MODULE NBAC
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLES procStatus, vote, decision, fdStatus, pending

(* Types *)
Alive = {"alive", "crashed"}
VoteVal = {"YES","NO"}
DecisionVal = {"COMMIT","ABORT","NONE"}
FDVal = {"all-correct","crashed"}

Init ==
  /\ procStatus = [p \in 1..N |-> "alive"]
  /\ vote = [p \in 1..N |-> CHOOSE v \in VoteVal : TRUE]
  /\ decision = [p \in 1..N |-> "NONE"]
  /\ fdStatus = [p \in 1..N |-> "all-correct"]
  /\ pending = [r \in 1..N |-> {s \in 1..N : procStatus[s]="alive"}]

Crash(p) ==
  /\ p \in 1..N
  /\ procStatus[p] = "alive"
  /\ procStatus' = [procStatus EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<vote, decision, fdStatus, pending>>

FDChange ==
  /\ \E p \in 1..N :
       fdStatus' = [fdStatus EXCEPT ![p] = CHOOSE f \in FDVal : TRUE]
  /\ UNCHANGED <<procStatus, vote, decision, pending>>

Deliver(r,s) ==
  /\ r \in 1..N
  /\ s \in pending[r]
  /\ procStatus[r] = "alive"
  /\ procStatus[s] = "alive"
  /\ pending' = [pending EXCEPT ![r] = pending[r] \ {s}]
  /\ UNCHANGED <<procStatus, vote, decision, fdStatus>>

Commit(p) ==
  /\ p \in 1..N
  /\ procStatus[p] = "alive"
  /\ decision[p] = "NONE"
  /\ (\A s \in 1..N : s \notin pending[p] /\ vote[s] = "YES")
  /\ fdStatus[p] = "all-correct"
  /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
  /\ UNCHANGED <<procStatus, vote, pending, fdStatus>>

Abort(p) ==
  /\ p \in 1..N
  /\ procStatus[p] = "alive"
  /\ decision[p] = "NONE"
  /\ (fdStatus[p] = "crashed" \/ (\E s \in 1..N : s \notin pending[p] /\ vote[s] = "NO"))
  /\ decision' = [decision EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED <<procStatus, vote, pending, fdStatus>>

Next ==
  \/ \E p \in 1..N : Crash(p)
  \/ FDChange
  \/ \E r,s \in 1..N : Deliver(r,s)
  \/ \E p \in 1..N : Commit(p)
  \/ \E p \in 1..N : Abort(p)

TypeInvariant ==
  /\ procStatus \in [1..N -> Alive]
  /\ vote \in [1..N -> VoteVal]
  /\ decision \in [1..N -> DecisionVal]
  /\ fdStatus \in [1..N -> FDVal]
  /\ pending \in [1..N -> SUBSET 1..N]

ValidityInvariant ==
  \A p \in 1..N : (decision[p] = "COMMIT" => (\A q \in 1..N : vote[q] = "YES"))

Safety == TypeInvariant /\ ValidityInvariant

Fairness == WF_vars(Commit) /\ WF_vars(Abort)

Spec == Init /\ [][Next]_vars /\ Fairness /\ Safety
===============================================================================