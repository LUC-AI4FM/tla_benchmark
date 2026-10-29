------------------------------ MODULE TCommit ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT RM          \* The set of participating resource managers

VARIABLE rmState     \* rmState[rm] is the state of resource manager rm

vars == << rmState >>

States == {"working", "prepared", "committed", "aborted"}

-----------------------------------------------------------------------------
TypeOK == rmState \in [RM -> States]

Init == rmState = [rm \in RM |-> "working"]

(* Every RM is prepared to commit or has already committed. *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

(* No RM has committed. *)
notCommitted == \A rm \in RM : rmState[rm] # "committed"

-----------------------------------------------------------------------------
(* An RM in the working state signals that it is prepared to commit. *)
Prepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

(* An RM reaches a final decision. *)
Decide(rm) ==
    \/ /\ rmState[rm] = "prepared"
       /\ canCommit
       /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    \/ /\ rmState[rm] \in {"working", "prepared"}
       /\ notCommitted
       /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

Next == \E rm \in RM : Prepare(rm) \/ Decide(rm)

Fairness == \A rm \in RM : WF_vars(Decide(rm))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* Consistency: no RM commits while another aborts. *)
Consistency ==
    \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                           /\ rmState[rm2] = "committed"

(* Validity: a commit happens only if every RM was prepared to commit. *)
Validity ==
    (\E rm \in RM : rmState[rm] = "committed")
        => \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

(* Stability: once committed or aborted, an RM's decision is irrevocable. *)
Stability ==
    [][\A rm \in RM : rmState[rm] \in {"committed", "aborted"}
                        => rmState'[rm] = rmState[rm]]_vars

(* Liveness: all RMs eventually reach the same final decision. *)
AllCommitted == \A rm \in RM : rmState[rm] = "committed"
AllAborted   == \A rm \in RM : rmState[rm] = "aborted"

Agreement == <>[](AllCommitted \/ AllAborted)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Consistency /\ Validity)
THEOREM Spec => Stability
THEOREM Spec => Agreement
=============================================================================