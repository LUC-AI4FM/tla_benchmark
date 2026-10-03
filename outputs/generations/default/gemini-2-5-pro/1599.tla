-------------------------- MODULE FastMutex --------------------------
EXTENDS Integers, TLC

CONSTANT N
ASSUME N \in Nat \ {0}
ProcessSet == 1..N

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

(* The set of control locations (program counter values) for each process. *)
PCVals == {"ncs", "L1", "L2", "L3", "L5", "L6", "cs", "exit"}

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcessSet -> BOOLEAN]
    /\ pc \in [ProcessSet -> PCVals]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcessSet |-> FALSE]
    /\ pc = [i \in ProcessSet |-> "ncs"]

(***************************************************************************)
(* The actions for a process i.                                            *)
(***************************************************************************)

(* A process leaves its non-critical section to start competing for entry. *)
LeaveNCS(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "L1"]
    /\ UNCHANGED <<x, y, b>>

(* L1: Set intent flag and claim variable x. *)
L1(i) ==
    /\ pc[i] = "L1"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "L2"]
    /\ UNCHANGED <<y>>

(* L2, branch 1: If y is set by another process, back off. *)
L2(i) ==
    /\ pc[i] = "L2"
    /\ y /= 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "L3"]
    /\ UNCHANGED <<x, y>>

(* L3: Wait until y is cleared, then retry from the beginning. *)
L3(i) ==
    /\ pc[i] = "L3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "L1"]
    /\ UNCHANGED <<x, y, b>>

(* L2, branch 2: If y is not set, claim it. *)
L4(i) ==
    /\ pc[i] = "L2"
    /\ y = 0
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "L5"]
    /\ UNCHANGED <<x, b>>

(* L5, branch 1: If another process overwrote x, there is contention. *)
L5(i) ==
    /\ pc[i] = "L5"
    /\ x /= i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "L6"]
    /\ UNCHANGED <<x, y>>

(* L6: Wait for all other processes' intent flags to be cleared. Then, if y
   was stolen, retry; otherwise, this process won the race and enters the CS. *)
L6(i) ==
    /\ pc[i] = "L6"
    /\ \A j \in ProcessSet : b[j] = FALSE
    /\ IF y /= i
       THEN pc' = [pc EXCEPT ![i] = "L3"]
       ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b>>

(* L5, branch 2: If x was not overwritten, this process has a fast path to the CS. *)
L7(i) ==
    /\ pc[i] = "L5"
    /\ x = i
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b>>

(* A process can choose to leave the critical section. *)
LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<x, y, b>>

(* exit: Clear indicators y and b[i] and return to the non-critical section. *)
Exit(i) ==
    /\ pc[i] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x>>

(* The next-state relation is the disjunction of all possible actions. *)
Next ==
    \E i \in ProcessSet :
        \/ LeaveNCS(i)
        \/ L1(i)
        \/ L2(i)
        \/ L3(i)
        \/ L4(i)
        \/ L5(i)
        \/ L6(i)
        \/ L7(i)
        \/ LeaveCS(i)
        \/ Exit(i)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties of the specification.                                        *)
(***************************************************************************)

(* Safety: At most one process is in the critical section at any time. *)
MutualExclusion ==
    Cardinality({i \in ProcessSet : pc[i] = "cs"}) <= 1

(* Liveness: Every process that tries to enter the critical section
   (is at L1) will eventually do so (reach cs). This property is expected
   to hold only under the fairness assumptions defined below. *)
Liveness ==
    \A i \in ProcessSet : (pc[i] = "L1") ~> (pc[i] = "cs")

(* Conditional Liveness: If no process stays in its critical section forever,
   then every process trying to enter its critical section eventually succeeds. *)
ConditionalLiveness ==
    (\A i \in ProcessSet : [](pc[i] = "cs" => <>(pc[i] /= "cs"))) => Liveness

(***************************************************************************)
(* The fairness-enhanced specification.                                    *)
(***************************************************************************)

(* Weak fairness on each action of the entry and exit protocols for each process.
   This prevents a process from being stuck in the protocol if it is able to
   make progress. Note that LeaveNCS and LeaveCS are not included, allowing
   a process to remain in its non-critical or critical section indefinitely. *)
Fairness ==
    \A i \in ProcessSet :
        /\ WF_vars(L1(i))
        /\ WF_vars(L2(i))
        /\ WF_vars(L3(i))
        /\ WF_vars(L4(i))
        /\ WF_vars(L5(i))
        /\ WF_vars(L6(i))
        /\ WF_vars(L7(i))
        /\ WF_vars(Exit(i))

FairSpec == Spec /\ Fairness

=============================================================================