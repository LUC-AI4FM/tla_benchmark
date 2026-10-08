------------------------------ MODULE RingTermination ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS N, MaxPending

VARIABLES active, pending, globalDetected

(* Type invariant and bounds *)
TypeInv ==
    /\ active \in [1..N -> BOOLEAN]
    /\ pending \in [1..N -> Nat]
    /\ globalDetected \in BOOLEAN
    /\ \A i \in 1..N : pending[i] <= MaxPending

(* Initial state *)
Init ==
    /\ TypeInv
    /\ active = [i \in 1..N |-> TRUE]
    /\ pending = [i \in 1..N |-> 0]
    /\ globalDetected = FALSE

(* Termination predicate *)
Termination == 
    \A i \in 1..N : (NOT active[i]) /\ (pending[i] = 0)

(* Actions *)
NodeTerminate(i) ==
    /\ i \in 1..N
    /\ active[i] = TRUE
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    /\ globalDetected' = globalDetected

SendMessage(i) ==
    LET j == IF i < N THEN i+1 ELSE 1 IN
    /\ i \in 1..N
    /\ j \in 1..N
    /\ pending'[j] = pending[j] + 1
    /\ pending' = [pending EXCEPT ![j] = pending'[j]]
    /\ active' = active
    /\ globalDetected' = globalDetected

ReceiveMessage(i) ==
    /\ i \in 1..N
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
    /\ active' = active
    /\ globalDetected' = globalDetected

DetectTermination ==
    /\ Termination
    /\ globalDetected' = TRUE
    /\ active' = active
    /\ pending' = pending

Next == 
    \/ \E i \in 1..N : NodeTerminate(i)
    \/ \E i \in 1..N : SendMessage(i)
    \/ \E i \in 1..N : ReceiveMessage(i)
    \/ DetectTermination

(* Spec with weak fairness of DetectTermination *)
Spec == Init /\ [][Next]_vars /\ WF_DetectTermination

(* Safety invariant: detection implies termination *)
SafetyInv == globalDetected => Termination

(* Stability of detection once reached *)
StabilityInv == globalDetected => globalDetected'

(* Liveness: eventual detection after termination under weak fairness *)
Liveness ==
    Spec => [](Termination => <> globalDetected)

THEOREM SafetyTheorem == Spec => SafetyInv
THEOREM StabilityTheorem == Spec => StabilityInv
THEOREM LivenessTheorem == Liveness

=============================================================================