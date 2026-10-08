------------------------------ MODULE RingTermination ------------------------------
EXTENDS Naturals

CONSTANTS N

NodeSet == 0 .. N-1

VARIABLES active, terminationDetected

(*--------------------------------------------------------------------------*)
(* Initial condition *)
Init ==
    /\ active \in [NodeSet -> BOOLEAN]
    /\ (terminationDetected = FALSE
        \/ (terminationDetected = TRUE
            /\ ~Exists i \in NodeSet : active[i]))

(*--------------------------------------------------------------------------*)
(* Actions *)

Terminate(i) ==
    /\ i \in NodeSet
    /\ active[i]
    /\ LET newActive == [active EXCEPT ![i] = FALSE] IN
       /\ active' = newActive
       /\ IF (newActive = [j \in NodeSet |-> FALSE]) THEN
              terminationDetected' ∈ {terminationDetected, TRUE}
          ELSE
              terminationDetected' = terminationDetected

Wakeup(i,j) ==
    /\ i \in NodeSet
    /\ j \in NodeSet
    /\ active[i]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ terminationDetected' = terminationDetected

DetectTermination ==
    /\ ~Exists i \in NodeSet : active[i]
    /\ terminationDetected' = TRUE
    /\ active' = active

(*--------------------------------------------------------------------------*)
(* Next-state relation *)
Next ==
    ∃ i \in NodeSet : Terminate(i)
    \/ ∃ i,j \in NodeSet : Wakeup(i,j)
    \/ DetectTermination

(*--------------------------------------------------------------------------*)
(* Temporal specification with weak fairness on DetectTermination *)
Spec ==
    Init
    /\ [][Next]_<<active,terminationDetected>>
    /\ WF(DetectTermination)

(*--------------------------------------------------------------------------*)
(* Invariants and liveness properties *)

TDCorrect == [] (terminationDetected => ~Exists i \in NodeSet : active[i])

Quiescence ==
    []( (~Exists i \in NodeSet : active[i]) => [](~Exists i \in NodeSet : active[i]))

Liveness ==
    [] ((~Exists i \in NodeSet : active[i]) => <> terminationDetected)

============================================================================