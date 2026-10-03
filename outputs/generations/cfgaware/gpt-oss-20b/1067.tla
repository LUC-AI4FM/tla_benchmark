------------------------------ MODULE RingTermination ------------------------------
EXTENDS Naturals

CONSTANTS Node

VARIABLES active, detected

(* Type invariant *)
TypeInvariant == active \in [Node -> BOOLEAN] /\ detected \in BOOLEAN

Init ==
  /\ active = [n \in Node |-> TRUE]
  /\ detected = FALSE

Terminate(n) ==
  /\ n \in Node
  /\ active[n] = TRUE
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ detected' = detected

WakeUp(n, m) ==
  /\ n \in Node
  /\ m \in Node
  /\ active[n] = TRUE
  /\ active[m] = FALSE
  /\ active' = [active EXCEPT ![m] = TRUE]
  /\ detected' = detected

Detect ==
  /\ (∀ n ∈ Node : active[n] = FALSE)
  /\ detected' = TRUE
  /\ active' = active

Next ==
  \/ (∃ n \in Node : Terminate(n))
  \/ (∃ n,m \in Node : WakeUp(n, m))
  \/ Detect

Spec == Init /\ [][Next]_<<active, detected>> /\ WF_vars(Detect)

Correctness == detected => ∀ n ∈ Node : active[n] = FALSE

Quiescent == ∀ n ∈ Node : ¬active[n]

Liveness == []<> detected
====