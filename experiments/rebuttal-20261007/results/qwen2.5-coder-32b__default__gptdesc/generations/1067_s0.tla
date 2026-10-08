------------------------------- MODULE TerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node

VARIABLES state, detected

(* --algorithm termination-detection
variables 
    state = [n \in Node |-> "active"],  (* "active" or "inactive" *)
    detected = FALSE;                   (* global termination detection flag *)

process (node \in Node)
begin
    while TRUE do
        if state[node] = "active" then
            either
                /\ await(\E m \in Node : state[m] = "active")
                /\ with (m \in Node : state[m] = "active") do
                    state[node] := "inactive"
            or
                /\ await(\E m \in Node : state[m] = "inactive" /\ m # node)
                /\ with (m \in Node : state[m] = "inactive" /\ m # node) do
                    state[m] := "active"
        end if;
        await(detected);
    od;
end process;

process detection
begin
    while TRUE do
        await(\A n \in Node : state[n] = "inactive");
        detected := TRUE;
    od;
end process;

Init == /\ state \in [Node -> {"active", "inactive"}]
        /\ detected = FALSE

Next == \/ \E node \in Node :
                (state[node] = "active" /\
                 \/ \/ \E m \in Node : state[m] = "active"
                        /\ state' = [state EXCEPT ![node] = "inactive"]
                   \/ \E m \in Node : state[m] = "inactive" /\ m # node
                        /\ state' = [state EXCEPT ![m] = "active"])
            \/ detected
               /\ \A n \in Node : state[n] = "inactive"
               /\ detected'

Spec == Init /\ [][Next]_<<state, detected>>

TerminationDetected == <>[](detected)

Quiescence == <>(\A n \in Node : state[n] = "inactive")

FairDetection == WF_<<>>_(<>[](\A n \in Node : state[n] = "inactive"))

Correctness == Spec /\ TerminationDetected /\ Quiescence /\ FairDetection

=============================================================================