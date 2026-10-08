------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

VARIABLE counter

CONSTANT Max == 5

(* Initial condition: start at 1 *)
Init == counter = 1

(* Increment action: enabled while counter < Max *)
Increment == counter' = counter + 1 /\ counter <= Max - 1

(* Stay action: once at Max, remain there *)
Stay == counter' = counter /\ counter = Max

(* Next-state relation *)
Next == Increment \/ Stay

(* Specification with weak fairness on Increment *)
Spec == Init /\ [][Next]_counter /\ WF_Increment

(* Liveness property: eventually stabilize permanently at Max *)
Liveness == Spec => <> (counter = Max /\ [](counter = Max))

============================================================