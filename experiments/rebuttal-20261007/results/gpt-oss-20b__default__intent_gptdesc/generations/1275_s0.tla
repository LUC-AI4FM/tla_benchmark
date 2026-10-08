------------------------------ MODULE SimpleInitStutter ------------------------------
VARIABLE x

(* Initialization: nondeterministically choose 0 or 1, but must be < 1 *)
Init == \E v \in {0,1} : (v < 1) /\ x = v

(* After initialization, no state changes; stuttering action *)
Next == x' = x

(* Specification: initial condition followed by stuttering forever *)
Spec == Init /\ [][Next]_x

(* Safety invariant: variable always strictly less than 1 *)
Inv == [] (x < 1)

(* Liveness expectation: system remains stable, no other progress possible *)
Stable == [] (x' = x)

=============================================================================