---------------------------- MODULE spec ----------------------------

VARIABLE x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x /\ WF_x(Next)

(* Property that x is always true - this will be violated *)
Prop == []x

(* Additional properties for experimentation *)

(* State predicate asserting x equals true *)
AlwaysTrue == x = TRUE

(* Trivially always satisfied property *)
TriviallyTrue == TRUE

(* Expose the variable directly as a property *)
XValue == x

=============================================================================