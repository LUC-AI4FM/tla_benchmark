------------------------------ MODULE OneVarBoolMachine ------------------------------
VARIABLE x

(* --algorithm Init
   BEGIN
      x := TRUE;
   END; *)

Init == x = TRUE

Next == (x' = ~x)

Stutter == (x' = x)

Spec == Init /\ []((Next) \/ Stutter)

Prop == x

===============================================================================