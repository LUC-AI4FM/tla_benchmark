------------------------------ MODULE CounterDemo ------------------------------
EXTENDS Naturals

CONSTANT Limit

VARIABLE counter

(*--------------------------------------------------------------------------*)
(*  Initial state: the counter starts at zero.                               *)
(*--------------------------------------------------------------------------*)
Init == counter = 0

(*--------------------------------------------------------------------------*)
(*  Next-state relation: if the counter is below the limit, increment it;   *)
(*  otherwise keep it unchanged (stuttering).                              *)
(*--------------------------------------------------------------------------*)
Next ==
  IF counter < Limit THEN
    counter' = counter + 1
  ELSE
    counter' = counter

(*--------------------------------------------------------------------------*)
(*  Temporal specification: start in Init and always obey Next.             *)
(*--------------------------------------------------------------------------*)
Spec == Init /\ []Next

=============================================================================