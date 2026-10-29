---------------------------- MODULE InstanceWrapper ----------------------------
(***************************************************************************)
(* A wrapper module that delegates its entire behavior to a reusable,      *)
(* separately defined module.  The local state variable `state` is bound   *)
(* to the parameter `x` of the instantiated module, so every behavior of   *)
(* this module is a behavior of the imported specification under that     *)
(* renaming.                                                               *)
(***************************************************************************)

    ------------------------------ MODULE Inner ------------------------------
    (***********************************************************************)
    (* The reusable module.  It defines a simple cyclic state machine on   *)
    (* the variable x, together with its safety and liveness properties.  *)
    (***********************************************************************)
    EXTENDS Naturals

    VARIABLE x

    States == 0..2

    TypeOK == x \in States

    Init == x = 0

    Next == x' = (x + 1) % 3

    Spec == Init /\ [][Next]_x /\ WF_x(Next)

    \* Safety: the state always stays within the allowed range.
    Safety == []TypeOK

    \* Liveness: the machine keeps cycling back to its initial state.
    Liveness == []<>(x = 0)
    ==========================================================================