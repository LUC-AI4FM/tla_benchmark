---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* Model-checking helper module over Session4.                             *)
(* It defines only constant-valued operators used to override the          *)
(* constants and definitions of Session4 during model checking.            *)
(* There are no variables, no actions, no temporal formula and no          *)
(* explicit safety or liveness properties.                                 *)
(***************************************************************************)
EXTENDS Session4, Integers, TLC

\* A distinguished minimum integer value.
const_MinValue == -1000

\* The union over l \in 0..5 of the sets of functions (tuples) mapping
\* 1..l to the shifted range (l+1)..(2*l).
const_Tuples ==
    UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

=============================================================================