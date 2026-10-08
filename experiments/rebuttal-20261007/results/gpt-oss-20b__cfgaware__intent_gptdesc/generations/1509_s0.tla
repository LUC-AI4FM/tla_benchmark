------------------------------ MODULE SimpleState ------------------------------
EXTENDS Naturals, TLC

CONSTANTS StateSet, Domain

VARIABLES state, f

(* ------------------------------------------------------------------ *)
(*  Initial condition: the system starts in an arbitrary value from   *)
(*  StateSet and the mapping f is a total function from Domain to    *)
(*  StateSet that contains at least one index whose image equals     *)
(*  the current state.                                               *)
(* ------------------------------------------------------------------ *)

Init == /\ state \in StateSet
        /\ f \in [Domain -> StateSet]
        /\ \E i \in Domain : f[i] = state

(* ------------------------------------------------------------------ *)
(*  Next-state relation: the system may nondeterministically choose   *)
(*  any value from StateSet (including the current one) for the new   *)
(*  state and assign an arbitrary total function to f that still     *)
(*  satisfies the invariant.                                         *)
(* ------------------------------------------------------------------ *)

Next == /\ state' \in StateSet
        /\ f' \in [Domain -> StateSet]
        /\ \E i \in Domain : f'[i] = state'

(* ------------------------------------------------------------------ *)
(*  Invariant: at every reachable state there exists an index in     *)
(*  Domain whose mapped value equals the current state.               *)
(* ------------------------------------------------------------------ *)

Inv == \E i \in Domain : f[i] = state

(* ------------------------------------------------------------------ *)
(*  Specification: initial condition followed by arbitrary steps      *)
(*  satisfying Next.                                                 *)
(* ------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_<<state,f>>

(* ------------------------------------------------------------------ *)
(*  Safety property: the invariant holds in all reachable states.   *)
(* ------------------------------------------------------------------ *)

Safety == [] Inv

(* ------------------------------------------------------------------ *)
(*  Liveness property: the system never deadlocks – there is always a *)
(*  possible transition (here, Next is always enabled).               *)
(* ------------------------------------------------------------------ *)

Liveness == [] <> Next

===============================================================================