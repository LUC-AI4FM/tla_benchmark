-------------------------------- MODULE SharedStateComposition --------------------------------
(***************************************************************************)
(* A shared integer state (state) that is updated through a reusable,      *)
(* black-box component specification. The component is instantiated in   *)
(* two ways:                                                               *)
(*   C : unparameterized, so its parameters bind by name to x and MaxVal   *)
(*   P : parameterized, with the component variable x bound to state       *)
(* The main system drives state using P's transitions and keeps the       *)
(* component's own copy x in lock-step. This lets us check that the two   *)
(* usages agree (compositional consistency) and that the range invariant  *)
(* holds for both.                                                         *)
(***************************************************************************)
EXTENDS Naturals

    ------------------------------ MODULE Component ------------------------------
    (***********************************************************************)
    (* Reusable component. It is treated as a black box: it is used only  *)
    (* through CInit, CNext, CSpec and CTypeOK. Every allowed transition   *)
    (* keeps x inside 0..MaxVal.                                           *)
    (***********************************************************************)
    CONSTANT MaxVal
    VARIABLE x

    CRange == 0..MaxVal

    CTypeOK == x \in CRange

    CInit == x \in CRange

    \* Any legal step moves x by at most one and never leaves CRange.
    CNext == /\ x' \in ((IF x = 0 THEN 0 ELSE x - 1)..(x + 1)) \cap CRange
             /\ x' # x

    CSpec == CInit /\ [][CNext]_x
    ==============================================================================