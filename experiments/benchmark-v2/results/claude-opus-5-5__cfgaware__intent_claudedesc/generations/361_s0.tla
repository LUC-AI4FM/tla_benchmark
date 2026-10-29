---- MODULE LargeInitStateSpace ----
EXTENDS Naturals

VARIABLES x, y, z

vars == <<x, y, z>>

(* Three independent parameters drawn from distinct ranges.
   Cartesian product size: 100 * 60 * 50 = 300,000 initial states. *)
XRange == 0..99
YRange == 100..159
ZRange == 200..249

Init ==
    /\ x \in XRange
    /\ y \in YRange
    /\ z \in ZRange

(* The system is static: no state changes after initialization. *)
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in XRange
    /\ y \in YRange
    /\ z \in ZRange

(* Trivially satisfied invariant. *)
Inv == TRUE

====