--------------------------- MODULE ABSpec ---------------------------
EXTENDS Integers

CONSTANT Data

(***************************************************************************
--algorithm ABSpec {
   variables msgA \in [data : Data, bit : {0,1}], msgB = msgA ;
   fair process (A = "A") {
     a: while (TRUE) {
          await msgA.bit = msgB.bit ;
          with (d \in Data) { msgA := [data |-> d, bit |-> 1 - msgA.bit] }
        }
   }
   fair process (B = "B") {
     b: while (TRUE) {
          await msgA.bit # msgB.bit ;
          msgB := msgA
        }
   }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES msgA, msgB

vars == << msgA, msgB >>

ProcSet == {"A"} \cup {"B"}

Init == /\ msgA \in [data : Data, bit : {0,1}]
        /\ msgB = msgA

A == /\ msgA.bit = msgB.bit
     /\ \E d \in Data : msgA' = [data |-> d, bit |-> 1 - msgA.bit]
     /\ msgB' = msgB

B == /\ msgA.bit # msgB.bit
     /\ msgB' = msgA
     /\ msgA' = msgA

Next == A \/ B

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

-----------------------------------------------------------------------------
Msg == [data : Data, bit : {0,1}]

TypeOK == /\ msgA \in Msg
          /\ msgB \in Msg

(* When the bits agree, B has received exactly what A sent. *)
Consistency == (msgA.bit = msgB.bit) => (msgA = msgB)

(* Every message sent by A is eventually received by B. *)
Delivery == \A m \in Msg : (msgA = m) ~> (msgB = m)

(* Both processes make progress infinitely often. *)
Progress == []<>(msgA.bit = msgB.bit) /\ []<>(msgA.bit # msgB.bit)
=============================================================================