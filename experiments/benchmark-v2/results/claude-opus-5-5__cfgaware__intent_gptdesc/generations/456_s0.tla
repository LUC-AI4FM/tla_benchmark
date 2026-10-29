---------------------------- MODULE SharedValueChannel ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Reusable sender/receiver protocol module. The datum `value` and the     *)
(* handshake flag `full` are external parameters that the instantiating    *)
(* system binds to its own state.                                          *)
(***************************************************************************)
---------------------------- MODULE Channel ----------------------------
CONSTANT Data
VARIABLES value, full

ChanTypeOK == /\ value \in Data
              /\ full \in BOOLEAN

ChanInit == /\ value \in Data
            /\ full = FALSE

\* Sender may only write when the slot is empty (no conflicting overwrite).
Send(v) == /\ ~full
           /\ v \in Data
           /\ value' = v
           /\ full' = TRUE

\* Receiver may only take a value that has been provided.
Receive == /\ full
           /\ full' = FALSE
           /\ UNCHANGED value

ChanNext == (\E v \in Data : Send(v)) \/ Receive

ChanSpec == ChanInit /\ [][ChanNext]_<<value, full>>

\* Correctness invariant of the protocol: types are always respected.
ChanInv == ChanTypeOK
=========================================================================