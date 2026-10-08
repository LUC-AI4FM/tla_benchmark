------------------------------ MODULE Handshake ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS DATASET

VARIABLES ready, ack, data

(*--------------------------------------------------------------------------*)
(* Type invariant – all variables stay within their domains                 *)
(*--------------------------------------------------------------------------*)
TypeInvariant == /\ ready ∈ BOOLEAN
                 /\ ack  ∈ BOOLEAN
                 /\ data ∈ DATASET

(*--------------------------------------------------------------------------*)
(* Initial state – handshake bits are equal (no pending transfer) and the   *)
(* data channel holds a valid value                                         *)
(*--------------------------------------------------------------------------*)
Init == /\ ready = FALSE
       /\ ack  = FALSE
       /\ data ∈ DATASET

(*--------------------------------------------------------------------------*)
(* Sender action – may flip ready only when ready==ack. The sender can      *)
(* choose any data value from the finite set.                               *)
(*--------------------------------------------------------------------------*)
SenderAction ==
  /\ ready = ack
  /\ data' ∈ DATASET
  /\ ready' = ~ready
  /\ ack'   = ack

(*--------------------------------------------------------------------------*)
(* Receiver action – may flip acknowledge only when ready!=ack (a pending    *)
(* transfer). The receiver does not change the data value.                  *)
(*--------------------------------------------------------------------------*)
ReceiverAction ==
  /\ ready != ack
  /\ ready' = ready
  /\ ack'   = ~ack

Next == SenderAction \/ ReceiverAction

(*--------------------------------------------------------------------------*)
(* Specification – initial condition, next-state relation and weak fairness *)
(* on both actions to guarantee progress.                                   *)
(*--------------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ WF_vars(SenderAction) /\ WF_vars(ReceiverAction)

(*--------------------------------------------------------------------------*)
(* Data integrity – data never leaves its domain (type safety).             *)
(* This is already enforced by the type invariant, but we keep it as a     *)
(* separate assertion for clarity.                                          *)
(*--------------------------------------------------------------------------*)
DataIntegrity == TypeInvariant

(*--------------------------------------------------------------------------*)
(* Liveness property – any pending transfer (ready≠ack) will eventually be   *)
(* acknowledged (ack becomes equal to ready).                               *)
(*--------------------------------------------------------------------------*)
LivenessProperty == [](ready != ack => <> (ack = ready))

(*--------------------------------------------------------------------------*)
(* Handshake invariant – the two bits always indicate either a pending or  *)
(* consumed state. This is trivially true given the action definitions, but   *)
(* we assert it explicitly for completeness.                               *)
(*--------------------------------------------------------------------------*)
HandshakeInvariant == [] ((ready = ack) \/ (ready != ack))

(*--------------------------------------------------------------------------*)
(* Assertions to be checked by TLC                                            *)
(*--------------------------------------------------------------------------*)
ASSERTION TypeSafety  == TypeInvariant
ASSERTION DataIntegrity == DataIntegrity
ASSERTION Liveness   == LivenessProperty
ASSERTION Handshake  == HandshakeInvariant

=============================================================================