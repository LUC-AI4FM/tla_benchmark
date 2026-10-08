\*======================================================================
\*  Module: AsyncBuffer
\*
\*  A simple asynchronous interface between a sender and a receiver
\*  communicating over a one-place buffer.  The protocol uses a ready/
\*  acknowledge handshake with single‑bit toggle signals.
\*
\*  Exported names:
\*      Spec          -- the complete specification
\*      TypeInvariant -- invariant that data is in DATASET and both
\*                      ready and ack are bits {0,1}
\*======================================================================
\* MODULE AsyncBuffer
MODULE AsyncBuffer

EXTENDS Naturals, Sequences

CONSTANTS DataSet

VARIABLES data, ready, ack

(*--------------------------------------------------------------------
  Type invariant:  data ∈ DATASET and ready/ack are single bits.
--------------------------------------------------------------------*)
TypeInvariant == /\ data \in DataSet
                 /\ ready \in {0,1}
                 /\ ack   \in {0,1}

(*--------------------------------------------------------------------
  Initial state:  type constraints hold and ready = ack.
--------------------------------------------------------------------*)
Init == TypeInvariant /\ (ready = ack)

(*--------------------------------------------------------------------
  Sender step:  can transmit only when ready = ack.  It updates data
  and toggles ready.
--------------------------------------------------------------------*)
SenderStep ==
  /\ ready = ack
  /\ data' \in DataSet
  /\ ready' = 1 - ready      (* toggle *)
  /\ ack'   = ack

(*--------------------------------------------------------------------
  Receiver step:  can accept only when ready ≠ ack.  It toggles ack
  to match ready.
--------------------------------------------------------------------*)
ReceiverStep ==
  /\ ready # ack
  /\ ready' = ready
  /\ ack'   = ready          (* now equal *)
  /\ data'  = data

(*--------------------------------------------------------------------
  Stuttering step:  all variables unchanged.
--------------------------------------------------------------------*)
Stutter ==
  /\ data'  = data
  /\ ready' = ready
  /\ ack'   = ack

(*--------------------------------------------------------------------
  Next action:  one of the three possibilities.
--------------------------------------------------------------------*/
Next == SenderStep \/ ReceiverStep \/ Stutter

(*--------------------------------------------------------------------
  The complete specification.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<data,ready,ack>>

EXPORTS Spec, TypeInvariant
===============================================================================