---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data,        \* abstract set of payloads
          MaxSubmit    \* bound on submissions, used only for model checking

ASSUME Data # {}
ASSUME MaxSubmit \in Nat

Bits == {0, 1}
Msgs == Data \X Bits

VARIABLES
    input,      \* pending-input queue filled by the environment
    sBit,       \* sender's control bit
    sAck,       \* last acknowledgment bit seen by the sender
    rBit,       \* receiver's control bit
    msg,        \* the message currently on the channel: <<payload, bit>>
    submitted,  \* history: all payloads submitted by the environment, in order
    delivered   \* history: all payloads delivered to the receiver, in order

vars == <<input, sBit, sAck, rBit, msg, submitted, delivered>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ input \in Seq(Data)
    /\ sBit \in Bits
    /\ sAck \in Bits
    /\ rBit \in Bits
    /\ msg \in Msgs
    /\ submitted \in Seq(Data)
    /\ delivered \in Seq(Data)

Init ==
    /\ input = << >>
    /\ sBit = 0
    /\ sAck = 0
    /\ rBit = 0
    /\ msg = << CHOOSE d \in Data : TRUE, 0 >>
    /\ submitted = << >>
    /\ delivered = << >>

-----------------------------------------------------------------------------
(* Environment: nondeterministically appends a new payload to the pending   *)
(* queue, but only when sender and receiver agree on the control bit.       *)
EnvAppend(d) ==
    /\ sBit = rBit
    /\ input' = Append(input, d)
    /\ submitted' = Append(submitted, d)
    /\ UNCHANGED <<sBit, sAck, rBit, msg, delivered>>

Env == \E d \in Data : EnvAppend(d)

(* Sender: once its previous message has been acknowledged, it takes the     *)
(* next queued payload, flips its control bit and transmits the pair.       *)
Send ==
    /\ sAck = sBit
    /\ input # << >>
    /\ sBit' = 1 - sBit
    /\ msg' = << Head(input), 1 - sBit >>
    /\ input' = Tail(input)
    /\ UNCHANGED <<sAck, rBit, submitted, delivered>>

(* Receiver: accepts the transmitted message when its bit differs from its  *)
(* own, adopts that bit and delivers the payload.                           *)
RcvMsg ==
    /\ msg[2] # rBit
    /\ rBit' = msg[2]
    /\ delivered' = Append(delivered, msg[1])
    /\ UNCHANGED <<input, sBit, sAck, msg, submitted>>

(* Sender learns the receiver's bit (acknowledgment). It may happen late,   *)
(* modelling the unreliable / delayed return path.                          *)
RcvAck ==
    /\ sAck # rBit
    /\ sAck' = rBit
    /\ UNCHANGED <<input, sBit, rBit, msg, submitted, delivered>>

(* Messages and acks may or may not be acted on immediately: any action may *)
(* be delayed arbitrarily long (stuttering), and actions interleave freely. *)
Next == Env \/ Send \/ RcvMsg \/ RcvAck

Fairness ==
    /\ WF_vars(Send)
    /\ WF_vars(RcvMsg)
    /\ WF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: every delivered payload was previously submitted.                *)
NoSpuriousDelivery ==
    \A i \in 1..Len(delivered) :
        \E j \in 1..Len(submitted) : delivered[i] = submitted[j]

(* No duplication: each submission is delivered at most once, i.e. there   *)
(* are never more deliveries than submissions.                              *)
NoDuplication == Len(delivered) <= Len(submitted)

(* Order preservation: the delivered sequence is a prefix of the submitted  *)
(* sequence.                                                                *)
OrderPreserved ==
    /\ Len(delivered) <= Len(submitted)
    /\ delivered = SubSeq(submitted, 1, Len(delivered))

Safety == TypeOK /\ NoSpuriousDelivery /\ NoDuplication /\ OrderPreserved

(* Liveness: if the environment eventually stops submitting, then           *)
(* eventually every submitted payload is delivered.                         *)
Liveness ==
    (<>[][UNCHANGED submitted]_vars) => <>[](delivered = submitted)

(* State constraint for bounded model checking with TLC.                    *)
StateConstraint == Len(submitted) <= MaxSubmit

THEOREM Spec => [](Safety)
THEOREM Spec => Liveness
=============================================================================