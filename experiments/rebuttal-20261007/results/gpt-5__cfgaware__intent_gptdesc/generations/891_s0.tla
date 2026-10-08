------------------------------- MODULE Handshake -------------------------------
EXTENDS Naturals, Sequences, TLC

(*
Asynchronous single-bit handshake between a sender and a receiver.
The data domain is a fixed finite set DATA provided by the model.
*)

CONSTANT DATA

ASSUME DataAssumptions ==
    /\ DATA # {}
    /\ FiniteSet(DATA)

VARIABLES r, a, d, offer, sent, recv

vars == << r, a, d, offer, sent, recv >>

(*
r, a: Boolean ready/acknowledge bits
d: current value on the data channel (can change at any time)
offer: the value latched by the sender at the instant it toggles r
sent: sequence of values produced by the sender (one per ready toggle)
recv: sequence of values consumed by the receiver (one per ack toggle)
*)

Init ==
    /\ r \in BOOLEAN
    /\ a = r
    /\ d \in DATA
    /\ offer = d
    /\ sent = << >>
    /\ recv = << >>

Send ==
    /\ r = a
    /\ \E v \in DATA:
         /\ r' = ~r
         /\ a' = a
         /\ d' = v
         /\ offer' = v
         /\ sent' = Append(sent, v)
         /\ recv' = recv

ChangeData ==
    /\ \E v \in DATA:
         /\ d' = v
         /\ UNCHANGED << r, a, offer, sent, recv >>

Rcv ==
    /\ r # a
    /\ a' = r
    /\ recv' = Append(recv, offer)
    /\ UNCHANGED << r, d, offer, sent >>

Next ==
    Send \/ ChangeData \/ Rcv

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Rcv)

(*
Type safety: bits are Booleans, data/offer are in DATA, histories are sequences
over DATA.
*)
TypeInvariant ==
    /\ r \in BOOLEAN
    /\ a \in BOOLEAN
    /\ d \in DATA
    /\ offer \in DATA
    /\ IsSeq(sent) /\ IsSeq(recv)
    /\ \A i \in DOMAIN sent : sent[i] \in DATA
    /\ \A i \in DOMAIN recv : recv[i] \in DATA

(*
Data integrity: delivered values are exactly those produced by the sender, in
order and without corruption; recv is always a prefix of sent.
*)
DataIntegrity ==
    /\ Len(recv) <= Len(sent)
    /\ recv = SubSeq(sent, 1, Len(recv))

(*
Handshake-bit meaning: r=a iff no transfer is pending; r#a iff exactly one
transfer is pending, and offer is the unique outstanding value.
*)
PendingBitInvariant ==
    /\ (r = a) <=> (Len(sent) = Len(recv))
    /\ (r # a) <=> (Len(sent) = Len(recv) + 1)
    /\ (r # a) => offer = sent[Len(sent)]

(*
Liveness: every send is eventually acknowledged; equivalently, whenever a
transfer is pending (r # a), eventually it is consumed (r = a).
*)
SendEvent == Send
AckEvent  == Rcv

AckEventuallyFollowsSend ==
    [] (SendEvent => <> AckEvent)

NoPendingStuck ==
    [] (r # a => <> (r = a))

(*
Optional theorems documenting intended properties under Spec.
These are not checked by SANY but can be model-checked by TLC.
*)
THEOREM Spec => []TypeInvariant
THEOREM Spec => [](DataIntegrity /\ PendingBitInvariant)
THEOREM Spec => AckEventuallyFollowsSend
THEOREM Spec => NoPendingStuck

===============================================================================