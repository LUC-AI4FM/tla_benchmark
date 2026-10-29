---------------------------- MODULE AsyncFifoChannel ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Data

DataVal == {0, 1}

VARIABLES
    buf,
    full,
    rdy,
    ackd,
    got,
    sent

vars == <<buf, full, rdy, ackd, got, sent>>

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ buf  \in Data
    /\ full \in BOOLEAN
    /\ rdy  \in BOOLEAN
    /\ ackd \in BOOLEAN
    /\ got  \in Data
    /\ sent \in Data

Init ==
    /\ buf  \in Data
    /\ full = FALSE
    /\ rdy  = FALSE
    /\ ackd = FALSE
    /\ got  \in Data
    /\ sent = buf

-----------------------------------------------------------------------------
Offer(d) ==
    /\ ~full
    /\ ~ackd
    /\ buf'  = d
    /\ sent' = d
    /\ full' = TRUE
    /\ UNCHANGED <<rdy, ackd, got>>

Ready ==
    /\ ~rdy
    /\ ~ackd
    /\ rdy' = TRUE
    /\ UNCHANGED <<buf, full, ackd, got, sent>>

Accept ==
    /\ full
    /\ rdy
    /\ ~ackd
    /\ got'  = buf
    /\ ackd' = TRUE
    /\ rdy'  = FALSE
    /\ UNCHANGED <<buf, full, sent>>

Remove ==
    /\ full
    /\ ackd
    /\ full' = FALSE
    /\ ackd' = FALSE
    /\ UNCHANGED <<buf, rdy, got, sent>>

SenderStep   == \E d \in Data : Offer(d)
ReceiverStep == Ready \/ Accept

Next ==
    \/ SenderStep
    \/ Ready
    \/ Accept
    \/ Remove

Fairness ==
    /\ WF_vars(SenderStep)
    /\ WF_vars(Ready)
    /\ WF_vars(Accept)
    /\ WF_vars(Remove)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
CapacityOK ==
    Cardinality(IF full THEN {buf} ELSE {}) <= 1

AckOnlyOffered ==
    ackd => (full /\ got = buf /\ got = sent)

BufferedValueOffered ==
    full => buf = sent

SafetyInvariant ==
    /\ TypeInvariant
    /\ CapacityOK
    /\ AckOnlyOffered
    /\ BufferedValueOffered

BufferUnchanged ==
    [][(full /\ full') => (buf' = buf)]_vars

NoDuplicateDelivery ==
    [][(ackd /\ ~ackd') => ~full']_vars

NoOverwrite ==
    [][full => (full' \/ ackd)]_vars

-----------------------------------------------------------------------------
EagerDelivery ==
    \A d \in Data : (full /\ buf = d /\ rdy) ~> (ackd /\ got = d)

OfferedEventuallyCleared ==
    full ~> ~full

DeliveredAndAcked ==
    \A d \in Data : (full /\ buf = d) ~> (ackd /\ got = d)

SenderProgress ==
    []<>(full)

ReceiverProgress ==
    []<>(ackd)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => BufferUnchanged /\ NoDuplicateDelivery /\ NoOverwrite
THEOREM Spec => EagerDelivery /\ DeliveredAndAcked /\ OfferedEventuallyCleared
=============================================================================