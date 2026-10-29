---------------------------- MODULE AsynchChannel ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES
    val,      \* data value currently on the channel
    rdy,      \* ready bit, toggled by the sender
    ack,      \* acknowledge bit, toggled by the receiver
    sentLog,  \* history: sequence of all values sent
    rcvdLog   \* history: sequence of all values received

chan == <<val, rdy, ack>>
vars == <<val, rdy, ack, sentLog, rcvdLog>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}
    /\ sentLog \in Seq(Data)
    /\ rcvdLog \in Seq(Data)

Init ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy
    /\ sentLog = << >>
    /\ rcvdLog = << >>

\* Sender may send only after the previous value has been acknowledged
Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = 1 - rdy
    /\ sentLog' = Append(sentLog, val')
    /\ UNCHANGED <<ack, rcvdLog>>

\* Receiver may consume only when new data is ready
Rcv ==
    /\ rdy # ack
    /\ ack' = 1 - ack
    /\ rcvdLog' = Append(rcvdLog, val)
    /\ UNCHANGED <<val, rdy, sentLog>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars /\ WF_vars(Send) /\ WF_vars(Rcv)

-----------------------------------------------------------------------------
\* Safety properties

\* Received values are exactly the sent values, in order, each once
NoDuplication ==
    /\ Len(rcvdLog) <= Len(sentLog)
    /\ rcvdLog = SubSeq(sentLog, 1, Len(rcvdLog))

\* At most one value is outstanding; nothing is skipped
NoDataLoss ==
    /\ Len(sentLog) - Len(rcvdLog) \in {0, 1}
    /\ (Len(sentLog) = Len(rcvdLog)) <=> (rdy = ack)

\* While data is pending, the channel holds exactly the last unreceived value
ProperSynchronization ==
    (rdy # ack) => /\ Len(sentLog) = Len(rcvdLog) + 1
                   /\ val = sentLog[Len(sentLog)]

\* The sender never overwrites unacknowledged data
NoOverwrite ==
    [][(rdy # ack) => (val' = val /\ rdy' = rdy)]_vars

Invariants ==
    /\ TypeOK
    /\ NoDuplication
    /\ NoDataLoss
    /\ ProperSynchronization

-----------------------------------------------------------------------------
\* Liveness properties

\* Every value sent is eventually received
EventuallyReceived == (rdy # ack) ~> (rdy = ack)

\* Every sent message (by position) is eventually received
AllSentReceived ==
    \A n \in Nat : (Len(sentLog) >= n) ~> (Len(rcvdLog) >= n)

\* Communication keeps making progress
Progress == []<>(rdy # ack) /\ []<>(rdy = ack)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => NoOverwrite
THEOREM Spec => EventuallyReceived /\ Progress
=============================================================================