------------------------------ MODULE ReliableBroadcast ------------------------------
(***************************************************************************)
(* Reliable broadcast for N processes under crash and omission faults.    *)
(*                                                                         *)
(*  - Processes 1..N. Each process p may initiate one broadcast instance, *)
(*    identified by p, with a value taken from Values.                     *)
(*  - Crash faults: at most T processes crash permanently.                 *)
(*  - Communication faults: messages may be delayed and reordered. They   *)
(*    may be duplicated through retransmission. They may be omitted       *)
(*    (dropped), with at most F omissions in total. Messages are never    *)
(*    corrupted. A sender keeps retransmitting until the receiver         *)
(*    acknowledges receipt. The ack is abstracted as atomic with the      *)
(*    receipt.                                                            *)
(*  - No malicious (Byzantine) behaviour is modelled. F is the budget of  *)
(*    benign omission faults.                                             *)
(*                                                                         *)
(* Protocol (eager relay): a process that learns a value for an instance  *)
(* (as broadcaster, or on the first receipt of a message for that         *)
(* instance) delivers it at once. It then relays the value to every other *)
(* process until acknowledged.                                            *)
(*                                                                         *)
(* A process may irrevocably decide Bot ("nothing will be delivered") for  *)
(* an instance b only under all of these conditions:                      *)
(*  - the broadcaster b has crashed;                                      *)
(*  - no live process holds a value for b;                                *)
(*  - no message for b is in transit to a live process.                   *)
(* This is a perfect-failure-detector style oracle.                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N \in Nat \ {0}
ASSUME T \in Nat
ASSUME F \in Nat

Procs  == 1..N
Values == {0, 1}
None   == -1          \* not yet decided / not yet broadcast
Bot    == -2          \* irrevocably decided "no value will be delivered"

Msg == [from : Procs, to : Procs, inst : Procs, val : Values]

VARIABLES
    crashed,   \* set of crashed processes
    bval,      \* bval[b] : value broadcast by b (ghost), or None
    dec,       \* dec[p][b] : value delivered by p for instance b, None, or Bot
    msgs,      \* messages currently in transit
    acked,     \* acked[p][b] : processes that acknowledged p's relay for b
    drops      \* number of message omissions so far

vars == <<crashed, bval, dec, msgs, acked, drops>>

Alive == Procs \ crashed

TypeOK ==
    /\ crashed \subseteq Procs
    /\ bval \in [Procs -> Values \cup {None}]
    /\ dec \in [Procs -> [Procs -> Values \cup {None, Bot}]]
    /\ msgs \subseteq Msg
    /\ acked \in [Procs -> [Procs -> SUBSET Procs]]
    /\ drops \in 0..F

Init ==
    /\ crashed = {}
    /\ bval = [b \in Procs |-> None]
    /\ dec = [p \in Procs |-> [b \in Procs |-> None]]
    /\ msgs = {}
    /\ acked = [p \in Procs |-> [b \in Procs |-> {}]]
    /\ drops = 0

\* Process p initiates its broadcast with value v and delivers it to itself.
Broadcast(p, v) ==
    /\ p \in Alive
    /\ bval[p] = None
    /\ bval' = [bval EXCEPT ![p] = v]
    /\ dec' = [dec EXCEPT ![p][p] = v]
    /\ UNCHANGED <<crashed, msgs, acked, drops>>

\* Process p (re)sends its value for instance b to q, until q acknowledges.
Send(p, q, b) ==
    /\ p \in Alive
    /\ p # q
    /\ dec[p][b] \in Values
    /\ q \notin acked[p][b]
    /\ LET m == [from |-> p, to |-> q, inst |-> b, val |-> dec[p][b]]
       IN  /\ m \notin msgs
           /\ msgs' = msgs \cup {m}
    /\ UNCHANGED <<crashed, bval, dec, acked, drops>>

\* Process q receives a message from p for instance b.
Receive(q, p, b) ==
    /\ q \in Alive
    /\ \E m \in msgs :
         /\ m.to = q /\ m.from = p /\ m.inst = b
         /\ msgs' = msgs \ {m}
         /\ acked' = [acked EXCEPT ![p][b] = @ \cup {q}]
         /\ dec' = IF dec[q][b] = None
                     THEN [dec EXCEPT ![q][b] = m.val]
                     ELSE dec
    /\ UNCHANGED <<crashed, bval, drops>>

\* Omission fault: a message in transit is lost.
Drop(m) ==
    /\ drops < F
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ drops' = drops + 1
    /\ UNCHANGED <<crashed, bval, dec, acked>>

\* Crash fault: process p stops forever.
Crash(p) ==
    /\ p \in Alive
    /\ Cardinality(crashed) < T
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<bval, dec, msgs, acked, drops>>

\* Process q irrevocably determines that no value will be delivered for b.
Abandon(q, b) ==
    /\ q \in Alive
    /\ b \in crashed
    /\ dec[q][b] = None
    /\ \A m \in msgs : m.inst = b => m.to \in crashed
    /\ \A r \in Alive : dec[r][b] \notin Values
    /\ dec' = [dec EXCEPT ![q][b] = Bot]
    /\ UNCHANGED <<crashed, bval, msgs, acked, drops>>

\* Terminal stuttering once every live process has decided every instance.
Done ==
    /\ \A p \in Alive, b \in Procs : dec[p][b] # None
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs, v \in Values : Broadcast(p, v)
    \/ \E p, q, b \in Procs : Send(p, q, b)
    \/ \E p, q, b \in Procs : Receive(q, p, b)
    \/ \E m \in msgs : Drop(m)
    \/ \E p \in Procs : Crash(p)
    \/ \E q, b \in Procs : Abandon(q, b)
    \/ Done

Fairness ==
    /\ \A p \in Procs : WF_vars(\E v \in Values : Broadcast(p, v))
    /\ \A p, q, b \in Procs : WF_vars(Send(p, q, b))
    /\ \A p, q, b \in Procs : WF_vars(Receive(q, p, b))
    /\ \A q, b \in Procs : WF_vars(Abandon(q, b))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

\* A delivered value is always the value actually broadcast by the broadcaster.
Integrity ==
    \A p, b \in Procs :
        dec[p][b] \in Values => dec[p][b] = bval[b]

\* No two processes deliver different values for the same instance.
AgreementSafety ==
    \A p, q, b \in Procs :
        (dec[p][b] \in Values /\ dec[q][b] \in Values) => dec[p][b] = dec[q][b]

\* No live process decides Bot while another live process delivered a value.
NoBotConflict ==
    \A p, q, b \in Procs :
        (p \in Alive /\ q \in Alive) =>
            ~(dec[p][b] \in Values /\ dec[q][b] = Bot)

CrashBound == Cardinality(crashed) <= T

SafetyInv == TypeOK /\ Integrity /\ AgreementSafety /\ NoBotConflict /\ CrashBound

\* Decisions are irrevocable: at most one decision per process per instance.
DecisionStable ==
    [][\A p, b \in Procs : dec[p][b] # None => dec'[p][b] = dec[p][b]]_vars

-----------------------------------------------------------------------------
(* Liveness *)

Correct(p) == [](p \notin crashed)

Validity ==
    \A p, q \in Procs :
        (Correct(p) /\ Correct(q)) =>
            \A v \in Values : [](bval[p] = v => <>(dec[q][p] = v))

AgreementLiveness ==
    \A p, q, b \in Procs :
        (Correct(p) /\ Correct(q)) =>
            \A v \in Values : [](dec[p][b] = v => <>(dec[q][b] = v))

Termination ==
    \A q, b \in Procs :
        Correct(q) => <>(dec[q][b] # None)

Liveness == Validity /\ AgreementLiveness /\ Termination

THEOREM Spec => [](SafetyInv) /\ DecisionStable /\ Liveness

=============================================================================