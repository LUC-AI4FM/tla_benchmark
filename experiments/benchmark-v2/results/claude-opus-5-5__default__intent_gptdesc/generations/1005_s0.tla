---------------------------- MODULE ReliableBroadcast ----------------------------
(***************************************************************************)
(* Crash-tolerant reliable broadcast over lossy, asynchronous channels.    *)
(*                                                                         *)
(* Processes 1..N. Each process b may initiate one broadcast instance,     *)
(* identified by b. The protocol is echo/relay based:                      *)
(*   - The broadcaster delivers its value and sends it to all others.      *)
(*   - A process delivers on the first message it receives for an          *)
(*     instance and relays it to all others.                               *)
(*   - Live processes periodically retransmit what they have sent, which   *)
(*     masks transient message omission.                                   *)
(*                                                                         *)
(* Faults:                                                                 *)
(*   - Crash: at most T processes stop permanently.                        *)
(*   - Channel faults: messages may be delayed, reordered, duplicated      *)
(*     (by retransmission) or lost (omission). They are never corrupted.   *)
(*   - F is the overall fault budget the system is parameterized by.       *)
(*     Byzantine behaviour beyond crash/omission is NOT modeled, and we    *)
(*     require T <= F < N.                                                 *)
(*                                                                         *)
(* "No value will be delivered" for instance b is decided by an            *)
(* oracle-style perfect failure detector (action GiveUp). It is enabled    *)
(* only when b has crashed and the instance is provably dead among the     *)
(* live processes. That condition is stable once it holds.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,          \* number of processes
    T,          \* maximum number of crash failures
    F,          \* overall fault budget (Byzantine bound; only crash/omission modeled)
    Values,     \* set of values that may be broadcast
    Nil,        \* "nothing yet"
    NoDeliver   \* irrevocable decision: nothing will be delivered

ASSUME
    /\ N \in Nat \ {0}
    /\ T \in Nat /\ F \in Nat
    /\ T <= F /\ F < N
    /\ Values # {}
    /\ Nil \notin Values /\ NoDeliver \notin Values /\ Nil # NoDeliver

Procs == 1..N

Msgs == [from : Procs, to : Procs, inst : Procs, val : Values]

VARIABLES
    crashed,  \* set of crashed processes (monotone)
    bval,     \* bval[b] : value broadcast by b, or Nil
    dlv,      \* dlv[p][b] : value delivered by p for instance b, Nil, or NoDeliver
    sent,     \* every message ever sent (sender's retransmission buffer)
    net       \* messages currently in transit (subset of sent)

vars == <<crashed, bval, dlv, sent, net>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ crashed \subseteq Procs
    /\ bval \in [Procs -> Values \cup {Nil}]
    /\ dlv \in [Procs -> [Procs -> Values \cup {Nil, NoDeliver}]]
    /\ sent \subseteq Msgs
    /\ net \subseteq sent

Alive == Procs \ crashed

Init ==
    /\ crashed = {}
    /\ bval = [b \in Procs |-> Nil]
    /\ dlv = [p \in Procs |-> [b \in Procs |-> Nil]]
    /\ sent = {}
    /\ net = {}

-----------------------------------------------------------------------------
(* Process b initiates its broadcast instance with value v. *)
Broadcast(b, v) ==
    /\ b \in Alive
    /\ bval[b] = Nil
    /\ dlv[b][b] = Nil
    /\ LET out == {[from |-> b, to |-> q, inst |-> b, val |-> v] : q \in Procs \ {b}}
       IN /\ bval' = [bval EXCEPT ![b] = v]
          /\ dlv' = [dlv EXCEPT ![b][b] = v]
          /\ sent' = sent \cup out
          /\ net' = net \cup out
    /\ UNCHANGED crashed

(* Process p receives message m. It delivers on first receipt and relays.  *)
(* Duplicates are consumed without effect.                                 *)
Receive(p, m) ==
    /\ p \in Alive
    /\ m \in net
    /\ m.to = p
    /\ IF dlv[p][m.inst] = Nil
         THEN LET relay == {[from |-> p, to |-> q, inst |-> m.inst, val |-> m.val]
                              : q \in Procs \ {p}}
              IN /\ dlv' = [dlv EXCEPT ![p][m.inst] = m.val]
                 /\ sent' = sent \cup relay
                 /\ net' = (net \ {m}) \cup relay
         ELSE /\ net' = net \ {m}
              /\ UNCHANGED <<dlv, sent>>
    /\ UNCHANGED <<crashed, bval>>

(* A live process retransmits everything it has sent that is not in transit. *)
Retransmit(p) ==
    /\ p \in Alive
    /\ \E m \in sent : m.from = p /\ m \notin net
    /\ net' = net \cup {m \in sent : m.from = p}
    /\ UNCHANGED <<crashed, bval, dlv, sent>>

(* Channel omission: a message in transit is lost. *)
Lose(m) ==
    /\ m \in net
    /\ net' = net \ {m}
    /\ UNCHANGED <<crashed, bval, dlv, sent>>

(* Crash failure: the process stops taking steps forever. *)
Crash(p) ==
    /\ p \in Alive
    /\ Cardinality(crashed) < T
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<bval, dlv, sent, net>>

(* Instance b is dead: b crashed, no live process delivered a value for b,   *)
(* and no message for b is in transit to a live process. Every live sender   *)
(* of a b-message has delivered for b, so nothing can be retransmitted.      *)
(* The condition is therefore stable.                                        *)
InstanceDead(b) ==
    /\ b \in crashed
    /\ \A q \in Alive : dlv[q][b] \notin Values
    /\ ~\E m \in net : m.inst = b /\ m.to \in Alive

(* Perfect failure detector: irrevocably decide that nothing is delivered. *)
GiveUp(p, b) ==
    /\ p \in Alive
    /\ dlv[p][b] = Nil
    /\ InstanceDead(b)
    /\ dlv' = [dlv EXCEPT ![p][b] = NoDeliver]
    /\ UNCHANGED <<crashed, bval, sent, net>>

Next ==
    \/ \E b \in Procs, v \in Values : Broadcast(b, v)
    \/ \E p \in Procs, m \in Msgs : Receive(p, m)
    \/ \E p \in Procs : Retransmit(p)
    \/ \E m \in Msgs : Lose(m)
    \/ \E p \in Procs : Crash(p)
    \/ \E p, b \in Procs : GiveUp(p, b)

(* Fairness assumptions:                                                    *)
(*  - Fair-lossy channels: a message that is sent infinitely often (through *)
(*    retransmission) is eventually received. This is strong fairness of    *)
(*    Receive.                                                              *)
(*  - Live processes keep retransmitting. This is weak fairness of          *)
(*    Retransmit.                                                           *)
(*  - The failure-detector decision is eventually taken. This is weak       *)
(*    fairness of GiveUp.                                                   *)
Fairness ==
    /\ \A p \in Procs, m \in Msgs : SF_vars(Receive(p, m))
    /\ \A p \in Procs : WF_vars(Retransmit(p))
    /\ \A p, b \in Procs : WF_vars(GiveUp(p, b))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* SAFETY *)

CrashBound == Cardinality(crashed) <= T

(* Integrity: every delivered value is the value actually broadcast. *)
Integrity ==
    \A p, b \in Procs :
        dlv[p][b] \in Values => (bval[b] # Nil /\ dlv[p][b] = bval[b])

(* Integrity: at most one value per instance, and decisions are irrevocable. *)
DeliverOnce ==
    [][\A p, b \in Procs : dlv[p][b] # Nil => dlv'[p][b] = dlv[p][b]]_vars

(* Agreement (safety): no two processes deliver different values. *)
AgreementSafety ==
    \A p, q, b \in Procs :
        (dlv[p][b] \in Values /\ dlv[q][b] \in Values) => dlv[p][b] = dlv[q][b]

(* Live processes never disagree between "delivered" and "nothing delivered". *)
NoConflictingDecision ==
    \A p, q \in Alive, b \in Procs :
        ~(dlv[p][b] \in Values /\ dlv[q][b] = NoDeliver)

(* A process gives up only for a crashed broadcaster. *)
GiveUpOnlyIfCrashed ==
    \A p, b \in Procs : dlv[p][b] = NoDeliver => b \in crashed

Safety ==
    /\ TypeOK
    /\ CrashBound
    /\ Integrity
    /\ AgreementSafety
    /\ NoConflictingDecision
    /\ GiveUpOnlyIfCrashed

-----------------------------------------------------------------------------
(* LIVENESS *)

(* A process is correct iff it never crashes. *)
Correct(p) == [](p \notin crashed)

(* Validity: a correct broadcaster's value is delivered by every correct process. *)
Validity ==
    \A b, p \in Procs, v \in Values :
        (Correct(b) /\ Correct(p)) =>
            [](bval[b] = v => <>(dlv[p][b] = v))

(* Agreement (liveness): if a correct process delivers v, every correct process does. *)
AgreementLiveness ==
    \A p, q, b \in Procs, v \in Values :
        (Correct(p) /\ Correct(q)) =>
            [](dlv[p][b] = v => <>(dlv[q][b] = v))

(* Termination: for every initiated instance, and for every instance whose  *)
(* broadcaster crashed, each correct process eventually decides. It either  *)
(* delivers a value or irrevocably decides NoDeliver.                       *)
Termination ==
    \A p, b \in Procs :
        Correct(p) =>
            []((bval[b] # Nil \/ b \in crashed) => <>(dlv[p][b] # Nil))

Liveness == Validity /\ AgreementLiveness /\ Termination

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => DeliverOnce
THEOREM Spec => Liveness
=============================================================================