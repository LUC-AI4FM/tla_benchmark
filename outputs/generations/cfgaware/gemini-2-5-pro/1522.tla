---------------------------- MODULE Huang ----------------------------
EXTENDS Reals, FiniteSets

CONSTANTS Procs, Leader
ASSUME Leader \in Procs

VARIABLES active, weight, messages

vars == <<active, weight, messages>>

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Real]
    /\ \A p \in Procs : weight[p] >= 0
    /\ messages \subseteq Procs \X Procs \X {r \in Real : r > 0}

RECURSIVE SumOverDomain(_, _)
SumOverDomain(S, f) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x_ \in S : TRUE
         IN f[x] + SumOverDomain(S \ {x}, f)

TotalWeight == SumOverDomain(Procs, weight) + SumOverDomain(messages, LAMBDA m: m[3])

Invariant == TotalWeight = 1

Init ==
    /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ messages = {}

(* An active process p sends half its weight to another process q. *)
Send(p, q) ==
    /\ active[p]
    /\ weight[p] > 0
    /\ active' = active
    /\ weight' = [weight EXCEPT ![p] = @ / 2]
    /\ messages' = messages \cup {<<p, q, weight[p] / 2>>}

(* A message m is received by its destination, which becomes active. *)
Receive(m) ==
    /\ m \in messages
    /\ LET receiver == m[2]
           w_payload == m[3]
       IN  /\ messages' = messages \ {m}
           /\ weight' = [weight EXCEPT ![receiver] = @ + w_payload]
           /\ active' = [active EXCEPT ![receiver] = TRUE]

(* A non-leader active process p becomes idle. If it has weight, it sends it to the Leader. *)
BecomeIdle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ IF weight[p] > 0
       THEN /\ messages' = messages \cup {<<p, Leader, weight[p]>>}
            /\ weight' = [weight EXCEPT ![p] = 0]
       ELSE /\ UNCHANGED <<weight, messages>>

(* The leader becomes idle when it is the only active process and has all the weight. *)
(* This action signifies that termination has been detected. *)
LeaderBecomesIdle ==
    /\ active[Leader]
    /\ weight[Leader] = 1
    /\ \A p \in Procs \ {Leader} : ~active[p]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, messages>>

Next ==
    \/ (\E p, q \in Procs : Send(p, q))
    \/ (\E m \in messages : Receive(m))
    \/ (\E p \in Procs \ {Leader} : BecomeIdle(p))
    \/ LeaderBecomesIdle

TerminationDetected ==
    active[Leader] = FALSE

AllIdleAndQueuesEmpty ==
    /\ \A p \in Procs : active[p] = FALSE
    /\ messages = {}

Safety ==
    TerminationDetected => AllIdleAndQueuesEmpty

Liveness ==
    <>TerminationDetected

Fairness ==
    /\ \A p \in Procs : WF_vars(\E q \in Procs : Send(p, q))
    /\ \A p \in Procs \ {Leader} : WF_vars(BecomeIdle(p))
    /\ WF_vars(LeaderBecomesIdle)
    /\ WF_vars(\E m \in messages : Receive(m))

=============================================================================