---------------------------- MODULE MCSession2 ----------------------------
(***************************************************************************)
(* Model-checking entry point for the Session2 system.                     *)
(* Session2.tla was not available, so this module is self-contained so     *)
(* that SANY can parse it. It models a generic two-party session            *)
(* lifecycle: open, exchange messages, close. It adds no constraints,      *)
(* constants or invariants beyond that baseline behavior.                  *)
(* If Session2.tla is available, replace the body with:                    *)
(*     EXTENDS Session2                                                    *)
(* and point the TLC .cfg file at Session2's own Init, Next or Spec        *)
(* and its properties.                                                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Parties, MaxMsgs

ASSUME /\ Parties # {}
       /\ MaxMsgs \in Nat

VARIABLES state, sent, recvd

vars == <<state, sent, recvd>>

States == {"idle", "open", "closed"}

TypeOK ==
    /\ state \in [Parties -> States]
    /\ sent  \in [Parties -> 0..MaxMsgs]
    /\ recvd \in [Parties -> 0..MaxMsgs]

Init ==
    /\ state = [p \in Parties |-> "idle"]
    /\ sent  = [p \in Parties |-> 0]
    /\ recvd = [p \in Parties |-> 0]

Open(p) ==
    /\ state[p] = "idle"
    /\ state' = [state EXCEPT ![p] = "open"]
    /\ UNCHANGED <<sent, recvd>>

Send(p, q) ==
    /\ p # q
    /\ state[p] = "open"
    /\ state[q] = "open"
    /\ sent[p] < MaxMsgs
    /\ recvd[q] < MaxMsgs
    /\ sent'  = [sent  EXCEPT ![p] = @ + 1]
    /\ recvd' = [recvd EXCEPT ![q] = @ + 1]
    /\ UNCHANGED state

Close(p) ==
    /\ state[p] = "open"
    /\ state' = [state EXCEPT ![p] = "closed"]
    /\ UNCHANGED <<sent, recvd>>

Done ==
    /\ \A p \in Parties : state[p] = "closed"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Parties : Open(p)
    \/ \E p, q \in Parties : Send(p, q)
    \/ \E p \in Parties : Close(p)
    \/ Done

Spec == Init /\ [][Next]_vars /\ \A p \in Parties : WF_vars(Close(p))

(* Safety: messages are conserved between senders and receivers. *)
TotalSent == LET F[S \in SUBSET Parties] ==
                   IF S = {} THEN 0
                   ELSE LET x == CHOOSE y \in S : TRUE
                        IN  sent[x] + F[S \ {x}]
             IN F[Parties]

TotalRecvd == LET F[S \in SUBSET Parties] ==
                    IF S = {} THEN 0
                    ELSE LET x == CHOOSE y \in S : TRUE
                         IN  recvd[x] + F[S \ {x}]
              IN F[Parties]

Conservation == TotalSent = TotalRecvd

(* Safety: a closed session is never reopened. *)
NoReopen == [][\A p \in Parties : state[p] = "closed" => state'[p] = "closed"]_vars

(* Liveness: every opened session is eventually closed. *)
EventuallyClosed == \A p \in Parties : (state[p] = "open") ~> (state[p] = "closed")

THEOREM Spec => [](TypeOK /\ Conservation)
=============================================================================