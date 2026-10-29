---------------------------- MODULE MCSession1 ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session1 specification.                  *)
(*                                                                         *)
(* In the original setup this module is only:                              *)
(*     EXTENDS Session1                                                    *)
(* plus a configuration file with  SPECIFICATION Spec .                    *)
(* Its comment says: "Nothing to be added for model checking."             *)
(*                                                                         *)
(* The contents of Session1 are not available. A file that EXTENDS a       *)
(* missing module will not pass SANY. So this module is self-contained.    *)
(* It inlines a minimal stand-in for Session1 that defines the Init, Next  *)
(* and Spec the wrapper refers to. The stand-in session model below is     *)
(* assumed, not taken from the real Session1. Replace this section with    *)
(* "EXTENDS Session1" once the real module is available.                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxMsgs            \* bound on messages sent within a session

ASSUME MaxMsgsAssump == MaxMsgs \in Nat

VARIABLES state,            \* session status: "Closed" or "Open"
          sent,             \* number of messages sent in the current session
          received          \* number of messages received in the current session

vars == <<state, sent, received>>

States == {"Closed", "Open"}

---------------------------------------------------------------------------
(* Stand-in definitions for Session1                                       *)
---------------------------------------------------------------------------

TypeOK ==
    /\ state \in States
    /\ sent \in 0..MaxMsgs
    /\ received \in 0..MaxMsgs

Init ==
    /\ state = "Closed"
    /\ sent = 0
    /\ received = 0

OpenSession ==
    /\ state = "Closed"
    /\ state' = "Open"
    /\ sent' = 0
    /\ received' = 0

Send ==
    /\ state = "Open"
    /\ sent < MaxMsgs
    /\ sent' = sent + 1
    /\ UNCHANGED <<state, received>>

Receive ==
    /\ state = "Open"
    /\ received < sent
    /\ received' = received + 1
    /\ UNCHANGED <<state, sent>>

CloseSession ==
    /\ state = "Open"
    /\ received = sent
    /\ state' = "Closed"
    /\ UNCHANGED <<sent, received>>

Next ==
    \/ OpenSession
    \/ Send
    \/ Receive
    \/ CloseSession

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Receive)

---------------------------------------------------------------------------
(* Properties (stand-in)                                                   *)
---------------------------------------------------------------------------

\* Safety: a session never receives more messages than were sent.
NoPhantomMessages == received <= sent

\* Safety: a closed session has no outstanding messages.
ClosedIsQuiescent == (state = "Closed") => (received = sent)

\* Liveness: every message sent is eventually received.
AllSentEventuallyReceived ==
    \A n \in 1..MaxMsgs : [](sent >= n => <>(received >= n))

---------------------------------------------------------------------------
(* Model-checking wrapper part                                             *)
(* Nothing to be added for model checking.                                 *)
(* Configuration file:  SPECIFICATION Spec                                 *)
---------------------------------------------------------------------------

THEOREM Spec => [](TypeOK /\ NoPhantomMessages /\ ClosedIsQuiescent)
THEOREM Spec => AllSentEventuallyReceived
=============================================================================