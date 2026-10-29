---------------------------- MODULE NBAC ----------------------------
(***************************************************************************)
(* Asynchronous Non-Blocking Atomic Commitment (NBAC) with failure         *)
(* detectors, parameterized by the number of processes N.                  *)
(*                                                                         *)
(* Each process votes YES or NO. A live process broadcasts its vote.       *)
(* Any process may crash at any time, before or after sending its vote.    *)
(* The failure detector of a process may raise a suspicion at any time,    *)
(* possibly prematurely, even if nobody has crashed. A process that has    *)
(* sent its vote receives votes and decides:                               *)
(*   - ABORT immediately if it suspects a failure or has received a NO;    *)
(*   - COMMIT only if it has received YES from all N processes and no NO.  *)
(*                                                                         *)
(* The failure detector is treated as part of the environment, like        *)
(* crashes. Only the process actions Send, Receive and Decide are weakly   *)
(* fair.                                                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Proc     == 1 .. N
Votes    == {"YES", "NO"}
PCs      == {"INIT", "SENT", "COMMIT", "ABORT"}
Messages == Proc \X Votes      \* a message <<sender, vote>>

VARIABLES
    vote,       \* vote[p]      : initial vote of process p
    pc,         \* pc[p]        : control state of process p
    crashed,    \* crashed[p]   : TRUE iff p has crashed
    suspected,  \* suspected[p] : TRUE iff p's failure detector suspects some process
    sent,       \* set of vote messages broadcast so far
    rcvd        \* rcvd[p]      : set of vote messages received by p

vars == <<vote, pc, crashed, suspected, sent, rcvd>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ vote      \in [Proc -> Votes]
    /\ pc        \in [Proc -> PCs]
    /\ crashed   \in [Proc -> BOOLEAN]
    /\ suspected \in [Proc -> BOOLEAN]
    /\ sent      \subseteq Messages
    /\ rcvd      \in [Proc -> SUBSET Messages]

Decided(p) == pc[p] \in {"COMMIT", "ABORT"}

-----------------------------------------------------------------------------
(* Initial states: the common part and the three initialization scenarios. *)

InitCommon ==
    /\ pc        = [p \in Proc |-> "INIT"]
    /\ crashed   = [p \in Proc |-> FALSE]
    /\ suspected = [p \in Proc |-> FALSE]
    /\ sent      = {}
    /\ rcvd      = [p \in Proc |-> {}]

InitArbitrary ==
    /\ vote \in [Proc -> Votes]
    /\ InitCommon

InitAllYes ==
    /\ vote = [p \in Proc |-> "YES"]
    /\ InitCommon

InitAllNo ==
    /\ vote = [p \in Proc |-> "NO"]
    /\ InitCommon

Init == InitArbitrary

-----------------------------------------------------------------------------
(* Process actions (weakly fair). *)

\* A live process broadcasts its vote.
Send(p) ==
    /\ ~crashed[p]
    /\ pc[p] = "INIT"
    /\ pc'   = [pc EXCEPT ![p] = "SENT"]
    /\ sent' = sent \cup {<<p, vote[p]>>}
    /\ UNCHANGED <<vote, crashed, suspected, rcvd>>

\* A live process receives some vote message that has been sent.
Receive(p) ==
    /\ ~crashed[p]
    /\ pc[p] # "INIT"
    /\ \E m \in sent \ rcvd[p] :
          rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
    /\ UNCHANGED <<vote, pc, crashed, suspected, sent>>

ReceivedNo(p)     == \E q \in Proc : <<q, "NO">> \in rcvd[p]
ReceivedAllYes(p) == \A q \in Proc : <<q, "YES">> \in rcvd[p]

\* Abort immediately upon a suspicion or upon receiving a NO vote.
DecideAbort(p) ==
    /\ ~crashed[p]
    /\ pc[p] = "SENT"
    /\ suspected[p] \/ ReceivedNo(p)
    /\ pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<vote, crashed, suspected, sent, rcvd>>

\* Commit only with YES from all N processes, no NO, and no suspicion.
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ pc[p] = "SENT"
    /\ ~suspected[p]
    /\ ~ReceivedNo(p)
    /\ ReceivedAllYes(p)
    /\ pc' = [pc EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, crashed, suspected, sent, rcvd>>

Decide(p) == DecideAbort(p) \/ DecideCommit(p)

-----------------------------------------------------------------------------
(* Environment actions (no fairness): crashes and failure-detector output. *)

\* A process may crash at any time, before or after sending its vote.
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, pc, suspected, sent, rcvd>>

\* The failure detector of a live process may suspect at any time,
\* possibly prematurely, even when no process has crashed.
Suspect(p) ==
    /\ ~crashed[p]
    /\ ~suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, pc, crashed, sent, rcvd>>

-----------------------------------------------------------------------------
NonCrashStep(p) == Send(p) \/ Receive(p) \/ Decide(p)

Next ==
    \/ \E p \in Proc : NonCrashStep(p)
    \/ \E p \in Proc : Crash(p)
    \/ \E p \in Proc : Suspect(p)

Fairness == \A p \in Proc : WF_vars(NonCrashStep(p))

Spec          == InitArbitrary /\ [][Next]_vars /\ Fairness
SpecArbitrary == InitArbitrary /\ [][Next]_vars /\ Fairness
SpecAllYes    == InitAllYes    /\ [][Next]_vars /\ Fairness
SpecAllNo     == InitAllNo     /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties. *)

\* Agreement: no two correct processes decide differently.
Agreement ==
    \A p, q \in Proc :
        (~crashed[p] /\ ~crashed[q]) =>
            ~(pc[p] = "COMMIT" /\ pc[q] = "ABORT")

\* Abort validity: if any process votes NO, no process ever commits.
AbortValidity ==
    (\E p \in Proc : vote[p] = "NO") => (\A q \in Proc : pc[q] # "COMMIT")

AbortValidityProp == []AbortValidity

\* Commit validity: if all processes vote YES and no process is ever
\* suspected, then no process ever aborts.
CommitValidity ==
    ( /\ \A p \in Proc : vote[p] = "YES"
      /\ [](\A p \in Proc : ~suspected[p]) )
    => [](\A p \in Proc : pc[p] # "ABORT")

\* Termination: if no process ever crashes and no process is ever
\* suspected, every process eventually decides.
Termination ==
    ( /\ [](\A p \in Proc : ~crashed[p])
      /\ [](\A p \in Proc : ~suspected[p]) )
    => <>(\A p \in Proc : Decided(p))

THEOREM Spec => []TypeOK
THEOREM Spec => []Agreement
THEOREM Spec => AbortValidityProp
THEOREM Spec => CommitValidity
THEOREM Spec => Termination
=============================================================================