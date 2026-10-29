---------------------------- MODULE NBAC ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Proc     == 1..N
Votes    == {"YES", "NO"}
RcvVals  == {"none", "YES", "NO"}
DecVals  == {"none", "commit", "abort"}

Msg == [src : Proc, dst : Proc, v : Votes]

VARIABLES
    vote,       \* vote[p] : the initial vote of p (YES or NO)
    crashed,    \* crashed[p] : TRUE once p has crashed (irreversible)
    sentTo,     \* sentTo[p] : set of processes p has already sent its vote to
    msgs,       \* set of messages in transit (sent but not yet received)
    rcvd,       \* rcvd[p][q] : vote of q as known by p ("none" if unknown)
    suspect,    \* suspect[p][q] : failure detector output of p about q
    proposal,   \* proposal[p] : value p proposed to the (abstract) consensus
    consensus,  \* value chosen by the abstract uniform consensus object
    decision    \* decision[p] : final decision of p

vars == << vote, crashed, sentTo, msgs, rcvd, suspect,
           proposal, consensus, decision >>

-----------------------------------------------------------------------------

TypeOK ==
    /\ vote      \in [Proc -> Votes]
    /\ crashed   \in [Proc -> BOOLEAN]
    /\ sentTo    \in [Proc -> SUBSET Proc]
    /\ msgs      \subseteq Msg
    /\ rcvd      \in [Proc -> [Proc -> RcvVals]]
    /\ suspect   \in [Proc -> [Proc -> BOOLEAN]]
    /\ proposal  \in [Proc -> DecVals]
    /\ consensus \in DecVals
    /\ decision  \in [Proc -> DecVals]

CrashedSet == { p \in Proc : crashed[p] }

-----------------------------------------------------------------------------
(* Initial state: every process votes YES or NO (all scenarios allowed,    *)
(* including all-YES). Each process knows its own vote.                     *)

Init ==
    /\ vote      \in [Proc -> Votes]
    /\ crashed   = [p \in Proc |-> FALSE]
    /\ sentTo    = [p \in Proc |-> {p}]
    /\ msgs      = {}
    /\ rcvd      = [p \in Proc |-> [q \in Proc |->
                        IF q = p THEN vote[p] ELSE "none"]]
    /\ suspect   = [p \in Proc |-> [q \in Proc |-> FALSE]]
    /\ proposal  = [p \in Proc |-> "none"]
    /\ consensus = "none"
    /\ decision  = [p \in Proc |-> "none"]

-----------------------------------------------------------------------------
(* Message-sending phase: p sends its vote to q (one destination at a time, *)
(* so a crash may interrupt the broadcast).                                 *)

Send(p, q) ==
    /\ ~crashed[p]
    /\ q \notin sentTo[p]
    /\ msgs'   = msgs \cup { [src |-> p, dst |-> q, v |-> vote[p]] }
    /\ sentTo' = [sentTo EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED << vote, crashed, rcvd, suspect, proposal, consensus, decision >>

(* Asynchronous reception of a vote message. *)
Receive(p, m) ==
    /\ m \in msgs
    /\ m.dst = p
    /\ ~crashed[p]
    /\ rcvd' = [rcvd EXCEPT ![p][m.src] = m.v]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED << vote, crashed, sentTo, suspect, proposal, consensus, decision >>

(* Crash: irreversible local fault; at least one process stays correct. *)
Crash(p) ==
    /\ ~crashed[p]
    /\ Cardinality(CrashedSet) < N - 1
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, sentTo, msgs, rcvd, suspect, proposal, consensus, decision >>

(* Unreliable failure detector: suspicion of q by p may change arbitrarily. *)
FDChange(p, q) ==
    /\ ~crashed[p]
    /\ p # q
    /\ suspect' = [suspect EXCEPT ![p][q] = ~@]
    /\ UNCHANGED << vote, crashed, sentTo, msgs, rcvd, proposal, consensus, decision >>

(* Proposal to the abstract uniform consensus:                              *)
(*   commit  if p has received YES from every process;                      *)
(*   abort   if p received a NO, or suspects some q whose vote is missing.  *)
CanCommit(p) == \A q \in Proc : rcvd[p][q] = "YES"
CanAbort(p)  == \E q \in Proc :
                    \/ rcvd[p][q] = "NO"
                    \/ (rcvd[p][q] = "none" /\ suspect[p][q])

Propose(p) ==
    /\ ~crashed[p]
    /\ proposal[p] = "none"
    /\ \E val \in DecVals \ {"none"} :
          /\ \/ val = "commit" /\ CanCommit(p)
             \/ val = "abort"  /\ CanAbort(p)
          /\ proposal'  = [proposal EXCEPT ![p] = val]
          /\ consensus' = IF consensus = "none" THEN val ELSE consensus
    /\ UNCHANGED << vote, crashed, sentTo, msgs, rcvd, suspect, decision >>

(* Decision: adopt the value chosen by consensus. *)
Decide(p) ==
    /\ ~crashed[p]
    /\ proposal[p] # "none"
    /\ consensus # "none"
    /\ decision[p] = "none"
    /\ decision' = [decision EXCEPT ![p] = consensus]
    /\ UNCHANGED << vote, crashed, sentTo, msgs, rcvd, suspect, proposal, consensus >>

Next ==
    \/ \E p, q \in Proc : Send(p, q)
    \/ \E p \in Proc : \E m \in msgs : Receive(p, m)
    \/ \E p \in Proc : Crash(p)
    \/ \E p, q \in Proc : FDChange(p, q)
    \/ \E p \in Proc : Propose(p)
    \/ \E p \in Proc : Decide(p)

Fairness ==
    /\ \A p, q \in Proc : WF_vars(Send(p, q))
    /\ \A p \in Proc : WF_vars(\E m \in msgs : Receive(p, m))
    /\ \A p \in Proc : WF_vars(Propose(p))
    /\ \A p \in Proc : WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties (invariants) *)

\* No two processes (crashed or not) decide differently (uniform agreement).
Agreement ==
    \A p, q \in Proc :
        (decision[p] # "none" /\ decision[q] # "none")
            => decision[p] = decision[q]

\* If any process votes NO, no process decides commit.
ValidityNo ==
    (\E p \in Proc : vote[p] = "NO") => \A p \in Proc : decision[p] # "commit"

\* Commit only if every process voted YES.
ValidityCommit ==
    \A p \in Proc : decision[p] = "commit" => \A q \in Proc : vote[q] = "YES"

\* Decisions are irrevocable and consistent with consensus.
DecisionConsistent ==
    \A p \in Proc : decision[p] # "none" => decision[p] = consensus

Safety == TypeOK /\ Agreement /\ ValidityNo /\ ValidityCommit /\ DecisionConsistent

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Eventual (strong) completeness of the failure detector: every crashed
\* process is eventually permanently suspected by every live process.
FDCompleteness ==
    \A p, q \in Proc :
        <>[]((~crashed[p] /\ crashed[q]) => suspect[p][q])

\* Eventual stabilization of the suspicions.
FDStabilization == <>[][UNCHANGED suspect]_suspect

FDAssumption == FDCompleteness /\ FDStabilization

\* Every non-crashed process eventually decides.
Termination ==
    \A p \in Proc : <>(crashed[p] \/ decision[p] # "none")

NonBlocking == FDAssumption => Termination

\* Non-triviality: all YES, no crashes, no suspicions => commit eventually.
NoFaults ==
    [](\A p \in Proc : ~crashed[p]) /\ [](\A p, q \in Proc : ~suspect[p][q])

NonTriviality ==
    ((\A p \in Proc : vote[p] = "YES") /\ NoFaults)
        => <>(\A p \in Proc : decision[p] = "commit")

=============================================================================