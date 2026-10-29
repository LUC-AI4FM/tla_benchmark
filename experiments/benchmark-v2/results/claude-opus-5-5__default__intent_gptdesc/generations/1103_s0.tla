---------------------------- MODULE NonBlockingAtomicCommit ----------------------------
(***************************************************************************)
(* Non-blocking atomic commitment (NBAC) for N crash-prone processes that *)
(* use an unreliable failure detector.                                    *)
(*                                                                         *)
(*  - Voting phase: every process holds an initial vote, YES or NO.        *)
(*  - Message-sending phase: each process sends its vote to every other   *)
(*    process, one destination at a time, so a crash can interrupt it.    *)
(*  - Asynchronous reception: in-transit messages sit in a network set    *)
(*    and are moved to the receiver's set of delivered messages.          *)
(*  - Crashes are irreversible local faults.                              *)
(*  - The failure detector is a per-process Boolean oracle,               *)
(*    suspected[p][q]. It may change at any time, so it is neither        *)
(*    accurate nor complete.                                              *)
(*  - A process proposes once it has heard from or suspects every other   *)
(*    process. It proposes "commit" only if it has a YES from everyone,   *)
(*    and otherwise proposes "abort". A NO voter may abort unilaterally.  *)
(*  - Agreement despite unreliable suspicions comes from an abstract      *)
(*    consensus object: the first proposal becomes the single outcome.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Proc      == 1..N
Votes     == {"YES", "NO"}
Outcomes  == {"commit", "abort"}
None      == "none"
Msg       == [from : Proc, to : Proc, vote : Votes]

VARIABLES
    vote,       \* vote[p] : initial vote of p (fixed after Init)
    crashed,    \* crashed[p] : TRUE once p has crashed (irreversible)
    sentTo,     \* sentTo[p] : set of processes p has sent its vote to
    network,    \* set of in-transit (sent, not yet delivered) messages
    rcvd,       \* rcvd[p] : set of messages delivered to p
    suspected,  \* suspected[p][q] : failure detector output of p about q
    proposed,   \* proposed[p] : p has proposed to the consensus object
    consensus,  \* value chosen by the abstract consensus object (or None)
    decision    \* decision[p] : None, "commit" or "abort"

vars == <<vote, crashed, sentTo, network, rcvd, suspected,
          proposed, consensus, decision>>

---------------------------------------------------------------------------
(* Helper predicates *)

ReceivedFrom(p, q) == \E m \in rcvd[p] : m.from = q

KnowsYes(p, q) ==
    IF q = p THEN vote[p] = "YES"
             ELSE \E m \in rcvd[p] : m.from = q /\ m.vote = "YES"

\* p has enough information to propose
CanPropose(p) ==
    \/ vote[p] = "NO"
    \/ \A q \in Proc \ {p} : ReceivedFrom(p, q) \/ suspected[p][q]

\* Value proposed by p: commit only if p knows that everyone voted YES
ProposalValue(p) ==
    IF \A q \in Proc : KnowsYes(p, q) THEN "commit" ELSE "abort"

---------------------------------------------------------------------------
TypeOK ==
    /\ vote      \in [Proc -> Votes]
    /\ crashed   \in [Proc -> BOOLEAN]
    /\ sentTo    \in [Proc -> SUBSET Proc]
    /\ network   \subseteq Msg
    /\ rcvd      \in [Proc -> SUBSET Msg]
    /\ suspected \in [Proc -> [Proc -> BOOLEAN]]
    /\ proposed  \in [Proc -> BOOLEAN]
    /\ consensus \in Outcomes \cup {None}
    /\ decision  \in [Proc -> Outcomes \cup {None}]

Init ==
    /\ vote      \in [Proc -> Votes]     \* any mix, including all YES
    /\ crashed   = [p \in Proc |-> FALSE]
    /\ sentTo    = [p \in Proc |-> {}]
    /\ network   = {}
    /\ rcvd      = [p \in Proc |-> {}]
    /\ suspected = [p \in Proc |-> [q \in Proc |-> FALSE]]
    /\ proposed  = [p \in Proc |-> FALSE]
    /\ consensus = None
    /\ decision  = [p \in Proc |-> None]

---------------------------------------------------------------------------
(* Actions *)

\* p sends its vote to q
SendTo(p, q) ==
    /\ ~crashed[p]
    /\ q \in Proc \ {p}
    /\ q \notin sentTo[p]
    /\ network' = network \cup {[from |-> p, to |-> q, vote |-> vote[p]]}
    /\ sentTo'  = [sentTo EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED <<vote, crashed, rcvd, suspected, proposed, consensus, decision>>

Send(p) == \E q \in Proc : SendTo(p, q)

\* asynchronous delivery of message m to a live process p
Deliver(p, m) ==
    /\ ~crashed[p]
    /\ m \in network
    /\ m.to = p
    /\ network' = network \ {m}
    /\ rcvd'    = [rcvd EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<vote, crashed, sentTo, suspected, proposed, consensus, decision>>

Receive(p) == \E m \in network : Deliver(p, m)

\* irreversible crash fault
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, sentTo, network, rcvd, suspected, proposed, consensus, decision>>

\* nondeterministic, unreliable failure-detector change
FDChange(p, q) ==
    /\ p # q
    /\ suspected' = [suspected EXCEPT ![p][q] = ~@]
    /\ UNCHANGED <<vote, crashed, sentTo, network, rcvd, proposed, consensus, decision>>

\* p proposes to the abstract consensus object; the first proposal wins
Propose(p) ==
    /\ ~crashed[p]
    /\ ~proposed[p]
    /\ CanPropose(p)
    /\ proposed'  = [proposed EXCEPT ![p] = TRUE]
    /\ consensus' = IF consensus = None THEN ProposalValue(p) ELSE consensus
    /\ UNCHANGED <<vote, crashed, sentTo, network, rcvd, suspected, decision>>

\* p learns the consensus outcome and decides irrevocably
Decide(p) ==
    /\ ~crashed[p]
    /\ decision[p] = None
    /\ consensus # None
    /\ decision' = [decision EXCEPT ![p] = consensus]
    /\ UNCHANGED <<vote, crashed, sentTo, network, rcvd, suspected, proposed, consensus>>

Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : Crash(p)
    \/ \E p, q \in Proc : FDChange(p, q)
    \/ \E p \in Proc : Propose(p)
    \/ \E p \in Proc : Decide(p)

Fairness ==
    \A p \in Proc :
        /\ WF_vars(Send(p))
        /\ WF_vars(Receive(p))
        /\ WF_vars(Propose(p))
        /\ WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties (invariants) *)

\* No two non-crashed processes decide differently
Agreement ==
    \A p, q \in Proc :
        (~crashed[p] /\ ~crashed[q] /\ decision[p] # None /\ decision[q] # None)
            => decision[p] = decision[q]

\* Stronger variant: no two processes decide differently, crashed ones included
UniformAgreement ==
    \A p, q \in Proc :
        (decision[p] # None /\ decision[q] # None) => decision[p] = decision[q]

\* Commit is only possible if every process voted YES
CommitValidity ==
    \A p \in Proc : decision[p] = "commit" => \A q \in Proc : vote[q] = "YES"

\* If any process votes NO, then no process decides commit
NoVoteValidity ==
    (\E q \in Proc : vote[q] = "NO") => \A p \in Proc : decision[p] # "commit"

ConsensusValidity ==
    consensus = "commit" => \A q \in Proc : vote[q] = "YES"

Safety == TypeOK /\ Agreement /\ UniformAgreement /\ CommitValidity
          /\ NoVoteValidity /\ ConsensusValidity

\* Decisions are irrevocable and votes never change
DecisionStable ==
    [][\A p \in Proc : decision[p] # None => decision'[p] = decision[p]]_vars

VotesFixed == [][vote' = vote]_vars

---------------------------------------------------------------------------
(* Failure detector assumptions *)

\* Eventually every crashed process is permanently suspected by everyone
EventualStrongCompleteness ==
    <>[](\A p, q \in Proc : (p # q /\ crashed[q]) => suspected[p][q])

\* Eventually suspicions match crashes exactly (diamond-P)
EventuallyPerfectFD ==
    <>[](\A p, q \in Proc : p # q => (suspected[p][q] <=> crashed[q]))

\* Failure-free run with a never-mistaken detector
NoCrashNoSuspicion ==
    /\ [](\A p \in Proc : ~crashed[p])
    /\ [](\A p, q \in Proc : ~suspected[p][q])

AllYes == \A p \in Proc : vote[p] = "YES"

---------------------------------------------------------------------------
(* Liveness properties *)

\* Every non-crashed process eventually decides
Termination ==
    \A p \in Proc : <>(crashed[p] \/ decision[p] # None)

\* Non-blocking termination under the eventual detector assumption
NonBlockingTermination == EventualStrongCompleteness => Termination

\* Termination under the stronger eventually perfect detector assumption
TerminationUnderDiamondP == EventuallyPerfectFD => Termination

\* Validity (commit side): if all vote YES and there are no crashes or
\* suspicions, then every process eventually commits
CommitProgress ==
    (AllYes /\ NoCrashNoSuspicion) =>
        <>(\A p \in Proc : decision[p] = "commit")

THEOREM Spec => []Safety
THEOREM Spec => DecisionStable /\ VotesFixed
THEOREM Spec => NonBlockingTermination
THEOREM Spec => TerminationUnderDiamondP
THEOREM Spec => CommitProgress
=============================================================================