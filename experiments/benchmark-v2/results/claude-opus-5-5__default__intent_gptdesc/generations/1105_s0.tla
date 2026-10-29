------------------------------ MODULE AtomicCommitFD ------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment with crash failures, asynchronous        *)
(* reliable point-to-point channels, and a perfect failure detector.       *)
(*                                                                         *)
(*  - Crash(p) makes p stop forever, and p is immediately and permanently  *)
(*    suspected. Only crashed processes are ever suspected.                *)
(*  - Send(p) is one broadcast: it puts one vote message to every process  *)
(*    into the network.                                                    *)
(*  - Deliver(s, r) delivers one vote message.                             *)
(*  - A crashed sender's broadcast may be delivered only partially, which  *)
(*    is its single unpredictable message.                                 *)
(*  - Decide(p) uses only p's local knowledge to form a proposal: the      *)
(*    votes p received and the processes p suspects.                       *)
(*    The final outcome then comes from an abstract consensus object, as   *)
(*    in the classic reduction of NBAC to consensus.                       *)
(*    The first proposal that reaches the object fixes the outcome.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,        \* number of processes
          InitVote  \* initial distribution of votes: [1..N -> {"YES","NO"}]

ASSUME NAssump    == N \in Nat \ {0}
ASSUME VoteAssump == InitVote \in [1..N -> {"YES", "NO"}]

Proc     == 1..N
Votes    == {"YES", "NO"}
PCs      == {"init", "sent", "commit", "abort", "crashed"}
Outcomes == {"NONE", "COMMIT", "ABORT"}
Msgs     == Proc \X Proc \X Votes            \* <<sender, receiver, vote>>

VARIABLES pc,         \* local state of each process
          msgs,       \* vote messages in transit
          rcvdYes,    \* rcvdYes[p] = senders whose YES vote p has received
          rcvdNo,     \* rcvdNo[p]  = senders whose NO vote p has received
          crashed,    \* set of crashed processes
          suspected,  \* set of suspected processes (failure detector output)
          consensus   \* abstract consensus object deciding the final outcome

vars == <<pc, msgs, rcvdYes, rcvdNo, crashed, suspected, consensus>>

---------------------------------------------------------------------------
Init ==
  /\ pc        = [p \in Proc |-> "init"]
  /\ msgs      = {}
  /\ rcvdYes   = [p \in Proc |-> {}]
  /\ rcvdNo    = [p \in Proc |-> {}]
  /\ crashed   = {}
  /\ suspected = {}
  /\ consensus = "NONE"

\* p broadcasts its vote to every process (exactly once).
Send(p) ==
  /\ pc[p] = "init"
  /\ pc'   = [pc EXCEPT ![p] = "sent"]
  /\ msgs' = msgs \cup {<<p, q, InitVote[p]>> : q \in Proc}
  /\ UNCHANGED <<rcvdYes, rcvdNo, crashed, suspected, consensus>>

\* Deliver the vote message from s to a non-crashed recipient r.
Deliver(s, r) ==
  /\ r \notin crashed
  /\ \E v \in Votes :
       /\ <<s, r, v>> \in msgs
       /\ msgs' = msgs \ {<<s, r, v>>}
       /\ IF v = "YES"
            THEN /\ rcvdYes' = [rcvdYes EXCEPT ![r] = @ \cup {s}]
                 /\ UNCHANGED rcvdNo
            ELSE /\ rcvdNo'  = [rcvdNo  EXCEPT ![r] = @ \cup {s}]
                 /\ UNCHANGED rcvdYes
  /\ UNCHANGED <<pc, crashed, suspected, consensus>>

\* p crashes; the perfect failure detector immediately and permanently suspects it.
Crash(p) ==
  /\ p \notin crashed
  /\ pc'        = [pc EXCEPT ![p] = "crashed"]
  /\ crashed'   = crashed \cup {p}
  /\ suspected' = suspected \cup {p}
  /\ UNCHANGED <<msgs, rcvdYes, rcvdNo, consensus>>

\* p can decide once it has received a NO vote, or once it has, for every
\* process, either received that process's vote or suspected it.
CanDecide(p) ==
  \/ rcvdNo[p] # {}
  \/ \A q \in Proc : q \in rcvdYes[p] \cup suspected

LocalProposal(p) == IF rcvdYes[p] = Proc THEN "COMMIT" ELSE "ABORT"

Decide(p) ==
  /\ pc[p] = "sent"
  /\ CanDecide(p)
  /\ LET dec == IF consensus = "NONE" THEN LocalProposal(p) ELSE consensus
     IN  /\ consensus' = dec
         /\ pc' = [pc EXCEPT ![p] = IF dec = "COMMIT" THEN "commit" ELSE "abort"]
  /\ UNCHANGED <<msgs, rcvdYes, rcvdNo, crashed, suspected>>

\* Stuttering once every process has decided or crashed, to avoid spurious deadlock.
Done ==
  /\ \A p \in Proc : pc[p] \in {"commit", "abort", "crashed"}
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Proc : Send(p) \/ Crash(p) \/ Decide(p)
  \/ \E s, r \in Proc : Deliver(s, r)
  \/ Done

Fairness ==
  /\ \A p \in Proc : WF_vars(Send(p))
  /\ \A p \in Proc : WF_vars(Decide(p))
  /\ \A s, r \in Proc : WF_vars(Deliver(s, r))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Type and bound invariants *)
TypeOK ==
  /\ pc        \in [Proc -> PCs]
  /\ msgs      \subseteq Msgs
  /\ rcvdYes   \in [Proc -> SUBSET Proc]
  /\ rcvdNo    \in [Proc -> SUBSET Proc]
  /\ crashed   \subseteq Proc
  /\ suspected \subseteq Proc
  /\ consensus \in Outcomes

CountsInBounds ==
  /\ \A p \in Proc :
       /\ Cardinality(rcvdYes[p]) \in 0..N
       /\ Cardinality(rcvdNo[p])  \in 0..N
       /\ Cardinality(rcvdYes[p]) + Cardinality(rcvdNo[p]) <= N
  /\ Cardinality(crashed)   \in 0..N
  /\ Cardinality(suspected) \in 0..N
  /\ Cardinality(msgs)      \in 0..(N * N)

\* Perfect failure detector: exactly the crashed processes are suspected.
FDAccuracy == suspected = crashed

Correct == Proc \ crashed
AllYes  == \A p \in Proc : InitVote[p] = "YES"
SomeNo  == \E p \in Proc : InitVote[p] = "NO"

(* Safety properties *)
Agreement ==
  \A p, q \in Correct : ~(pc[p] = "commit" /\ pc[q] = "abort")

AbortValidity ==
  SomeNo => \A p \in Proc : pc[p] # "commit"

\* If everyone votes YES and nobody is (yet) suspected, then nobody has aborted.
CommitValidity ==
  (AllYes /\ suspected = {}) => \A p \in Proc : pc[p] # "abort"

\* If everyone votes YES and no crash ever happens, then nobody ever aborts.
CommitValidityTemporal ==
  (AllYes /\ [](suspected = {})) => [](\A p \in Proc : pc[p] # "abort")

Invariants ==
  /\ TypeOK /\ CountsInBounds /\ FDAccuracy
  /\ Agreement /\ AbortValidity /\ CommitValidity

(* Liveness *)
AllCorrectDecided == \A p \in Proc : p \notin crashed => pc[p] \in {"commit", "abort"}

\* Once crashes stop and the detector suspects exactly the crashed processes,
\* every non-crashed process eventually decides.
Stable == [](crashed = crashed' /\ suspected = crashed)
TerminationUnderStability == (<>[][crashed' = crashed]_vars) => <>AllCorrectDecided
Termination == <>AllCorrectDecided

THEOREM Spec => []Invariants
THEOREM Spec => CommitValidityTemporal
THEOREM Spec => TerminationUnderStability
================================================================================