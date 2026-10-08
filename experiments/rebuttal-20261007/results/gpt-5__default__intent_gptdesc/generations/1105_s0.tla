------------------------------ MODULE AtomicCommitAbstract ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    N,              \* Number of processes
    Proc,           \* Set of process identifiers
    Votes           \* Initial votes: function Proc -> {"YES","NO"}

(*
  Basic value sets
*)
VoteVal == {"YES", "NO"}
NoMsg   == "NoMsg"
DecVal  == {"Undecided", "COMMIT", "ABORT"}

ASSUME
    /\ N \in Nat
    /\ IsFiniteSet(Proc) /\ Proc # {}
    /\ Cardinality(Proc) = N
    /\ Votes \in [Proc -> VoteVal]

VARIABLES
    Sent,           \* [Proc -> BOOLEAN], whether p has (attempted and performed) its one broadcast
    UnpredSent,     \* [Proc -> BOOLEAN], whether p's one optional unpredictable message has been injected
    Crashed,        \* SUBSET Proc, set of processes that have crashed (stop forever)
    Susp,           \* SUBSET Proc, set of processes suspected by the failure detector
    Net,            \* SUBSET Proc \X Proc \X VoteVal, multiset abstracted as a set of in-flight vote messages
    Received,       \* [Proc -> [Proc -> (VoteVal \cup {NoMsg})]], local receive buffers
    Decision        \* [Proc -> DecVal], local decision state

vars == << Sent, UnpredSent, Crashed, Susp, Net, Received, Decision >>

(*
  Helper predicates over local state
*)
HasVote(p, r) == Received[p][r] \in VoteVal
AllYes(p)     == \A r \in Proc: Received[p][r] = "YES"
SawNo(p)      == \E r \in Proc: Received[p][r] = "NO"
MissingFromSusp(p) == \E r \in Susp: Received[p][r] = NoMsg
Decided(p)    == Decision[p] \in {"COMMIT", "ABORT"}

(*
  Initialization
*)
Init ==
    /\ Sent = [p \in Proc |-> FALSE]
    /\ UnpredSent = [p \in Proc |-> FALSE]
    /\ Crashed = {}
    /\ Susp = {}
    /\ Net = {}
    /\ Received = [p \in Proc |-> [q \in Proc |-> NoMsg]]
    /\ Decision = [p \in Proc |-> "Undecided"]

(*
  Actions
*)

Broadcast(p) ==
    /\ p \in Proc
    /\ p \notin Crashed
    /\ ~Sent[p]
    /\ Sent' = [Sent EXCEPT ![p] = TRUE]
    /\ Net' = Net \cup { <<p, q, Votes[p]>> : q \in Proc }
    /\ UNCHANGED << UnpredSent, Crashed, Susp, Received, Decision >>

Deliver(p, q) ==
    /\ p \in Proc /\ q \in Proc
    /\ \E v \in VoteVal: <<p, q, v>> \in Net
    /\ LET v == CHOOSE x \in VoteVal: <<p, q, x>> \in Net IN
         /\ Net' = Net \ { <<p, q, v>> }
         /\ Received' =
               IF q \notin Crashed /\ Received[q][p] = NoMsg
               THEN [Received EXCEPT ![q][p] = v]
               ELSE Received
    /\ UNCHANGED << Sent, UnpredSent, Crashed, Susp, Decision >>

Crash(p) ==
    /\ p \in Proc
    /\ p \notin Crashed
    /\ Crashed' = Crashed \cup {p}
    /\ Susp' = Susp \cup {p}   \* immediately and permanently suspected upon crash
    /\ Decision' = Decision
    /\ Sent' = Sent
    /\ Received' = Received
    /\ \* Optionally inject at most one unpredictable message from p to any q with any value,
       \* but only if p has not already unpredictably sent one and has not broadcast.
       (
         /\ UnpredSent' = UnpredSent
         /\ Net' = Net
       )
       \/
       (
         /\ ~UnpredSent[p]
         /\ ~Sent[p]
         /\ \E q \in Proc, v \in VoteVal:
               /\ UnpredSent' = [UnpredSent EXCEPT ![p] = TRUE]
               /\ Net' = Net \cup { <<p, q, v>> }
       )

DecideCommit(p) ==
    /\ p \in Proc
    /\ p \notin Crashed
    /\ Decision[p] = "Undecided"
    /\ Susp = {}                        \* commit only with no suspicions (i.e., no crashes)
    /\ AllYes(p)                        \* and only after receiving YES from all
    /\ Decision' = [Decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED << Sent, UnpredSent, Crashed, Susp, Net, Received >>

DecideAbort(p) ==
    /\ p \in Proc
    /\ p \notin Crashed
    /\ Decision[p] = "Undecided"
    /\ ( SawNo(p) \/ MissingFromSusp(p) )
    /\ Decision' = [Decision EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED << Sent, UnpredSent, Crashed, Susp, Net, Received >>

Next ==
    \E p \in Proc: Broadcast(p)
    \/ \E p \in Proc: Crash(p)
    \/ \E p \in Proc: \E q \in Proc: Deliver(p, q)
    \/ \E p \in Proc: DecideCommit(p)
    \/ \E p \in Proc: DecideAbort(p)

(*
  Type and safety invariants
*)
TypeOK ==
    /\ Sent \in [Proc -> BOOLEAN]
    /\ UnpredSent \in [Proc -> BOOLEAN]
    /\ Crashed \subseteq Proc
    /\ Susp \subseteq Proc
    /\ Net \subseteq Proc \X Proc \X VoteVal
    /\ Received \in [Proc -> [Proc -> (VoteVal \cup {NoMsg})]]
    /\ Decision \in [Proc -> DecVal]

SafetyInv ==
    /\ Susp \subseteq Crashed
    /\ \A p \in Proc: p \in Crashed => p \in Susp
    /\ \A p \in Proc: UnpredSent[p] => p \in Crashed

(*
  Fairness to enable liveness reasoning:
  - Each noncrashed process eventually performs its one broadcast (if it never crashes before).
  - Each in-flight point-to-point message is eventually delivered to a noncrashed recipient.
  - If a decision (commit/abort) becomes continuously enabled for a noncrashed process, it eventually occurs.
*)
Fairness ==
    /\ \A p \in Proc: WF_vars(Broadcast(p))
    /\ \A p \in Proc: \A q \in Proc: WF_vars(Deliver(p, q))
    /\ \A p \in Proc: WF_vars(DecideCommit(p))
    /\ \A p \in Proc: WF_vars(DecideAbort(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Correctness properties

  Agreement: no two nonfaulty processes (those that never crash) decide different outcomes.
*)
Nonfaulty(p) == [] (p \notin Crashed)

Agreement ==
    \A p, q \in Proc:
        (Nonfaulty(p) /\ Nonfaulty(q))
        => [] ( (Decided(p) /\ Decided(q)) => Decision[p] = Decision[q] )

(*
  Abort validity: if any process initially votes NO, then no process may decide COMMIT.
*)
AbortValidity ==
    (\E r \in Proc: Votes[r] = "NO")
    => [] (\A p \in Proc: Decision[p] # "COMMIT")

(*
  Commit validity: if all processes initially vote YES and no one is suspected at that time,
  then (assuming no crashes occur thereafter) no process decides ABORT.
*)
CommitValidity ==
    ((\A r \in Proc: Votes[r] = "YES") /\ (Susp = {}))
    => ( [] (Crashed = {}) => [] (\A p \in Proc: Decision[p] # "ABORT") )

(*
  Termination under stability:
  If from some point on there are no further crashes and the failure detector suspects no noncrashed process
  (i.e., Susp \subseteq Crashed), then every noncrashed process eventually decides (COMMIT or ABORT).
*)
TerminationUnderStability ==
    (<>[] (UNCHANGED Crashed /\ Susp \subseteq Crashed))
    => (\A p \in Proc: Nonfaulty(p) => <> Decided(p))

=============================================================================