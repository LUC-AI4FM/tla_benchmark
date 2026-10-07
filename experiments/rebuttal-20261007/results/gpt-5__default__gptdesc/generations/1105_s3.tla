---- MODULE NBAC_FD ----
EXTENDS Naturals

CONSTANT Proc

ASSUME Proc # {}

(***************************************************************************)
(* Basic domains                                                          *)
(***************************************************************************)
Votes == {"YES", "NO"}
DecVals == {"COMMIT", "ABORT"}
Decisions == {"UNDECIDED"} \cup DecVals

Message ==
  [type : {"VOTE"}, from : Proc, to : Proc, val : Votes] \/
  [type : {"DECIDE"}, from : Proc, to : Proc, val : DecVals]

Messages ==
  { [type |-> "VOTE",   from |-> p, to |-> q, val |-> v] : p \in Proc, q \in Proc, v \in Votes } \cup
  { [type |-> "DECIDE", from |-> p, to |-> q, val |-> d] : p \in Proc, q \in Proc, d \in DecVals }

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
  vote,        \* function Proc -> Votes
  decision,    \* function Proc -> Decisions
  recvdYes,    \* function Proc -> SUBSET Proc
  recvdNo,     \* function Proc -> SUBSET Proc
  Crashed,     \* SUBSET Proc
  Suspected,   \* SUBSET Proc (failure detector output)
  Net,         \* SUBSET Messages (asynchronous network)
  Sent,        \* SUBSET (Proc \X Proc): which vote messages were sent
  DecSent      \* SUBSET (Proc \X Proc): which DECIDE messages were sent

vars == << vote, decision, recvdYes, recvdNo, Crashed, Suspected, Net, Sent, DecSent >>

(***************************************************************************)
(* Helper predicates                                                       *)
(***************************************************************************)
AllVotesYes == \A p \in Proc : vote[p] = "YES"
AllVotesNo  == \A p \in Proc : vote[p] = "NO"
Decided(p)  == decision[p] \in DecVals

(***************************************************************************)
(* Type and safety invariants (state predicates)                           *)
(***************************************************************************)
TypeInv ==
  /\ vote \in [Proc -> Votes]
  /\ decision \in [Proc -> Decisions]
  /\ recvdYes \in [Proc -> SUBSET Proc]
  /\ recvdNo \in [Proc -> SUBSET Proc]
  /\ Crashed \subseteq Proc
  /\ Suspected \subseteq Proc
  /\ Net \in SUBSET Messages
  /\ Sent \subseteq (Proc \X Proc)
  /\ DecSent \subseteq (Proc \X Proc)

NoContradictoryVotes ==
  \A p \in Proc : recvdYes[p] \cap recvdNo[p] = {}

FDAcuracy ==
  Suspected \subseteq Crashed

SafetyInvariants == TypeInv /\ NoContradictoryVotes /\ FDAcuracy

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
  /\ vote \in [Proc -> Votes]
  /\ \E v \in Votes : vote = [p \in Proc |-> v]   \* specialized: all YES or all NO
  /\ decision = [p \in Proc |-> "UNDECIDED"]
  /\ recvdYes = [p \in Proc |-> IF vote[p] = "YES" THEN {p} ELSE {}]
  /\ recvdNo  = [p \in Proc |-> IF vote[p] = "NO"  THEN {p} ELSE {}]
  /\ Crashed = {}
  /\ Suspected = {}
  /\ Net = {}
  /\ Sent = {}
  /\ DecSent = {}

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
SendVoteAct(p, q) ==
  /\ p \in Proc /\ q \in Proc
  /\ p \notin Crashed
  /\ <<p, q>> \notin Sent
  /\ LET msg == [type |-> "VOTE", from |-> p, to |-> q, val |-> vote[p]]
     IN Net' = Net \cup {msg}
  /\ Sent' = Sent \cup {<<p, q>>}
  /\ UNCHANGED << vote, decision, recvdYes, recvdNo, Crashed, Suspected, DecSent >>

ReceiveVote(p, m) ==
  /\ p \in Proc /\ p \notin Crashed
  /\ m \in Net
  /\ m.type = "VOTE" /\ m.to = p
  /\ Net' = Net \ {m}
  /\ IF m.val = "YES"
        THEN /\ recvdYes' = [recvdYes EXCEPT ![p] = @ \cup {m.from}]
             /\ UNCHANGED recvdNo
        ELSE /\ recvdNo'  = [recvdNo  EXCEPT ![p] = @ \cup {m.from}]
             /\ UNCHANGED recvdYes
  /\ UNCHANGED << vote, decision, Crashed, Suspected, Sent, DecSent >>

ReceiveDecide(p, m) ==
  /\ p \in Proc /\ p \notin Crashed
  /\ m \in Net
  /\ m.type = "DECIDE" /\ m.to = p
  /\ Net' = Net \ {m}
  /\ decision' = [decision EXCEPT ![p] = m.val]
  /\ UNCHANGED << vote, recvdYes, recvdNo, Crashed, Suspected, Sent, DecSent >>

DecideCommit(p) ==
  /\ p \in Proc /\ p \notin Crashed
  /\ decision[p] = "UNDECIDED"
  /\ recvdNo[p] = {}
  /\ recvdYes[p] = Proc
  /\ Suspected = {}
  /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
  /\ UNCHANGED << vote, recvdYes, recvdNo, Crashed, Suspected, Net, Sent, DecSent >>

DecideAbort(p) ==
  /\ p \in Proc /\ p \notin Crashed
  /\ decision[p] = "UNDECIDED"
  /\ (recvdNo[p] # {} \/ Suspected # {})
  /\ decision' = [decision EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED << vote, recvdYes, recvdNo, Crashed, Suspected, Net, Sent, DecSent >>

BroadcastDecisionTo(p, q) ==
  /\ p \in Proc /\ q \in Proc
  /\ p \notin Crashed
  /\ decision[p] \in DecVals
  /\ <<p, q>> \notin DecSent
  /\ Net' = Net \cup { [type |-> "DECIDE", from |-> p, to |-> q, val |-> decision[p]] }
  /\ DecSent' = DecSent \cup {<<p, q>>}
  /\ UNCHANGED << vote, decision, recvdYes, recvdNo, Crashed, Suspected, Sent >>

Crash(p) ==
  /\ p \in Proc /\ p \notin Crashed
  /\ Crashed' = Crashed \cup {p}
  /\ UNCHANGED << vote, decision, recvdYes, recvdNo, Suspected, Net, Sent, DecSent >>

FDUpdate ==
  /\ Suspected' \in SUBSET Crashed
  /\ Suspected \subseteq Suspected'
  /\ UNCHANGED << vote, decision, recvdYes, recvdNo, Crashed, Net, Sent, DecSent >>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
  \/ \E p \in Proc, q \in Proc : SendVoteAct(p, q)
  \/ \E p \in Proc, m \in Net : ReceiveVote(p, m)
  \/ \E p \in Proc, m \in Net : ReceiveDecide(p, m)
  \/ \E p \in Proc : DecideCommit(p)
  \/ \E p \in Proc : DecideAbort(p)
  \/ \E p \in Proc, q \in Proc : BroadcastDecisionTo(p, q)
  \/ \E p \in Proc : Crash(p)
  \/ FDUpdate

(***************************************************************************)
(* Fairness: weak fairness for non-stuttering process actions              *)
(***************************************************************************)
ReceiveSome(p) == \E m \in Net : (m.to = p) /\ (ReceiveVote(p, m) \/ ReceiveDecide(p, m))
BroadcastSome(p) == \E q \in Proc : BroadcastDecisionTo(p, q)

Fairness ==
  /\ \A p \in Proc : WF_vars(ReceiveSome(p))
  /\ \A p \in Proc : WF_vars(DecideCommit(p) \/ DecideAbort(p))
  /\ \A p \in Proc : \A q \in Proc : WF_vars(SendVoteAct(p, q))
  /\ \A p \in Proc : WF_vars(BroadcastSome(p))

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Temporal properties                                                     *)
(***************************************************************************)
Agreement ==
  [](\A p, q \in Proc : (Decided(p) /\ Decided(q)) => decision[p] = decision[q])

AbortValidity ==
  []((\E p \in Proc : vote[p] = "NO") => ~(\E p \in Proc : decision[p] = "COMMIT"))

CommitValidity ==
  []((AllVotesYes /\ (Crashed = {})) => (\A p \in Proc : decision[p] # "ABORT"))

Termination ==
  \A p \in Proc : ([](p \notin Crashed)) => (<>Decided(p))

EventualCommit ==
  (AllVotesYes /\ [](Crashed = {})) => <>(\A p \in Proc : decision[p] = "COMMIT")

FDCompleteness ==
  \A p \in Proc : [](p \in Crashed => <>(p \in Suspected))

TypeSafety ==
  []SafetyInvariants

====