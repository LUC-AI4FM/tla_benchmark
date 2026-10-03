----------------------------- MODULE AC_NB_FD -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

ASSUME N # {} 

(*
  Parameterized asynchronous non-blocking atomic commitment with a failure detector.
  Processes exchange initial votes, may crash, may suspect crashed processes,
  and decide Abort or Commit. Decisions are disseminated by DECIDE messages.
*)

CONSTANTS
(*
  No additional constants required by the configuration.
*)

(****************************************
*              State space              *
****************************************)

VARIABLES
  vote,       \* [N -> {"YES","NO"}]
  crashed,    \* SUBSET N
  suspected,  \* [N -> SUBSET N]  (local suspicion sets)
  sentV,      \* [N -> SUBSET N]  (to whom a vote was already sent)
  sentD,      \* [N -> SUBSET N]  (to whom a decide was already sent)
  msgs,       \* set of messages (undelivered)
  known,      \* [N -> [N -> {"Unknown","YES","NO"}]] local knowledge of votes
  decision    \* [N -> {"Undecided","Abort","Commit"}]

Vars == << vote, crashed, suspected, sentV, sentD, msgs, known, decision >>

Vals == {"YES","NO"}
LocalVal == {"Unknown"} \cup Vals
Decisions == {"Undecided","Abort","Commit"}

MsgType == {"VOTE","DECIDE"}
MsgVal  == Vals \cup {"Abort","Commit"}
Message == [type: MsgType, from: N, to: N, val: MsgVal]

Decided(i) == decision[i] \in {"Abort","Commit"}

(****************************************
*                Init                   *
****************************************)

Init ==
  /\ (vote = [i \in N |-> "YES"] \/ vote = [i \in N |-> "NO"])
  /\ crashed = {}
  /\ suspected = [i \in N |-> {}]
  /\ sentV = [i \in N |-> {}]
  /\ sentD = [i \in N |-> {}]
  /\ msgs = {}
  /\ known = [i \in N |-> [j \in N |-> IF i = j THEN vote[i] ELSE "Unknown"]]
  /\ decision = [i \in N |-> "Undecided"]

(****************************************
*              Type Invariant           *
****************************************)

TypeOK ==
  /\ vote \in [N -> Vals]
  /\ crashed \subseteq N
  /\ suspected \in [N -> SUBSET N]
  /\ sentV \in [N -> SUBSET N]
  /\ sentD \in [N -> SUBSET N]
  /\ msgs \subseteq Message
  /\ known \in [N -> [N -> LocalVal]]
  /\ decision \in [N -> Decisions]

(****************************************
*            Process actions            *
****************************************)

SendVote(i) ==
  /\ i \in N
  /\ i \notin crashed
  /\ decision[i] = "Undecided"
  /\ \E j \in N: j \notin sentV[i]
  /\ \E j \in N:
       /\ j \notin sentV[i]
       /\ msgs' = msgs \cup { [type |-> "VOTE", from |-> i, to |-> j, val |-> vote[i]] }
       /\ sentV' = [sentV EXCEPT ![i] = @ \cup {j}]
  /\ UNCHANGED << vote, crashed, suspected, sentD, known, decision >>

ReceiveVote(j) ==
  /\ j \in N
  /\ j \notin crashed
  /\ \E m \in msgs:
       /\ m.type = "VOTE"
       /\ m.to = j
       /\ msgs' = msgs \ {m}
       /\ known' = [known EXCEPT ![j][m.from] = m.val]
  /\ UNCHANGED << vote, crashed, suspected, sentV, sentD, decision >>

DecideAbort(i) ==
  /\ i \in N
  /\ i \notin crashed
  /\ decision[i] = "Undecided"
  /\ (\E k \in N: known[i][k] = "NO") \/ (suspected[i] # {})
  /\ decision' = [decision EXCEPT ![i] = "Abort"]
  /\ UNCHANGED << vote, crashed, suspected, sentV, sentD, msgs, known >>

DecideCommit(i) ==
  /\ i \in N
  /\ i \notin crashed
  /\ decision[i] = "Undecided"
  /\ \A k \in N: known[i][k] = "YES"
  /\ decision' = [decision EXCEPT ![i] = "Commit"]
  /\ UNCHANGED << vote, crashed, suspected, sentV, sentD, msgs, known >>

SendDecide(i) ==
  /\ i \in N
  /\ i \notin crashed
  /\ Decided(i)
  /\ \E j \in N: j \notin sentD[i]
  /\ \E j \in N:
       /\ j \notin sentD[i]
       /\ msgs' = msgs \cup { [type |-> "DECIDE", from |-> i, to |-> j, val |-> decision[i]] }
       /\ sentD' = [sentD EXCEPT ![i] = @ \cup {j}]
  /\ UNCHANGED << vote, crashed, suspected, sentV, known, decision >>

ReceiveDecide(j) ==
  /\ j \in N
  /\ \E m \in msgs:
       /\ m.type = "DECIDE"
       /\ m.to = j
       /\ (decision[j] = "Undecided" \/ decision[j] = m.val)
       /\ msgs' = msgs \ {m}
       /\ decision' = [decision EXCEPT ![j] = m.val]
  /\ UNCHANGED << vote, crashed, suspected, sentV, sentD, known >>

Crash(i) ==
  /\ i \in N
  /\ i \notin crashed
  /\ crashed' = crashed \cup {i}
  /\ UNCHANGED << vote, suspected, sentV, sentD, msgs, known, decision >>

(*
  Failure detector convergence: eventually, each process' suspicion set
  contains all currently crashed processes (no false suspicions here).
*)
SuspectUpdate(i) ==
  /\ i \in N
  /\ suspected[i] # crashed
  /\ suspected' = [suspected EXCEPT ![i] = crashed]
  /\ UNCHANGED << vote, crashed, sentV, sentD, msgs, known, decision >>

Proc(i) ==
  SendVote(i)
  \/ ReceiveVote(i)
  \/ DecideAbort(i)
  \/ DecideCommit(i)
  \/ SendDecide(i)
  \/ ReceiveDecide(i)
  \/ SuspectUpdate(i)

Next ==
  \/ \E i \in N: SendVote(i)
  \/ \E j \in N: ReceiveVote(j)
  \/ \E i \in N: DecideAbort(i)
  \/ \E i \in N: DecideCommit(i)
  \/ \E i \in N: SendDecide(i)
  \/ \E j \in N: ReceiveDecide(j)
  \/ \E i \in N: Crash(i)
  \/ \E i \in N: SuspectUpdate(i)

(****************************************
*            Specification              *
****************************************)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A i \in N: WF_Vars(Proc(i))

(****************************************
*         Temporal properties           *
****************************************)

AgrrLtl ==
  [] ( \A i, j \in N:
        (Decided(i) /\ Decided(j)) => decision[i] = decision[j]
     )

CommitValidityLtl ==
  [] ( (\E i \in N: decision[i] = "Commit")
       => (\A k \in N: vote[k] = "YES")
     )

AbortValidityLtl ==
  [] ( (\E k \in N: vote[k] = "NO")
       => <> (\A i \in N: decision[i] = "Abort" \/ i \in crashed)
     )

TerminationLtl ==
  <> ( \A i \in N: decision[i] # "Undecided" \/ i \in crashed )

=============================================================================