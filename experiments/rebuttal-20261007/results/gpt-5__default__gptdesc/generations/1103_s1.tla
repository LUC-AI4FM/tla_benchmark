---- MODULE NBAC ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,
  Vote

(*
  Basic domains
*)
MsgType  == {"VOTE", "DECIDE"}
Votes    == {"YES", "NO"}
DecVals  == {"COMMIT", "ABORT"}
Decisions == DecVals \cup {"UNDECIDED"}

(*
  Messages carry either a vote (YES/NO) or a decision (COMMIT/ABORT)
*)
Message ==
  [ type: MsgType,
    from: Proc,
    to:   Proc,
    val:  Votes \cup DecVals ]

(*
  Distinguished atom indicating no message reception in a step
*)
NoMsg == "NoMsg"

(*
  Assumptions on constants
*)
ASSUME Proc # {}
ASSUME Vote \in [Proc -> Votes]

VARIABLES
  yesSet,       \* yesSet[p] \subseteq Proc: senders from whom p has received YES
  noSet,        \* noSet[p]  \subseteq Proc: senders from whom p has received NO
  decision,     \* decision[p] \in Decisions
  sentVote,     \* sentVote[p] \in BOOLEAN: whether p has broadcast its vote
  sentDecide,   \* sentDecide[p] \in BOOLEAN: whether p has broadcast its decision
  Suspect,      \* Suspect[p] \subseteq Proc: p's current suspicion set (failure detector)
  Msgs,         \* set of in-flight messages (subset of Message)
  crashed       \* set of crashed processes

vars == << yesSet, noSet, decision, sentVote, sentDecide, Suspect, Msgs, crashed >>

NotCrashed(p) == p \in Proc \ crashed

AllYes == \A p \in Proc: Vote[p] = "YES"

(*
  Initialization
*)
Init ==
  /\ yesSet \in [Proc -> SUBSET Proc]
  /\ noSet \in [Proc -> SUBSET Proc]
  /\ \A p \in Proc: yesSet[p] = {} /\ noSet[p] = {}
  /\ decision \in [Proc -> Decisions]
  /\ \A p \in Proc: decision[p] = "UNDECIDED"
  /\ sentVote \in [Proc -> BOOLEAN]
  /\ \A p \in Proc: sentVote[p] = FALSE
  /\ sentDecide \in [Proc -> BOOLEAN]
  /\ \A p \in Proc: sentDecide[p] = FALSE
  /\ Suspect \in [Proc -> SUBSET Proc]
  /\ \A p \in Proc: Suspect[p] = {}
  /\ Msgs \subseteq Message
  /\ Msgs = {}
  /\ crashed \subseteq Proc
  /\ crashed = {}

(*
  A per-process step that (atomically, per p):
    - optionally receives at most one message addressed to p
    - updates its local failure detector Suspect[p] nondeterministically
    - performs local state transitions:
        * records received votes
        * adopts a received decision if undecided
        * decides ABORT on seeing any NO vote
        * decides COMMIT on having YES from all processes
        * otherwise remains UNDECIDED
    - broadcasts its vote once
    - broadcasts its decision once when it decides
*)
PerProcStep(p) ==
  /\ NotCrashed(p)
  /\ \E rm \in ({NoMsg} \cup { m \in Msgs: m.to = p }),
       Snew \in SUBSET Proc:
       LET
         msgsAfterRecv ==
           IF rm = NoMsg THEN Msgs ELSE Msgs \ {rm}
         ys0 == yesSet[p]
         ns0 == noSet[p]
         dec0 == decision[p]
         ys1 ==
           IF rm # NoMsg /\ rm.type = "VOTE" /\ rm.val = "YES"
             THEN ys0 \cup {rm.from}
             ELSE ys0
         ns1 ==
           IF rm # NoMsg /\ rm.type = "VOTE" /\ rm.val = "NO"
             THEN ns0 \cup {rm.from}
             ELSE ns0
         dec1 ==
           IF rm # NoMsg /\ rm.type = "DECIDE" /\ dec0 = "UNDECIDED"
             THEN rm.val
             ELSE dec0
         hasNo == ns1 # {}
         allYesKnown == ys1 = Proc
         dec2 ==
           IF dec1 # "UNDECIDED" THEN dec1
           ELSE IF hasNo THEN "ABORT"
           ELSE IF allYesKnown THEN "COMMIT"
           ELSE "UNDECIDED"
         willSendVotes == ~sentVote[p]
         voteMsgs ==
           { [type |-> "VOTE", from |-> p, to |-> q, val |-> Vote[p]] : q \in Proc }
         decideMsgs ==
           IF ~sentDecide[p] /\ dec2 # "UNDECIDED"
             THEN { [type |-> "DECIDE", from |-> p, to |-> q, val |-> dec2] : q \in Proc }
             ELSE {}
         msgsAfterSend ==
           msgsAfterRecv
           \cup (IF willSendVotes THEN voteMsgs ELSE {})
           \cup decideMsgs
       IN
         /\ yesSet'    = [yesSet EXCEPT ![p] = ys1]
         /\ noSet'     = [noSet  EXCEPT ![p] = ns1]
         /\ decision'  = [decision EXCEPT ![p] = dec2]
         /\ sentVote'  = [sentVote EXCEPT ![p] = sentVote[p] \/ willSendVotes]
         /\ sentDecide'= [sentDecide EXCEPT ![p] = sentDecide[p] \/ (dec2 # "UNDECIDED")]
         /\ Suspect'   = [Suspect EXCEPT ![p] = Snew]
         /\ Msgs'      = msgsAfterSend
         /\ UNCHANGED crashed

(*
  A process may crash at any time; a crashed process takes no further PerProcStep actions
*)
Crash(p) ==
  /\ NotCrashed(p)
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED << yesSet, noSet, decision, sentVote, sentDecide, Suspect, Msgs >>

Next ==
  \E p \in Proc:
    PerProcStep(p) \/ Crash(p)

Spec ==
  Init /\ [][Next]_vars

(*
  Structural safety properties
*)
TypeOK ==
  /\ yesSet \in [Proc -> SUBSET Proc]
  /\ noSet \in [Proc -> SUBSET Proc]
  /\ \A p \in Proc: yesSet[p] \cap noSet[p] = {}
  /\ decision \in [Proc -> Decisions]
  /\ sentVote \in [Proc -> BOOLEAN]
  /\ sentDecide \in [Proc -> BOOLEAN]
  /\ Suspect \in [Proc -> SUBSET Proc]
  /\ Msgs \subseteq Message
  /\ crashed \subseteq Proc
  /\ Vote \in [Proc -> Votes]

Agreement ==
  ~(\E p, q \in Proc:
      decision[p] = "COMMIT" /\ decision[q] = "ABORT")

ValidityCommitImpliesAllYes ==
  \A p \in Proc: decision[p] = "COMMIT" => AllYes

ValidityNoVoteImpliesNoCommit ==
  (\E q \in Proc: Vote[q] = "NO") => (\A p \in Proc: decision[p] # "COMMIT")

Inv == TypeOK /\ Agreement /\ ValidityCommitImpliesAllYes

====