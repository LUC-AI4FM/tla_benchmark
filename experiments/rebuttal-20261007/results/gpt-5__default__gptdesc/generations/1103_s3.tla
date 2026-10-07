----------------------------- MODULE NBAC -----------------------------

EXTENDS Naturals

CONSTANT Proc, Votes

VOTE_VAL == {"YES", "NO"}
DEC_VAL == {"Commit", "Abort"}
DECISION_VAL == DEC_VAL \cup {"Undecided"}
UNKNOWN == "Unknown"
MSG ==
  { [type |-> "VOTE", from |-> i, to |-> j, v |-> x] : i \in Proc, j \in Proc, x \in VOTE_VAL } \cup
  { [type |-> "DECIDE", from |-> i, to |-> j, v |-> d] : i \in Proc, j \in Proc, d \in DEC_VAL }

ASSUME Votes \in [Proc -> VOTE_VAL]

VARIABLES decided, known, sentVote, net, Crashed, suspected

Vars == << decided, known, sentVote, net, Crashed, suspected >>

AllYes == \A p \in Proc : Votes[p] = "YES"
AnyNo  == \E p \in Proc : Votes[p] = "NO"

Inbox(p) == { m \in net : m.to = p }

TypeOK ==
  /\ decided \in [Proc -> DECISION_VAL]
  /\ known \in [Proc -> [Proc -> (VOTE_VAL \cup {UNKNOWN})]]
  /\ sentVote \in [Proc -> SUBSET Proc]
  /\ net \subseteq MSG
  /\ Crashed \subseteq Proc
  /\ suspected \in [Proc -> SUBSET Crashed]

Agreement ==
  \A p, q \in Proc :
    (decided[p] \in DEC_VAL /\ decided[q] \in DEC_VAL) => decided[p] = decided[q]

CommitImpliesAllYes ==
  \A p \in Proc : decided[p] = "Commit" => AllYes

SelfKnowsOwnVote ==
  \A p \in Proc : known[p][p] = Votes[p]

Init ==
  /\ decided = [ p \in Proc |-> "Undecided" ]
  /\ known = [ p \in Proc |-> [ q \in Proc |-> IF p = q THEN Votes[p] ELSE UNKNOWN ] ]
  /\ sentVote = [ p \in Proc |-> {} ]
  /\ net = {}
  /\ Crashed = {}
  /\ suspected = [ p \in Proc |-> {} ]

ProcStep(p) ==
  /\ p \in Proc \ Crashed
  /\ \E R, S, newSus, dNew :
       /\ R \subseteq Inbox(p)
       /\ S \subseteq ((Proc \ {p}) \ sentVote[p])
       /\ newSus \subseteq Crashed
       /\ LET
            k1 ==
              [ q \in Proc |->
                  IF \E m \in R : m.type = "VOTE" /\ m.from = q
                  THEN CHOOSE v \in VOTE_VAL :
                          \E m \in R : m.type = "VOTE" /\ m.from = q /\ v = m.v
                  ELSE known[p][q] ]
            decset == { m.v : m \in R /\ m.type = "DECIDE" }
            decLocal ==
              IF decided[p] # "Undecided" THEN decided[p]
              ELSE IF \E q \in Proc : k1[q] = "NO" THEN "Abort"
              ELSE IF \A q \in Proc : k1[q] = "YES" THEN "Commit"
              ELSE IF \E q \in Proc : k1[q] = UNKNOWN /\ q \in newSus THEN "Abort"
              ELSE "Undecided"
          IN
            /\ (decset # {} => dNew \in decset)
            /\ (decset = {} => dNew = decLocal)
            /\ known' = [ known EXCEPT ![p] = k1 ]
            /\ decided' = [ decided EXCEPT ![p] = dNew ]
            /\ sentVote' = [ sentVote EXCEPT ![p] = sentVote[p] \cup S ]
            /\ suspected' = [ suspected EXCEPT ![p] = newSus ]
            /\ net' =
                 LET
                   removed == net \ R
                   vmsgs ==
                     { [type |-> "VOTE", from |-> p, to |-> q, v |-> Votes[p]] : q \in S }
                   dmsgs ==
                     IF decided[p] = "Undecided" /\ dNew \in DEC_VAL
                     THEN { [type |-> "DECIDE", from |-> p, to |-> q, v |-> dNew] : q \in Proc \ {p} }
                     ELSE {}
                 IN
                   removed \cup vmsgs \cup dmsgs
            /\ Crashed' = Crashed

Crash(p) ==
  /\ p \in Proc \ Crashed
  /\ Crashed' = Crashed \cup {p}
  /\ UNCHANGED << decided, known, sentVote, net, suspected >>

Next ==
  (\E p \in Proc : ProcStep(p)) \/ (\E p \in Proc : Crash(p))

Spec ==
  Init /\ [][Next]_Vars /\ (\A p \in Proc : WF_Vars(ProcStep(p)))

Safety == TypeOK /\ Agreement /\ CommitImpliesAllYes /\ SelfKnowsOwnVote

============================================================================