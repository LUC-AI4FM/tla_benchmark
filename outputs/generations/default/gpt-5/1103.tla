----------------------------- MODULE NBAC -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,
  VOTE

ASSUME Proc # {} /\ VOTE \in [Proc -> {"YES","NO"}]

VSET == {"YES","NO"}
DSET == {"UNDECIDED","COMMIT","ABORT"}
UNKSET == VSET \cup {"UNK"}

Msg(p, q, v) == [from |-> p, to |-> q, val |-> v]
AllMsgs == { Msg(p, q, v) : p \in Proc, q \in Proc, v \in VSET }

VARIABLES
  crashed,   \* subset of Proc that have crashed
  FD,        \* local failure detector views: [Proc -> SUBSET Proc]
  recvd,     \* received votes matrix: [Proc -> [Proc -> {"YES","NO","UNK"}]]
  msgs,      \* in-flight messages: subset of AllMsgs
  decided    \* local decision: [Proc -> {"UNDECIDED","COMMIT","ABORT"}]

vars == << crashed, FD, recvd, msgs, decided >>

TypeOK ==
  /\ crashed \subseteq Proc
  /\ FD \in [Proc -> SUBSET Proc]
  /\ \A p \in Proc : FD[p] \subseteq crashed
  /\ recvd \in [Proc -> [Proc -> UNKSET]]
  /\ msgs \subseteq AllMsgs
  /\ decided \in [Proc -> DSET]
  /\ VOTE \in [Proc -> VSET]
  /\ Proc # {}

SelfKnowledge ==
  \A p \in Proc : recvd[p][p] = VOTE[p]

AllYes == \A p \in Proc : VOTE[p] = "YES"
SomeNo == \E p \in Proc : VOTE[p] = "NO"

NoAbortWhenAllYes ==
  AllYes => \A q \in Proc : decided[q] # "ABORT"

CommitImpliesAllYes ==
  \A q \in Proc : decided[q] = "COMMIT" => AllYes

AbortImpliesSomeNo ==
  \A q \in Proc : decided[q] = "ABORT" => SomeNo

Agreement ==
  \A p, q \in Proc :
    (decided[p] \in {"COMMIT","ABORT"} /\ decided[q] \in {"COMMIT","ABORT"})
      => decided[p] = decided[q]

Init ==
  /\ crashed = {}
  /\ FD = [p \in Proc |-> {}]
  /\ decided = [p \in Proc |-> "UNDECIDED"]
  /\ recvd = [p \in Proc |-> [q \in Proc |-> IF q = p THEN VOTE[p] ELSE "UNK"]]
  /\ msgs = { Msg(p, q, VOTE[p]) : p \in Proc, q \in Proc }
  /\ TypeOK
  /\ SelfKnowledge

Crash(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED <<FD, recvd, msgs, decided>>

Step(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ \E fdNew \in SUBSET crashed :
       /\ FD' = [FD EXCEPT ![p] = fdNew]
       /\ (
            /\ \E m \in msgs : m.to = p
               /\ recvd' = [recvd EXCEPT ![p][m.from] = m.val]
               /\ msgs' = msgs \ {m}
          \/ /\ recvd' = recvd
               /\ msgs' = msgs
          )
       /\ crashed' = crashed
       /\ decided' = [decided EXCEPT ![p] =
             IF decided[p] # "UNDECIDED" THEN decided[p]
             ELSE IF \E r \in Proc : recvd'[p][r] = "NO" THEN "ABORT"
             ELSE IF \A r \in Proc : recvd'[p][r] = "YES" THEN "COMMIT"
             ELSE "UNDECIDED"
          ]

Next ==
  \E p \in Proc : Crash(p) \/ Step(p)

Fairness ==
  \A p \in Proc : WF_vars(Step(p))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

THEOREM Spec => []TypeOK
THEOREM Spec => []SelfKnowledge
THEOREM Spec => []NoAbortWhenAllYes
THEOREM Spec => []CommitImpliesAllYes
THEOREM Spec => []AbortImpliesSomeNo
THEOREM Spec => []Agreement

============================================================================