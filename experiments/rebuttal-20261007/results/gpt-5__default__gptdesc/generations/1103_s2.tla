---- MODULE NBAC ----
EXTENDS Naturals

CONSTANTS 
    Proc,
    InputVote

ASSUME Proc /= {} 
ASSUME InputVote \in [Proc -> {"YES","NO"}]

(*
  Basic value sets
*)
Vals == {"YES","NO"}
Unknown == "UNKNOWN"
DecVals == {"UNDEC","COMMIT","ABORT"}
Bool == {TRUE, FALSE}

(*
  Message records carry a vote from a sender to a receiver
*)
Msg == [from: Proc, to: Proc, val: Vals]

VARIABLES
    crashed,   \* subset of Proc that have crashed
    fd,        \* local failure detector view: fd[p] is the set p suspects
    recvd,     \* recvd[p][q] is p's current knowledge of q's vote in Vals \cup {Unknown}
    sent,      \* sent[p][q] = TRUE iff p has already sent its vote to q
    msgs,      \* the multiset of in-flight messages, modeled as a set for simplicity
    decided    \* decided[p] in DecVals

vars == << crashed, fd, recvd, sent, msgs, decided >>

TypeOK ==
    /\ crashed \subseteq Proc
    /\ fd \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc: fd[p] \subseteq crashed
    /\ recvd \in [Proc -> [Proc -> (Vals \cup {Unknown})]]
    /\ sent \in [Proc -> [Proc -> Bool]]
    /\ msgs \subseteq Msg
    /\ decided \in [Proc -> DecVals]

SelfKnown ==
    \A p \in Proc: recvd[p][p] = InputVote[p]

CommitOccurs ==
    \E p \in Proc: decided[p] = "COMMIT"

AllYesConst ==
    \A q \in Proc: InputVote[q] = "YES"

CommitValidity ==
    CommitOccurs => AllYesConst

Init ==
    /\ crashed = {}
    /\ fd = [p \in Proc |-> {}]
    /\ recvd = [p \in Proc |-> [q \in Proc |-> IF q = p THEN InputVote[p] ELSE Unknown]]
    /\ sent = [p \in Proc |-> [q \in Proc |-> FALSE]]
    /\ msgs = {}
    /\ decided = [p \in Proc |-> "UNDEC"]

Inbox(p) == { m \in msgs : m.to = p }
UnsentPeers(p) == { q \in Proc : q # p /\ ~sent[p][q] }

ProcStep(p) ==
    /\ p \in Proc
    /\ p \notin crashed
    /\ \E fdnew \in SUBSET crashed:
         fd' = [fd EXCEPT ![p] = fdnew]
    /\ \E msgsR \in SUBSET Msg, recvdR \in [Proc -> [Proc -> (Vals \cup {Unknown})]]:
         LET inbox == Inbox(p) IN
           /\ IF inbox # {} THEN
                 \E m \in inbox:
                   /\ msgsR = msgs \ {m}
                   /\ recvdR = [recvd EXCEPT ![p][m.from] = m.val]
              ELSE
                 /\ msgsR = msgs
                 /\ recvdR = recvd
    /\ \E sentNew \in [Proc -> [Proc -> Bool]], msgsS \in SUBSET Msg:
         LET unsent == UnsentPeers(p) IN
           /\ IF unsent # {} THEN
                 \E q \in unsent:
                   /\ sentNew = [sent EXCEPT ![p][q] = TRUE]
                   /\ msgsS = msgsR \cup { [from |-> p, to |-> q, val |-> InputVote[p]] }
              ELSE
                 /\ sentNew = sent
                 /\ msgsS = msgsR
    /\ sent' = sentNew
    /\ msgs' = msgsS
    /\ recvd' = recvdR
    /\ decided' =
         LET tab == recvdR IN
           IF decided[p] # "UNDEC" THEN
             decided
           ELSE IF \E q \in Proc: tab[p][q] = "NO" THEN
             [decided EXCEPT ![p] = "ABORT"]
           ELSE IF \A q \in Proc: tab[p][q] = "YES" THEN
             [decided EXCEPT ![p] = "COMMIT"]
           ELSE IF \A q \in Proc: (tab[p][q] # Unknown) \/ (q \in fd'[p]) THEN
             [decided EXCEPT ![p] = "ABORT"]
           ELSE
             decided
    /\ UNCHANGED crashed

Crash(p) ==
    /\ p \in Proc
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED << fd, recvd, sent, msgs, decided >>

Next ==
    \E p \in Proc: ProcStep(p) \/ Crash(p)

Spec ==
    Init /\ [][Next]_vars /\ \A p \in Proc: WF_vars(ProcStep(p))

Safety ==
    [](TypeOK /\ SelfKnown /\ CommitValidity)

Liveness ==
    AllYesConst => <>CommitOccurs

====