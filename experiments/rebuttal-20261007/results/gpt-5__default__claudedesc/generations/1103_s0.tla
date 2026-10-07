----------------------------- MODULE NBAC -----------------------------

EXTENDS Naturals

CONSTANT N

VARIABLES pc, sent, rcvd, fd, voteInit

Proc == 1..N

States == {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}

Messages == [from: Proc, vote: {"YES", "NO"}]

YesMsg(p) == [from |-> p, vote |-> "YES"]
NoMsg(p)  == [from |-> p, vote |-> "NO"]

AllYesInit == \A p \in Proc: voteInit[p] = "YES"

AllYesRcvd(p) == \A q \in Proc: YesMsg(q) \in rcvd[p]

TypeOK ==
  /\ pc \in [Proc -> States]
  /\ voteInit \in [Proc -> {"YES", "NO"}]
  /\ sent \subseteq Messages
  /\ rcvd \in [Proc -> SUBSET Messages]
  /\ \A p \in Proc: rcvd[p] \subseteq sent
  /\ fd \in [Proc -> BOOLEAN]

InitAny ==
  /\ voteInit \in [Proc -> {"YES", "NO"}]
  /\ pc = voteInit
  /\ sent = {}
  /\ rcvd = [p \in Proc |-> {}]
  /\ fd = [p \in Proc |-> FALSE]

InitAllYes ==
  /\ voteInit = [p \in Proc |-> "YES"]
  /\ pc = voteInit
  /\ sent = {}
  /\ rcvd = [p \in Proc |-> {}]
  /\ fd = [p \in Proc |-> FALSE]

Init == InitAny

vars == << pc, sent, rcvd, fd, voteInit >>

EnvUpdate(p) ==
  \E r \in SUBSET sent', f \in BOOLEAN:
    /\ rcvd' = [rcvd EXCEPT ![p] = r]
    /\ rcvd[p] \subseteq r
    /\ fd' = [fd EXCEPT ![p] = f]
    /\ (f => \E q \in Proc: pc'[q] = "CRASH")

SendStep(p) ==
  /\ p \in Proc
  /\ pc[p] \in {"YES", "NO"}
  /\ LET msg == [from |-> p, vote |-> voteInit[p]] IN sent' = sent \cup {msg}
  /\ pc' = [pc EXCEPT ![p] = "SENT"]
  /\ EnvUpdate(p)
  /\ UNCHANGED << voteInit >>

DecideStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "SENT"
  /\ sent' = sent
  /\ EnvUpdate(p)
  /\ IF (~fd'[p] /\ AllYesRcvd(p))
        THEN pc' = [pc EXCEPT ![p] = "COMMIT"]
        ELSE pc' = [pc EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED << voteInit >>

CrashStep(p) ==
  /\ p \in Proc
  /\ pc[p] \in {"YES", "NO", "SENT"}
  /\ sent' = sent
  /\ EnvUpdate(p)
  /\ pc' = [pc EXCEPT ![p] = "CRASH"]
  /\ UNCHANGED << voteInit >>

IdleStep(p) ==
  /\ p \in Proc
  /\ sent' = sent
  /\ pc' = pc
  /\ EnvUpdate(p)
  /\ UNCHANGED << voteInit >>

Next ==
  \E p \in Proc:
    SendStep(p)
    \/ DecideStep(p)
    \/ CrashStep(p)
    \/ IdleStep(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc: WF_vars(SendStep(p))
  /\ \A p \in Proc: WF_vars(DecideStep(p))

Validity ==
  []( (\E p \in Proc: pc[p] = "COMMIT") => AllYesInit )

=============================================================================